// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISettlerBase} from "./interfaces/ISettlerBase.sol";
import {ISettlerTakerSubmitted} from "./interfaces/ISettlerTakerSubmitted.sol";

import {MultiCallContext} from "./multicall/MultiCallContext.sol";
import {Context} from "./Context.sol";
import {TwoStepOwnable} from "./deployer/TwoStepOwnable.sol";
import {SettlerSwapper} from "./SettlerSwapper.sol";

import {SafeTransferLib} from "./vendor/SafeTransferLib.sol";
import {FastLogic} from "./utils/FastLogic.sol";
import {UnsafeMath} from "./utils/UnsafeMath.sol";
import {Panic} from "./utils/Panic.sol";
import {AddressDerivation} from "./utils/AddressDerivation.sol";

type Address is uint256;

/**
 * @notice Returns the address representation of a uint256.
 * @param a The uint256 value to convert to an address.
 * @return The address representation of the provided uint256 value.
 */
function get(Address a) pure returns (address) {
    return address(uint160(0x00ffffffffffffffffffffffffffffffffffffffff & Address.unwrap(a)));
}

using {get} for Address global;

type MakerTraits is uint256;

/**
 * @notice Checks if the maker needs to unwraps WETH.
 * @param makerTraits The traits of the maker.
 * @return result A boolean indicating whether the maker needs to unwrap WETH.
 */
function unwrapWeth(MakerTraits makerTraits) pure returns (bool) {
    return (MakerTraits.unwrap(makerTraits) >> 247) & 1 != 0;
}

using {unwrapWeth} for MakerTraits global;

struct Order {
    uint256 salt;
    Address maker;
    Address receiver;
    Address makerAsset;
    Address takerAsset;
    uint256 makingAmount;
    uint256 takingAmount;
    MakerTraits makerTraits;
}

interface IPostInteraction {
    /**
     * @notice Callback method that gets called after all fund transfers
     * @param order Order being processed
     * @param extension Order extension data
     * @param orderHash Hash of the order being processed
     * @param taker Taker address
     * @param makingAmount Actual making amount
     * @param takingAmount Actual taking amount
     * @param remainingMakingAmount Order remaining making amount
     * @param extraData Extra data
     */
    function postInteraction(
        Order calldata order,
        bytes calldata extension,
        bytes32 orderHash,
        address taker,
        uint256 makingAmount,
        uint256 takingAmount,
        uint256 remainingMakingAmount,
        bytes calldata extraData
    ) external;
}

address constant LIMIT_ORDER_PROTOCOL = 0x111111125421cA6dc452d289314280a0f8842A65;

interface ISafeSetup {
    function setup(
        address[] calldata owners,
        uint256 threshold,
        address to,
        bytes calldata data,
        address fallbackHandler,
        address paymentToken,
        uint256 payment,
        address payable paymentReceiver
    ) external;
}

type TokenArrayIterator is uint256;

function _tokenIterator_eq(TokenArrayIterator a, TokenArrayIterator b) pure returns (bool) {
    return TokenArrayIterator.unwrap(a) == TokenArrayIterator.unwrap(b);
}

function _tokenIterator_ne(TokenArrayIterator a, TokenArrayIterator b) pure returns (bool) {
    return TokenArrayIterator.unwrap(a) != TokenArrayIterator.unwrap(b);
}

using {_tokenIterator_eq as ==, _tokenIterator_ne as !=} for TokenArrayIterator global;

library LibTokenArrayIterator {
    function iter(IERC20[] calldata a) internal pure returns (TokenArrayIterator r) {
        assembly ("memory-safe") {
            r := a.offset
        }
    }

    function end(IERC20[] calldata a) internal pure returns (TokenArrayIterator r) {
        unchecked {
            return TokenArrayIterator.wrap((a.length << 5) + TokenArrayIterator.unwrap(iter(a)));
        }
    }

    function next(TokenArrayIterator i) internal pure returns (TokenArrayIterator) {
        unchecked {
            return TokenArrayIterator.wrap(32 + TokenArrayIterator.unwrap(i));
        }
    }

    function get(IERC20[] calldata, TokenArrayIterator i) internal pure returns (IERC20 r) {
        assembly ("memory-safe") {
            r := calldataload(i)
            if shr(0xa0, r) { revert(0x00, 0x00) }
        }
    }
}

using LibTokenArrayIterator for TokenArrayIterator global;

struct Swap {
    IERC20 sellToken;
    uint256 minAmountOut;
    /// While Settler takes `actions` as `bytes[]`, we take it as just `bytes`; that is `abi.encode(originalActions)[32:]`.
    bytes actions;
    bytes32 zid;
}

function getActions(Swap calldata swap) pure returns (bytes calldata r) {
    assembly ("memory-safe") {
        r.offset := add(swap, calldataload(add(0x40, swap)))
        r.length := calldataload(r.offset)
        r.offset := add(0x20, r.offset)
    }
}

using {getActions} for Swap;

type SwapArrayIterator is uint256;

function _swapIterator_eq(SwapArrayIterator a, SwapArrayIterator b) pure returns (bool) {
    return SwapArrayIterator.unwrap(a) == SwapArrayIterator.unwrap(b);
}

function _swapIterator_ne(SwapArrayIterator a, SwapArrayIterator b) pure returns (bool) {
    return SwapArrayIterator.unwrap(a) != SwapArrayIterator.unwrap(b);
}

using {_swapIterator_eq as ==, _swapIterator_ne as !=} for SwapArrayIterator global;

library LibSwapArrayIterator {
    function iter(Swap[] calldata swaps) internal pure returns (SwapArrayIterator r) {
        assembly ("memory-safe") {
            r := swaps.offset
        }
    }

    function end(Swap[] calldata swaps) internal pure returns (SwapArrayIterator r) {
        unchecked {
            return SwapArrayIterator.wrap((swaps.length << 5) + SwapArrayIterator.unwrap(iter(swaps)));
        }
    }

    function next(SwapArrayIterator i) internal pure returns (SwapArrayIterator) {
        unchecked {
            return SwapArrayIterator.wrap(32 + SwapArrayIterator.unwrap(i));
        }
    }

    function get(Swap[] calldata swaps, SwapArrayIterator i) internal pure returns (Swap calldata r) {
        assembly ("memory-safe") {
            r := add(swaps.offset, calldataload(i))
        }
    }
}

using LibSwapArrayIterator for SwapArrayIterator global;

contract LimitOrderFeeCollector is IPostInteraction, MultiCallContext, TwoStepOwnable, SettlerSwapper {
    using SafeTransferLib for IERC20;
    using SafeTransferLib for address payable;
    using LibTokenArrayIterator for IERC20[];
    using LibSwapArrayIterator for Swap[];
    using UnsafeMath for uint256;
    using FastLogic for bool;

    address public feeCollector;
    IERC20 public immutable wnative;

    bytes32 private constant _ALLOWANCE_HOLDER_CODEHASH =
        0x99f5e8edaceacfdd183eb5f1da8a7757b322495b80cf7928db289a1b1a09f799;
    uint256 internal constant _BASIS = 10_000;

    bytes32 private constant _SINGLETON_INITHASH = 0x49f30800a6ac5996a48b80c47ff20f19f8728812498a2a7fe75a14864fab6438;
    bytes32 private constant _FACTORY_INITHASH = 0x13d77c68fe7529013a9a57a295a785084b80e3d6ae9358c7f334752e0c8615f4;
    bytes32 private constant _FALLBACK_INITHASH = 0x272190de126b4577e187d9f00b9ca5daeae76d771965d734876891a51f9c43d8;
    bytes private constant _SAFE_CONSTRUCTOR =
        hex"608060405234801561001057600080fd5b506040516101e63803806101e68339818101604052602081101561003357600080fd5b8101908080519060200190929190505050600073ffffffffffffffffffffffffffffffffffffffff168173ffffffffffffffffffffffffffffffffffffffff1614156100ca576040517f08c379a00000000000000000000000000000000000000000000000000000000081526004018080602001828103825260228152602001806101c46022913960400191505060405180910390fd5b806000806101000a81548173ffffffffffffffffffffffffffffffffffffffff021916908373ffffffffffffffffffffffffffffffffffffffff1602179055505060ab806101196000396000f3fe608060405273ffffffffffffffffffffffffffffffffffffffff600054167fa619486e0000000000000000000000000000000000000000000000000000000060003514156050578060005260206000f35b3660008037600080366000845af43d6000803e60008114156070573d6000fd5b3d6000f3fea2646970667358221220d1429297349653a4918076d650332de1a1068c5f3e07c5c82360c277770b955264736f6c63430007060033496e76616c69642073696e676c65746f6e20616464726573732070726f7669646564";

    address private constant _TOEHOLD0 = 0x4e59b44847b379578588920cA78FbF26c0B4956C;
    address private constant _TOEHOLD1 = 0x914d7Fec6aaC8cd542e72Bca78B30650d45643d7;
    bytes32 private constant _TOEHOLD_CODEHASH = 0x2fa86add0aed31f33a762c9d88e807c475bd51d0f52bd0955754b2608f7e4989;
    address private constant _SAFE_INITIAL_OWNER = 0x6d4197897b4e776C96c04309cF1CA47179C2B543;

    event SetFeeCollector(address indexed newFeeCollector);
    event GitCommit(bytes20 indexed commitHash);

    constructor(bytes20 gitCommit, address initialFeeCollector, IERC20 wnative_) {
        require((msg.sender == _TOEHOLD0).or(msg.sender == _TOEHOLD1));
        require(msg.sender.codehash == _TOEHOLD_CODEHASH);
        require(ALLOWANCE_HOLDER_ADDRESS.codehash == _ALLOWANCE_HOLDER_CODEHASH);
        require(LIMIT_ORDER_PROTOCOL.code.length != 0);
        require(initialFeeCollector != address(0));
        wnative_.balanceOf(address(0)); // check that WETH is ERC20-ish

        address singleton = AddressDerivation.deriveDeterministicContract(msg.sender, bytes32(0), _SINGLETON_INITHASH);
        address factory = AddressDerivation.deriveDeterministicContract(msg.sender, bytes32(0), _FACTORY_INITHASH);
        address fallback_ = AddressDerivation.deriveDeterministicContract(msg.sender, bytes32(0), _FALLBACK_INITHASH);
        bytes32 safeInitHash = keccak256(bytes.concat(_SAFE_CONSTRUCTOR, bytes32(uint256(uint160(singleton)))));
        address[] memory safeInitialOwners = new address[](1);
        safeInitialOwners[0] = _SAFE_INITIAL_OWNER;
        bytes32 safeSalt = keccak256(
            bytes.concat(
                keccak256(
                    abi.encodeCall(
                        ISafeSetup.setup,
                        (safeInitialOwners, 1, address(0), "", fallback_, address(0), 0, payable(address(0)))
                    )
                ),
                bytes32(0)
            )
        );
        address initialOwner = AddressDerivation.deriveDeterministicContract(factory, safeSalt, safeInitHash);
        require(initialOwner.code.length != 0);

        wnative = wnative_;

        emit GitCommit(gitCommit);

        _setPendingOwner(initialOwner);

        feeCollector = initialFeeCollector;
        emit SetFeeCollector(feeCollector);
    }

    modifier onlyLimitOrderProtocol() {
        if (Context._msgSender() != LIMIT_ORDER_PROTOCOL) {
            revert PermissionDenied();
        }
        _;
    }

    function _requireFeeCollector() private view {
        if (_msgSender() != feeCollector) {
            revert PermissionDenied();
        }
    }

    modifier onlyFeeCollector() {
        _requireFeeCollector();
        _;
    }

    function setFeeCollector(address newFeeCollector) external onlyOwner returns (bool) {
        require(newFeeCollector != address(0));
        feeCollector = newFeeCollector;
        emit SetFeeCollector(newFeeCollector);
        return true;
    }

    function collectTokens(IERC20[] calldata tokens, address recipient) external onlyFeeCollector returns (bool) {
        for ((TokenArrayIterator i, TokenArrayIterator end) = (tokens.iter(), tokens.end()); i != end; i = i.next()) {
            IERC20 token = tokens.get(i);
            token.safeTransfer(recipient, token.fastBalanceOf(address(this)));
        }
        return true;
    }

    function collectEth(address payable recipient) external onlyFeeCollector returns (bool) {
        recipient.safeTransferETH(address(this).balance);
        return true;
    }

    function collectBadlyBehavedToken(IERC20 token, address recipient, uint256 amount)
        external
        onlyFeeCollector
        returns (bool)
    {
        token.safeTransfer(recipient, amount);
        return true;
    }

    /// While Settler takes `actions` as `bytes[]`, we take it as just `bytes`; that is `abi.encode(originalActions)[32:]`.
    function swap(
        ISettlerTakerSubmitted settler,
        IERC20 sellToken,
        ISettlerBase.AllowedSlippage calldata slippage,
        bytes calldata actions,
        bytes32 zid
    ) external onlyFeeCollector validSettler(settler) returns (bool) {
        _swapAll(settler, sellToken, slippage.recipient, slippage.buyToken, slippage.minAmountOut, actions, zid);
        return true;
    }

    /// While Settler takes `actions` as `bytes[]`, we take it as just `bytes`; that is `abi.encode(originalActions)[32:]`.
    function multiSwap(
        ISettlerTakerSubmitted settler,
        address payable recipient,
        IERC20 buyToken,
        Swap[] calldata swaps
    ) external onlyFeeCollector validSettler(settler) returns (bool) {
        for ((SwapArrayIterator i, SwapArrayIterator end) = (swaps.iter(), swaps.end()); i != end; i = i.next()) {
            Swap calldata swap_ = swaps.get(i);
            _swapAll(settler, swap_.sellToken, recipient, buyToken, swap_.minAmountOut, swap_.getActions(), swap_.zid);
        }
        return true;
    }

    function resetAllowance(IERC20 token) external onlyFeeCollector returns (bool) {
        token.safeApprove(ALLOWANCE_HOLDER_ADDRESS, 0);
        return true;
    }

    /// @inheritdoc IPostInteraction
    function postInteraction(
        Order calldata order,
        bytes calldata /* extension */,
        bytes32 /* orderHash */,
        address /* taker */,
        uint256 /* makingAmount */,
        uint256 takingAmount,
        uint256 /* remainingMakingAmount */,
        bytes calldata extraData
    ) external override onlyLimitOrderProtocol {
        uint16 feeBps;
        assembly ("memory-safe") {
            feeBps := shr(0xf0, calldataload(extraData.offset))
        }
        if (feeBps >= _BASIS) {
            Panic.panic(Panic.ARITHMETIC_OVERFLOW);
        }
        unchecked {
            takingAmount -= (takingAmount * feeBps) / _BASIS;
        }

        address takerAsset = order.takerAsset.get();
        address receiver = order.maker.get();
        if ((takerAsset == address(wnative)).and(order.makerTraits.unwrapWeth())) {
            payable(receiver).safeTransferETH(takingAmount);
        } else {
            IERC20(takerAsset).safeTransfer(receiver, takingAmount);
        }
    }

    receive() external payable {}
}
