// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IUniswapV3Pool, UniswapV3Fork} from "src/core/UniswapV3Fork.sol";
import {Permit2Payment, Permit2PaymentBase} from "src/core/Permit2Payment.sol";
import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";
import {AddressDerivation} from "src/utils/AddressDerivation.sol";
import {Context, AbstractContext} from "src/Context.sol";
import {AllowanceHolderContext} from "src/allowanceholder/AllowanceHolderContext.sol";
import {uniswapV3InitHash, IUniswapV3Callback} from "src/core/univ3forks/UniswapV3.sol";
import {UnknownForkId} from "src/core/SettlerErrors.sol";

import {IAllowanceHolder} from "src/allowanceholder/IAllowanceHolder.sol";

import {Utils} from "../Utils.sol";
import {IERC20} from "src/IERC20.sol";

import {Test} from "forge-std/Test.sol";

contract UniswapV3Dummy is AllowanceHolderContext, Permit2Payment, UniswapV3Fork {
    address internal immutable uniFactory;

    constructor(address _uniFactory) UniswapV3Fork() Permit2Payment() {
        uniFactory = _uniFactory;
    }

    function sellSelf(address recipient, uint256 bps, bytes memory encodedPath, uint256 minBuyAmount)
        external
        takerSubmitted
        returns (uint256)
    {
        return super.sellToUniswapV3(recipient, bps, encodedPath, minBuyAmount);
    }

    function sell(
        address recipient,
        bytes memory encodedPath,
        ISignatureTransfer.PermitTransferFrom memory permit,
        bytes memory sig,
        uint256 minBuyAmount
    ) external takerSubmitted returns (uint256) {
        return super.sellToUniswapV3VIP(recipient, encodedPath, permit, sig, minBuyAmount);
    }

    fallback(bytes calldata data) external returns (bytes memory) {
        return _invokeCallback(data);
    }

    function _hasMetaTxn() internal pure override returns (bool) {
        return false;
    }

    function _allowanceHolderTransferFrom(address token, address owner, address recipient, uint256 amount)
        internal
        override
    {
        _ALLOWANCE_HOLDER.transferFrom(token, owner, recipient, amount);
    }

    function _operator() internal view override returns (address) {
        return AllowanceHolderContext._msgSender();
    }

    function _msgSender()
        internal
        view
        override(Permit2PaymentBase, AllowanceHolderContext, AbstractContext)
        returns (address)
    {
        return Permit2PaymentBase._msgSender();
    }

    function _dispatch(uint256, bytes4, bytes calldata) internal pure override returns (bool) {
        revert("unimplemented");
    }

    function _uniV3ForkInfo(uint8 forkId)
        internal
        view
        override
        returns (address factory, bytes32 initHash, bytes4 callbackSelector)
    {
        if (forkId == 0) {
            factory = uniFactory;
            initHash = uniswapV3InitHash;
            callbackSelector = IUniswapV3Callback.uniswapV3SwapCallback.selector;
        } else {
            revert UnknownForkId(forkId);
        }
    }
}

/// @dev We need a dummy to actually call our contract, so it needs an implementation which at the very least
/// calls the `uniswapV3SwapCallback`
contract UniswapV3PoolDummy {
    bytes public RETURN_DATA;

    constructor(bytes memory returnData) {
        RETURN_DATA = returnData;
    }

    fallback(bytes calldata) external payable returns (bytes memory) {
        (,,,, bytes memory data) = abi.decode(msg.data[4:], (address, bool, int256, uint160, bytes));
        msg.sender.call(
            abi.encodeWithSignature("uniswapV3SwapCallback(int256,int256,bytes)", int256(1), int256(1), data)
        );
        return RETURN_DATA;
    }
}

contract UniswapV3UnitTest is Utils, Test {
    UniswapV3Dummy uni;
    address UNI_FACTORY = _createNamedRejectionDummy("UNI_FACTORY");
    address PERMIT2 = _etchNamedRejectionDummy("PERMIT2", 0x000000000022D473030F116dDEE9F6B43aC78BA3);
    address ALLOWANCE_HOLDER = _etchNamedRejectionDummy("ALLOWANCE_HOLDER", 0x0000000000001fF3684f28c67538d4D072C22734);

    address TOKEN0 = _createNamedRejectionDummy("TOKEN0");
    address TOKEN1 = _createNamedRejectionDummy("TOKEN1");
    address TOKEN2 = _createNamedRejectionDummy("TOKEN2");
    address RECIPIENT = _createNamedRejectionDummy("RECIPIENT");

    address POOL;

    constructor() {
        address token0 = TOKEN0;
        address token1 = TOKEN1;
        (token0, token1) = token0 < token1 ? (token0, token1) : (token1, token0);
        uint24 fee = 500;
        POOL = _etchNamedRejectionDummy(
            "POOL",
            AddressDerivation.deriveDeterministicContract(
                UNI_FACTORY,
                keccak256(abi.encode(token0, token1, fee)),
                0xe34f199b19b2b4f47f68442619d555527d244f78a3297ea89325f843f87b8b54
            )
        );
    }

    function setUp() public {
        uni = new UniswapV3Dummy(UNI_FACTORY);
    }

    function testUniswapV3SellSelfFunded() public {
        uint256 bps = 10_000;
        uint256 amount = 99999;
        uint256 minBuyAmount = amount;

        bytes memory data = abi.encodePacked(TOKEN0, uint8(0), uint24(500), TOKEN1);

        _mockExpectCall(TOKEN0, abi.encodeWithSelector(IERC20.balanceOf.selector, address(uni)), abi.encode(amount));
        bool zeroForOne = TOKEN0 < TOKEN1;

        deployCodeTo(
            "UniswapV3UnitTest.t.sol:UniswapV3PoolDummy",
            abi.encode(abi.encode(zeroForOne ? int256(0) : -int256(amount), zeroForOne ? -int256(amount) : int256(0))),
            POOL
        );
        vm.expectCall(
            POOL,
            abi.encodeWithSelector(
                IUniswapV3Pool.swap.selector,
                RECIPIENT,
                zeroForOne,
                amount,
                zeroForOne ? 4295128740 : 1461446703485210103287273052203988822378723970341,
                abi.encodePacked(TOKEN0, uint24(500), TOKEN1, address(uni))
            )
        );
        _mockExpectCall(TOKEN0, abi.encodeCall(IERC20.transfer, (POOL, 1)), abi.encode(true));

        uni.sellSelf(RECIPIENT, bps, data, minBuyAmount);
    }

    function testUniswapV3SellSlippage() public {
        uint256 bps = 10_000;
        uint256 amount = 99999;
        uint256 minBuyAmount = amount + 1;

        bytes memory data = abi.encodePacked(TOKEN0, uint8(0), uint24(500), TOKEN1);

        _mockExpectCall(TOKEN0, abi.encodeWithSelector(IERC20.balanceOf.selector, address(uni)), abi.encode(amount));
        bool zeroForOne = TOKEN0 < TOKEN1;

        deployCodeTo(
            "UniswapV3UnitTest.t.sol:UniswapV3PoolDummy",
            abi.encode(abi.encode(zeroForOne ? int256(0) : -int256(amount), zeroForOne ? -int256(amount) : int256(0))),
            POOL
        );
        vm.expectCall(
            POOL,
            abi.encodeWithSelector(
                IUniswapV3Pool.swap.selector,
                RECIPIENT,
                zeroForOne,
                amount,
                zeroForOne ? 4295128740 : 1461446703485210103287273052203988822378723970341,
                abi.encodePacked(TOKEN0, uint24(500), TOKEN1, address(uni))
            )
        );
        _mockExpectCall(TOKEN0, abi.encodeCall(IERC20.transfer, (POOL, 1)), abi.encode(true));

        vm.expectRevert(
            abi.encodeWithSignature("TooMuchSlippage(address,uint256,uint256)", TOKEN1, minBuyAmount, amount)
        );
        uni.sellSelf(RECIPIENT, bps, data, minBuyAmount);
    }

    function testUniswapV3SellPermit2() public {
        uint256 amount = 99999;
        uint256 minBuyAmount = amount;

        bytes memory data = abi.encodePacked(TOKEN0, uint8(0), uint24(500), TOKEN1);
        // Override the UniswapV3 pool code to callback our contract
        // There's probably a smarter way to do this tbh
        deployCodeTo(
            "UniswapV3UnitTest.t.sol:UniswapV3PoolDummy",
            abi.encode(abi.encodePacked(-int256(amount), -int256(amount))),
            POOL
        );

        ISignatureTransfer.TokenPermissions memory permitted =
            ISignatureTransfer.TokenPermissions({token: TOKEN0, amount: amount});
        ISignatureTransfer.PermitTransferFrom memory permitTransfer =
            ISignatureTransfer.PermitTransferFrom({permitted: permitted, nonce: 0, deadline: 0});
        ISignatureTransfer.SignatureTransferDetails memory transferDetails =
            ISignatureTransfer.SignatureTransferDetails({to: POOL, requestedAmount: amount});

        // permitTransferFrom(((address,uint256),uint256,uint256),(address,uint256),address,bytes) 30f28b7a
        // cannot use abi.encodeWithSelector due to the selector overload and ambiguity
        _mockExpectCall(
            PERMIT2,
            abi.encodeWithSelector(bytes4(0x30f28b7a), permitTransfer, transferDetails, address(this), hex"deadbeef"),
            new bytes(0)
        );

        uni.sell(RECIPIENT, data, permitTransfer, hex"deadbeef", minBuyAmount);
    }

    function testUniswapV3SellAllowanceHolder() public {
        uint256 amount = 99999;
        uint256 minBuyAmount = amount;

        bytes memory data = abi.encodePacked(TOKEN0, uint8(0), uint24(500), TOKEN1);
        // Override the UniswapV3 pool code to callback our contract
        // There's probably a smarter way to do this tbh
        deployCodeTo(
            "UniswapV3UnitTest.t.sol:UniswapV3PoolDummy",
            abi.encode(abi.encodePacked(-int256(amount), -int256(amount))),
            POOL
        );

        ISignatureTransfer.PermitTransferFrom memory permitTransfer = ISignatureTransfer.PermitTransferFrom({
            permitted: ISignatureTransfer.TokenPermissions({token: TOKEN0, amount: amount}),
            nonce: 0,
            deadline: block.timestamp
        });

        _mockExpectCall(
            ALLOWANCE_HOLDER,
            abi.encodeCall(IAllowanceHolder.transferFrom, (TOKEN0, address(this), POOL, amount)),
            abi.encode(true)
        );

        vm.prank(ALLOWANCE_HOLDER);
        address(uni).call(
            abi.encodePacked(
                abi.encodeCall(uni.sell, (RECIPIENT, data, permitTransfer, hex"", minBuyAmount)), address(this)
            ) // Forward on true msg.sender
        );
        // uni.sell(RECIPIENT, data, minBuyAmount, permitTransfer, hex"");
    }
}
