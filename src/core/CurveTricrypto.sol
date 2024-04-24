// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "../IERC20.sol";
import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";
import {UnsafeMath} from "../utils/UnsafeMath.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {Panic} from "../utils/Panic.sol";
import {AddressDerivation} from "../utils/AddressDerivation.sol";

import {SettlerAbstract} from "../SettlerAbstract.sol";
import {ConfusedDeputy} from "./SettlerErrors.sol";

interface ICurveTricrypto {
    function exchange_extended(
        uint256 sellIndex,
        uint256 buyIndex,
        uint256 sellAmount,
        uint256 minBuyAmount,
        bool useEth,
        address payer,
        address receiver,
        bytes32 callbackSelector
    ) external returns (uint256 buyAmount);
}

interface ICurveTricryptoCallback {
    // The function name/selector is arbitrary, but the arguments are controlled by the pool
    function curveTricryptoSwapCallback(
        address payer,
        address receiver,
        IERC20 sellToken,
        uint256 sellAmount,
        uint256 buyAmount
    ) external;
}

abstract contract CurveTricrypto is SettlerAbstract {
    using UnsafeMath for uint256;
    using SafeTransferLib for IERC20;
    using AddressDerivation for address;

    address private constant curveFactory = 0x0c0e5f2fF0ff18a3be9b835635039256dC4B4963;
    // uint256 private constant codePrefixLen = 0x539d;
    // bytes32 private constant codePrefixHash = 0xec96085e693058e09a27755c07882ced27117a3161b1fdaf131a14c7db9978b7;
    uint256 private constant PATH_SIZE = 0x0a;
    uint256 private constant PATH_SKIP_HOP_SIZE = 0x0a;

    // solc is a piece of shit and even though this function is private, it conflicts with the function of the same name in UniswapV3.sol
    function _isPathMultiHopCurve(bytes memory encodedPath) private pure returns (bool) {
        return encodedPath.length > PATH_SIZE;
    }

    function _shiftHopFromPathInPlaceCurve(bytes memory encodedPath) private pure returns (bytes memory) {
        if (encodedPath.length < PATH_SKIP_HOP_SIZE) {
            Panic.panic(Panic.ARRAY_OUT_OF_BOUNDS);
        }
        assembly ("memory-safe") {
            let length := sub(mload(encodedPath), PATH_SKIP_HOP_SIZE)
            encodedPath := add(PATH_SKIP_HOP_SIZE, encodedPath)
            mstore(encodedPath, length)
        }
        return encodedPath;
    }

    function sellToCurveTricrypto(
        address recipient,
        IERC20 sellToken,
        bytes memory encodedPath,
        uint256 bips,
        uint256 minBuyAmount
    ) internal {
        ISignatureTransfer.PermitTransferFrom memory permit;
        permit.permitted.amount = (sellToken.balanceOf(address(this)) * bips).unsafeDiv(10_000);
        sellToCurveTricryptoMetaTxn(recipient, encodedPath, minBuyAmount, address(this), permit, new bytes(0));
    }

    function sellToCurveTricryptoVIP(
        address recipient,
        bytes memory encodedPath,
        uint256 minBuyAmount,
        ISignatureTransfer.PermitTransferFrom memory permit,
        bytes memory sig
    ) internal {
        sellToCurveTricryptoMetaTxn(recipient, encodedPath, minBuyAmount, _msgSender(), permit, sig);
    }

    function sellToCurveTricryptoMetaTxn(
        address recipient,
        bytes memory encodedPath,
        uint256 minBuyAmount,
        address payer,
        ISignatureTransfer.PermitTransferFrom memory permit,
        bytes memory sig
    ) internal {
        uint256 sellAmount = permit.permitted.amount;
        while (encodedPath.length >= PATH_SIZE) {
            uint64 factoryNonce;
            uint8 sellIndex;
            uint8 buyIndex;
            assembly ("memory-safe") {
                buyIndex := mload(add(0x0a, encodedPath))
                sellIndex := shr(0x08, buyIndex)
                factoryNonce := shr(0x10, buyIndex)
            }
            address pool = curveFactory.deriveContract(factoryNonce);
            /*
            bytes32 codePrefixHashActual;
            assembly ("memory-safe") {
                let ptr := mload(0x40)
                extcodecopy(pool, ptr, 0x00, codePrefixLen)
                codePrefixHashActual := keccak256(ptr, codePrefixLen)
            }
            if (codePrefixHashActual != codePrefixHash) {
                revert ConfusedDeputy();
            }
            */
            bool isForwarded = _isForwarded();
            if (payer != address(this)) {
                assembly ("memory-safe") {
                    tstore(0x00, isForwarded)
                    tstore(0x01, mload(add(0x20, permit))) // nonce
                    tstore(0x02, mload(add(0x40, permit))) // deadline
                    for {
                        let src := sig
                        let end := add(0x20, add(mload(sig), sig))
                        // TODO: dedupe copying length
                        let dst := 0x03
                    } lt(src, end) {
                        src := add(0x20, src)
                        dst := add(0x01, dst)
                    } { tstore(dst, mload(src)) }
                }
            }
            if (_isPathMultiHopCurve(encodedPath)) {
                sellAmount = abi.decode(
                    _setOperatorAndCall(
                        pool,
                        abi.encodeCall(
                            ICurveTricrypto.exchange_extended,
                            (
                                sellIndex,
                                buyIndex,
                                permit.permitted.amount,
                                0,
                                false,
                                payer,
                                address(this),
                                bytes32(ICurveTricryptoCallback.curveTricryptoSwapCallback.selector)
                            )
                        ),
                        _curveTricryptoSwapCallback
                    ),
                    (uint256)
                );
            } else {
                sellAmount = abi.decode(
                    _setOperatorAndCall(
                        pool,
                        abi.encodeCall(
                            ICurveTricrypto.exchange_extended,
                            (
                                sellIndex,
                                buyIndex,
                                permit.permitted.amount,
                                minBuyAmount,
                                false,
                                payer,
                                recipient,
                                bytes32(ICurveTricryptoCallback.curveTricryptoSwapCallback.selector)
                            )
                        ),
                        _curveTricryptoSwapCallback
                    ),
                    (uint256)
                );
            }
            payer = address(this);
            encodedPath = _shiftHopFromPathInPlaceCurve(encodedPath);
        }
    }

    function _curveTricryptoSwapCallback(bytes calldata data) private returns (bytes memory) {
        require(data.length == 0xa4 && bytes4(data) == ICurveTricryptoCallback.curveTricryptoSwapCallback.selector);
        address payer;
        IERC20 sellToken;
        uint256 sellAmount;
        assembly ("memory-safe") {
            payer := calldataload(add(0x04, data.offset))
            let err := shr(0xa0, payer)
            sellToken := calldataload(add(0x44, data.offset))
            err := or(shr(0xa0, sellToken), err)
            sellAmount := calldataload(add(0x64, data.offset))
            if err { revert(0x00, 0x00) }
        }
        curveTricryptoSwapCallback(payer, address(0), sellToken, sellAmount, 0);
        return new bytes(0);
    }

    function curveTricryptoSwapCallback(address payer, address, IERC20 sellToken, uint256 sellAmount, uint256)
        private
    {
        if (payer == address(this)) {
            sellToken.safeTransfer(msg.sender, sellAmount);
        } else {
            bool isForwarded;
            uint256 nonce;
            uint256 deadline;
            bytes memory sig;
            assembly ("memory-safe") {
                isForwarded := tload(0x00)
                tstore(0x00, 0x00)
                nonce := tload(0x01)
                tstore(0x01, 0x00)
                deadline := tload(0x02)
                tstore(0x02, 0x00)
                sig := mload(0x40)
                for {
                    let src := 0x03
                    let dst := sig
                    // TODO: dedupe copying length
                    let end := add(0x20, add(dst, tload(src)))
                } lt(dst, end) {
                    src := add(0x01, src)
                    dst := add(0x20, dst)
                } {
                    mstore(dst, tload(src))
                    tstore(src, 0x00)
                }
                mstore(0x40, add(0x20, add(mload(sig), sig)))
            }
            ISignatureTransfer.PermitTransferFrom memory permit = ISignatureTransfer.PermitTransferFrom({
                permitted: ISignatureTransfer.TokenPermissions({token: address(sellToken), amount: sellAmount}),
                nonce: nonce,
                deadline: deadline
            });
            (ISignatureTransfer.SignatureTransferDetails memory transferDetails,,) =
                _permitToTransferDetails(permit, msg.sender);
            _transferFrom(permit, transferDetails, payer, sig, isForwarded);
        }
    }
}
