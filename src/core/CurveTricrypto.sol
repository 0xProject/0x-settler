// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "../IERC20.sol";
import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {Panic} from "../utils/Panic.sol";

import {SettlerAbstract} from "../SettlerAbstract.sol";

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

interface ICurveTricryptoFactory {
    function find_pool_for_coins(IERC20, IERC20, uint256) external view returns (ICurveTricrypto);
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
    using SafeTransferLib for IERC20;

    ICurveTricryptoFactory private constant curveFactory =
        ICurveTricryptoFactory(0x0c0e5f2fF0ff18a3be9b835635039256dC4B4963);
    uint256 private constant PATH_SIZE = 0x2b;
    uint256 private constant PATH_SKIP_HOP_SIZE = 0x17;

    function _isPathMultiHop(bytes memory encodedPath) private pure returns (bool) {
        return encodedPath.length > PATH_SIZE;
    }

    function _shiftHopFromPathInPlace(bytes memory encodedPath) private pure returns (bytes memory) {
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
        bytes memory encodedPath,
        uint256 sellAmount,
        uint256 minBuyAmount,
        address payer,
        ISignatureTransfer.PermitTransferFrom memory permit,
        bytes memory sig
    ) internal {
        while (encodedPath.length >= PATH_SIZE) {
            IERC20 sellToken;
            uint8 poolIndex;
            uint8 sellIndex;
            uint8 buyIndex;
            IERC20 buyToken;
            assembly ("memory-safe") {
                sellToken := mload(add(0x14, encodedPath))
                buyIndex := mload(add(0x17, encodedPath))
                sellIndex := shr(0x08, buyIndex)
                poolIndex := shr(0x10, buyIndex)
                buyToken := mload(add(PATH_SIZE, encodedPath))
            }
            ICurveTricrypto pool = curveFactory.find_pool_for_coins(sellToken, buyToken, poolIndex); // order of sell/buy token doesn't matter
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
            if (_isPathMultiHop(encodedPath)) {
                sellAmount = abi.decode(
                    _setOperatorAndCall(
                        address(pool),
                        abi.encodeCall(
                            pool.exchange_extended,
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
                        address(pool),
                        abi.encodeCall(
                            pool.exchange_extended,
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
            encodedPath = _shiftHopFromPathInPlace(encodedPath);
        }
    }

    function _curveTricryptoSwapCallback(bytes calldata data) private returns (bytes memory) {
        require(data.length == 0xa4 && bytes4(data) == ICurveTricryptoCallback.curveTricryptoSwapCallback.selector);
        address payer;
        IERC20 sellToken;
        uint256 sellAmount;
        assembly ("memory-safe") {
            payer := calldataload(add(0x04, data.offset))
            let err := shr(0x60, payer)
            sellToken := calldataload(add(0x44, data.offset))
            err := or(shr(0x60, sellToken), err)
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
                deadline := tload(0x01)
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
