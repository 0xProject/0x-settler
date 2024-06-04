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

    function _curveFactory() internal virtual returns (address);
    // uint256 private constant codePrefixLen = 0x539d;
    // bytes32 private constant codePrefixHash = 0xec96085e693058e09a27755c07882ced27117a3161b1fdaf131a14c7db9978b7;

    function sellToCurveTricryptoVIP(
        address recipient,
        uint80 poolInfo,
        ISignatureTransfer.PermitTransferFrom memory permit,
        bytes memory sig,
        uint256 minBuyAmount
    ) internal {
        uint64 factoryNonce = uint64(poolInfo >> 16);
        uint8 sellIndex = uint8(poolInfo >> 8);
        uint8 buyIndex = uint8(poolInfo);
        address pool = _curveFactory().deriveContract(factoryNonce);
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
        assembly ("memory-safe") {
            sstore(0x00, isForwarded)
            sstore(0x01, mload(add(0x20, permit))) // nonce
            sstore(0x02, mload(add(0x40, permit))) // deadline
            for {
                let src := add(0x20, sig)
                let end
                {
                    let len := mload(sig)
                    end := add(len, src)
                    sstore(0x03, len)
                }
                let dst := 0x04
            } lt(src, end) {
                src := add(0x20, src)
                dst := add(0x01, dst)
            } { sstore(dst, mload(src)) }
        }
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
                    address(0), // payer
                    recipient,
                    bytes32(ICurveTricryptoCallback.curveTricryptoSwapCallback.selector)
                )
            ),
            uint32(ICurveTricryptoCallback.curveTricryptoSwapCallback.selector),
            _curveTricryptoSwapCallback
        );
    }

    function _curveTricryptoSwapCallback(bytes calldata data) private returns (bytes memory) {
        require(data.length == 0xa0);
        address payer;
        IERC20 sellToken;
        uint256 sellAmount;
        assembly ("memory-safe") {
            payer := calldataload(data.offset)
            let err := shr(0xa0, payer)
            sellToken := calldataload(add(0x40, data.offset))
            err := or(shr(0xa0, sellToken), err)
            sellAmount := calldataload(add(0x60, data.offset))
            if err { revert(0x00, 0x00) }
        }
        curveTricryptoSwapCallback(payer, address(0), sellToken, sellAmount, 0);
        return new bytes(0);
    }

    function curveTricryptoSwapCallback(address payer, address, IERC20 sellToken, uint256 sellAmount, uint256)
        private
    {
        assert(payer == address(0));
        bool isForwarded;
        uint256 nonce;
        uint256 deadline;
        bytes memory sig;
        assembly ("memory-safe") {
            isForwarded := sload(0x00)
            sstore(0x00, 0x00)
            nonce := sload(0x01)
            sstore(0x01, 0x00)
            deadline := sload(0x02)
            sstore(0x02, 0x00)
            sig := mload(0x40)
            for {
                let dst := add(0x20, sig)
                let end
                {
                    let len := sload(0x03)
                    end := add(dst, len)
                    mstore(sig, len)
                    mstore(0x40, end)
                }
                let src := 0x04
            } lt(dst, end) {
                src := add(0x01, src)
                dst := add(0x20, dst)
            } {
                mstore(dst, sload(src))
                sstore(src, 0x00)
            }
        }
        ISignatureTransfer.PermitTransferFrom memory permit = ISignatureTransfer.PermitTransferFrom({
            permitted: ISignatureTransfer.TokenPermissions({token: address(sellToken), amount: sellAmount}),
            nonce: nonce,
            deadline: deadline
        });
        (ISignatureTransfer.SignatureTransferDetails memory transferDetails,,) =
            _permitToTransferDetails(permit, msg.sender);
        _transferFrom(permit, transferDetails, sig, isForwarded);
    }
}
