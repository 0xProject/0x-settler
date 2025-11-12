// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {UnsafeMath} from "../utils/UnsafeMath.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {Panic} from "../utils/Panic.sol";
import {AddressDerivation} from "../utils/AddressDerivation.sol";

import {SettlerAbstract} from "../SettlerAbstract.sol";
import {revertConfusedDeputy} from "./SettlerErrors.sol";

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

library FastCurveTricrypto {
    function fastEncodeExchangeExtended(
        uint256 sellIndex,
        uint256 buyIndex,
        uint256 sellAmount,
        uint256 minBuyAmount,
        address receiver
    ) internal pure returns (bytes memory data) {
        assembly ("memory-safe") {
            data := mload(0x40)

            // callback is stored at
            // mstore(add(0x104, data), shl(0xe0, 0x6370a85c))
            // which is analogous to the next line
            // except that anything from add(0x108, data) on
            // is dirty, but that is not a problem as only the
            // initial 4 bytes at add(0x104, data) are used
            mstore(add(0xe8, data), 0x6370a85c) // selector for `curveTricryptoSwapCallback(address,address,address,uint256,uint256)`
            mstore(add(0xe4, data), receiver)
            codecopy(add(0xa4, data), codesize(), 0x4c) // useEth and payer (both zeroed); clear dirty bits in `receiver`
            mstore(add(0x84, data), minBuyAmount)
            mstore(add(0x64, data), sellAmount)
            mstore(add(0x44, data), buyIndex)
            mstore(add(0x24, data), sellIndex)
            mstore(add(0x04, data), 0xdd96994f) // selector for `exchange_extended(uint256,uint256,uint256,uint256,bool,address,address,bytes32)`
            mstore(data, 0x104)

            mstore(0x40, add(0x124, data))
        }
    }
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
        uint256 sellAmount = _permitToSellAmount(permit);
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
            revertConfusedDeputy();
        }
        */
        bool isForwarded = _isForwarded();
        assembly ("memory-safe") {
            tstore(0x00, isForwarded)
            tstore(0x01, mload(add(0x20, mload(permit)))) // amount
            tstore(0x02, mload(add(0x20, permit))) // nonce
            tstore(0x03, mload(add(0x40, permit))) // deadline
            for {
                let src := add(0x20, sig)
                let end
                {
                    let len := mload(sig)
                    end := add(len, src)
                    tstore(0x04, len)
                }
                let dst := 0x05
            } lt(src, end) {
                src := add(0x20, src)
                dst := add(0x01, dst)
            } { tstore(dst, mload(src)) }
        }
        _setOperatorAndCall(
            pool,
            FastCurveTricrypto.fastEncodeExchangeExtended(sellIndex, buyIndex, sellAmount, minBuyAmount, recipient),
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
        uint256 permittedAmount;
        uint256 nonce;
        uint256 deadline;
        bytes memory sig;
        assembly ("memory-safe") {
            isForwarded := tload(0x00)
            tstore(0x00, 0x00)
            permittedAmount := tload(0x01)
            tstore(0x01, 0x00)
            nonce := tload(0x02)
            tstore(0x02, 0x00)
            deadline := tload(0x03)
            tstore(0x03, 0x00)
            sig := mload(0x40)
            for {
                let dst := add(0x20, sig)
                let end
                {
                    let len := tload(0x04)
                    tstore(0x04, 0x00)
                    end := add(dst, len)
                    mstore(sig, len)
                    mstore(0x40, end)
                }
                let src := 0x05
            } lt(dst, end) {
                src := add(0x01, src)
                dst := add(0x20, dst)
            } {
                mstore(dst, tload(src))
                tstore(src, 0x00)
            }
        }
        ISignatureTransfer.PermitTransferFrom memory permit = ISignatureTransfer.PermitTransferFrom({
            permitted: ISignatureTransfer.TokenPermissions({token: address(sellToken), amount: permittedAmount}),
            nonce: nonce,
            deadline: deadline
        });
        ISignatureTransfer.SignatureTransferDetails memory transferDetails =
            ISignatureTransfer.SignatureTransferDetails({to: msg.sender, requestedAmount: sellAmount});
        _transferFrom(permit, transferDetails, sig, isForwarded);
    }
}
