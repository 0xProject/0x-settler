// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20, IERC20Meta} from "./IERC20.sol";
import {IERC721Owner} from "./IERC721Owner.sol";
import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";

import {Permit2PaymentTakerSubmitted} from "./core/Permit2Payment.sol";
import {Permit2PaymentAbstract} from "./core/Permit2PaymentAbstract.sol";

import {AbstractContext} from "./Context.sol";
import {AllowanceHolderContext} from "./allowanceholder/AllowanceHolderContext.sol";
import {CalldataDecoder, SettlerBase} from "./SettlerBase.sol";
import {UnsafeMath} from "./utils/UnsafeMath.sol";

import {ISettlerActions} from "./ISettlerActions.sol";
import {ActionInvalid} from "./core/SettlerErrors.sol";

abstract contract Settler is Permit2PaymentTakerSubmitted, SettlerBase {
    using UnsafeMath for uint256;
    using CalldataDecoder for bytes[];

    constructor() {
        assert(
            block.chainid == 31337
                || IERC721Owner(0x00000000000004533Fe15556B1E086BB1A72cEae).ownerOf(2) == address(this)
        );
    }

    function _hasMetaTxn() internal pure override returns (bool) {
        return false;
    }

    function _msgSender()
        internal
        view
        virtual
        // Solidity inheritance is so stupid
        override(Permit2PaymentTakerSubmitted, AbstractContext)
        returns (address)
    {
        return super._msgSender();
    }

    function _isRestrictedTarget(address target)
        internal
        pure
        virtual
        // Solidity inheritance is so stupid
        override(Permit2PaymentTakerSubmitted, Permit2PaymentAbstract)
        returns (bool)
    {
        return super._isRestrictedTarget(target);
    }

    function _dispatchVIP(bytes4 action, bytes calldata data) internal virtual returns (bool) {
        if (action == ISettlerActions.RFQ_VIP.selector) {
            (
                address recipient,
                ISignatureTransfer.PermitTransferFrom memory makerPermit,
                address maker,
                bytes memory makerSig,
                ISignatureTransfer.PermitTransferFrom memory takerPermit,
                bytes memory takerSig
            ) = abi.decode(
                data,
                (
                    address,
                    ISignatureTransfer.PermitTransferFrom,
                    address,
                    bytes,
                    ISignatureTransfer.PermitTransferFrom,
                    bytes
                )
            );

            fillRfqOrderVIP(recipient, makerPermit, maker, makerSig, takerPermit, takerSig);
        } else if (action == ISettlerActions.UNISWAPV3_VIP.selector) {
            (
                address recipient,
                bytes memory path,
                ISignatureTransfer.PermitTransferFrom memory permit,
                bytes memory sig,
                uint256 amountOutMin
            ) = abi.decode(data, (address, bytes, ISignatureTransfer.PermitTransferFrom, bytes, uint256));

            sellToUniswapV3VIP(recipient, path, permit, sig, amountOutMin);
        } else {
            return false;
        }
        return true;
    }

    function execute(AllowedSlippage calldata slippage, bytes[] calldata actions, bytes32 /* zid & affiliate */ )
        public
        payable
        takerSubmitted
        returns (bool)
    {
        for (uint256 i; i < actions.length; i = i.unsafeInc()) {
            (bytes4 action, bytes calldata data) = actions.decodeCall(i);
            if (!((i == 0 && _dispatchVIP(action, data)) || _dispatch(i, action, data))) {
                revert ActionInvalid(i, action, data);
            }
        }

        _checkSlippageAndTransfer(slippage);
        return true;
    }
}
