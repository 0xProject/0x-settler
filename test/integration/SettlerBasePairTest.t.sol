// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {BasePairTest} from "./BasePairTest.t.sol";

import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";
import {ISettlerActions} from "../../src/ISettlerActions.sol";
import {IZeroEx} from "./vendor/IZeroEx.sol";

import {IERC20} from "../../src/IERC20.sol";
import {LibBytes} from "../utils/LibBytes.sol";
import {SafeTransferLib} from "../../src/vendor/SafeTransferLib.sol";

import {AllowanceHolder} from "../../src/allowanceholder/AllowanceHolder.sol";
import {IAllowanceHolder} from "../../src/allowanceholder/IAllowanceHolder.sol";
import {Settler} from "../../src/Settler.sol";

abstract contract SettlerBasePairTest is BasePairTest {
    using SafeTransferLib for IERC20;
    using LibBytes for bytes;

    uint256 internal PERMIT2_FROM_NONCE = 1;
    uint256 internal PERMIT2_MAKER_NONCE = 1;

    Settler internal settler;
    IAllowanceHolder internal allowanceHolder;
    IZeroEx internal ZERO_EX = IZeroEx(0xDef1C0ded9bec7F1a1670819833240f027b25EfF);

    function setUp() public virtual override {
        super.setUp();
        allowanceHolder = IAllowanceHolder(address(new AllowanceHolder()));
        settler = new Settler(
            address(PERMIT2),
            0x1F98431c8aD98523631AE4a59f267346ea31F984, // UniV3 Factory
            0xe34f199b19b2b4f47f68442619d555527d244f78a3297ea89325f843f87b8b54, // UniV3 pool init code hash
            0x6B175474E89094C44Da98b954EedeAC495271d0F, // DAI
            address(allowanceHolder) // allowance holder
        );
    }

    bytes32 internal constant CONSIDERATION_TYPEHASH =
        keccak256("Consideration(address token,uint256 amount,address counterparty,bool partialFillAllowed)");
    bytes32 internal constant OTC_PERMIT2_WITNESS_TYPEHASH = keccak256(
        "PermitWitnessTransferFrom(TokenPermissions permitted,address spender,uint256 nonce,uint256 deadline,Consideration consideration)Consideration(address token,uint256 amount,address counterparty,bool partialFillAllowed)TokenPermissions(address token,uint256 amount)"
    );

    function _getDefaultFromPermit2Action() internal returns (bytes memory) {
        (ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig) = _getDefaultFromPermit2();
        return abi.encodeCall(ISettlerActions.TRANSFER_FROM, (address(settler), permit, sig));
    }

    function _getDefaultFromPermit2() internal returns (ISignatureTransfer.PermitTransferFrom memory, bytes memory) {
        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(fromToken()), amount(), PERMIT2_FROM_NONCE);
        bytes memory sig = getPermitTransferSignature(permit, address(settler), FROM_PRIVATE_KEY, permit2Domain);
        return (permit, sig);
    }
}
