// SPDX-License-Identifier: MIT
pragma solidity ^0.8.17;

import {ERC20} from "solmate/src/tokens/ERC20.sol";
import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";

import {BasePairTest} from "./BasePairTest.t.sol";

import {SafeTransferLib} from "../../../src/utils/SafeTransferLib.sol";
import {Settler} from "../../../src/Settler.sol";

abstract contract SettlerBaseTest is BasePairTest {
    using SafeTransferLib for ERC20;

    uint256 private PERMIT2_FROM_NONCE = 1;
    uint256 private PERMIT2_MAKER_NONCE = 1;

    Settler private settler;

    function setUp() public virtual override {
        super.setUp();
        settler = getSettler();

        warmPermit2Nonce(FROM);
        warmPermit2Nonce(MAKER);

        safeApproveIfBelow(fromToken(), FROM, address(PERMIT2), amount());
        safeApproveIfBelow(toToken(), MAKER, address(PERMIT2), amount());
    }

    function getSettler() private returns (Settler settler) {
        settler = new Settler(
            address(PERMIT2), 
            address(ZERO_EX), // ZeroEx
            0x1F98431c8aD98523631AE4a59f267346ea31F984, // UniV3 Factory
            0xe34f199b19b2b4f47f68442619d555527d244f78a3297ea89325f843f87b8b54 // UniV3 pool init code hash
        );
    }

    function _getDefaultPermit2DataEncoded() internal returns (bytes memory) {
        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(fromToken()), uint160(amount()), PERMIT2_FROM_NONCE);
        bytes memory sig =
            getPermitTransferSignature(permit, address(settler), FROM_PRIVATE_KEY, PERMIT2.DOMAIN_SEPARATOR());

        return abi.encode(permit, sig);
    }
}
