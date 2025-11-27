// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {BASE_SELECTOR} from "src/core/Renegade.sol";
import {BaseSettler} from "src/chains/Base/TakerSubmitted.sol";
import {ActionDataBuilder} from "../utils/ActionDataBuilder.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";
import {SettlerBasePairTest} from "./SettlerBasePairTest.t.sol";
import {
    BASE_GAS_SPONSOR,
    BASE_TXN_CALLDATA,
    BASE_TXN_BLOCK,
    BASE_USDC,
    BASE_WETH,
    BASE_AMOUNT
} from "./RenegadeTxn.t.sol";

abstract contract RenegadeTest is SettlerBasePairTest {
    uint32 selector;
    address target;
    bytes txnCalldata;

    function setUp() public virtual override {
        super.setUp();

        vm.label(target, "GasSponsor");
        vm.label(address(fromToken()), "USDC");
        vm.label(address(toToken()), "WETH");
    }

    function testRerunTxn() public {
        bytes memory _calldata = txnCalldata;
        assembly ("memory-safe") {
            let len := mload(_calldata)
            _calldata := add(0x04, _calldata)
            mstore(_calldata, sub(len, 4))
        }

        deal(address(fromToken()), address(this), amount());
        fromToken().approve(address(allowanceHolder), amount());
        allowanceHolder.exec(
            address(settler),
            address(fromToken()),
            amount(),
            payable(address(settler)),
            abi.encodeCall(
                settler.execute,
                (
                    ISettlerBase.AllowedSlippage({
                        recipient: payable(address(this)),
                        buyToken: toToken(),
                        minAmountOut: 0
                    }),
                    ActionDataBuilder.build(
                        abi.encodeCall(
                            ISettlerActions.TRANSFER_FROM,
                            (
                                address(settler),
                                defaultERC20PermitTransfer(address(fromToken()), amount(), 0 /* nonce */ ),
                                new bytes(0) /* sig (empty) */
                            )
                        ),
                        abi.encodeCall(ISettlerActions.RENEGADE, (target, address(fromToken()), _calldata))
                    ),
                    bytes32(0)
                )
            )
        );
    }
}

contract RenegadeBaseIntegrationTest is RenegadeTest {
    function setUp() public virtual override {
        target = BASE_GAS_SPONSOR;
        txnCalldata = BASE_TXN_CALLDATA;
        selector = BASE_SELECTOR;

        super.setUp();
    }

    function settlerInitCode() internal virtual override returns (bytes memory) {
        return bytes.concat(type(BaseSettler).creationCode, abi.encode(bytes20(0)));
    }

    function _testChainId() internal pure virtual override returns (string memory) {
        return "base";
    }

    function _testBlockNumber() internal pure virtual override returns (uint256) {
        return BASE_TXN_BLOCK - 1;
    }

    function fromToken() internal pure virtual override returns (IERC20) {
        return BASE_USDC;
    }

    function toToken() internal pure virtual override returns (IERC20) {
        return BASE_WETH;
    }

    function _testName() internal pure virtual override returns (string memory) {
        return "BASE-WETH";
    }

    function amount() internal pure virtual override returns (uint256) {
        return BASE_AMOUNT;
    }
}
