// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";

import {BnbSettler} from "src/chains/Bnb/TakerSubmitted.sol";
import {FLUX_VAULT} from "src/core/FluxPool.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";
import {ActionDataBuilder} from "test/utils/ActionDataBuilder.sol";
import {SettlerBasePairTest} from "./SettlerBasePairTest.t.sol";

error FluxError(uint16 code);

contract FluxPoolIntegrationTest is SettlerBasePairTest {
    IERC20 private constant USDT = IERC20(0x55d398326f99059fF775485246999027B3197955);
    IERC20 private constant WBNB = IERC20(0xbb4CdB9CBd36B01bD1cBaEBF2De08d9173bc095c);
    address private constant FLUX_QUOTE_CURVE = 0xcDDBC1CfF0B5b5F83ef85cb42FB742Ee8E620Ad0;
    bytes32 private constant POOL_ID = 0xa3b94efb3bde9749d7e2735e0dd4a4c9a7b502bb3c6c44ae30fd35b2563038ae;
    uint256 private constant QUOTE_CURVE_ALLOWLIST_SLOT = 6;
    uint256 private constant VAULT_ALLOWLIST_SLOT = 4;
    uint256 private constant EXPECTED_AMOUNT_OUT = 1643839108295557;

    function _testName() internal pure override returns (string memory) {
        return "USDT-WBNB";
    }

    function _testChainId() internal pure override returns (string memory) {
        return "bnb";
    }

    function _testBlockNumber() internal pure override returns (uint256) {
        return 115741100;
    }

    function fromToken() internal pure override returns (IERC20) {
        return USDT;
    }

    function toToken() internal pure override returns (IERC20) {
        return WBNB;
    }

    function amount() internal pure override returns (uint256) {
        return 1 ether;
    }

    function settlerInitCode() internal pure override returns (bytes memory) {
        return bytes.concat(type(BnbSettler).creationCode, abi.encode(bytes20(0)));
    }

    function setUp() public override {
        super.setUp();
        vm.etch(FROM, "");
        vm.makePersistent(FROM);
        safeApproveIfBelow(fromToken(), FROM, address(PERMIT2), amount());

        _setAllowed(FLUX_QUOTE_CURVE, QUOTE_CURVE_ALLOWLIST_SLOT, true);
        _setAllowed(FLUX_VAULT, VAULT_ALLOWLIST_SLOT, true);
    }

    function testFluxPool() public {
        uint256 vaultBalanceBefore = USDT.balanceOf(FLUX_VAULT);
        snapStartName("settler_fluxPool");
        _executeFluxPool();
        snapEnd();

        assertEq(USDT.balanceOf(FROM), 0);
        assertEq(USDT.balanceOf(FLUX_VAULT) - vaultBalanceBefore, amount());
        assertEq(WBNB.balanceOf(FROM), EXPECTED_AMOUNT_OUT);
    }

    function testFluxPoolRequiresQuoteCurveAllowlist() public {
        _setAllowed(FLUX_QUOTE_CURVE, QUOTE_CURVE_ALLOWLIST_SLOT, false);
        vm.expectRevert(abi.encodeWithSelector(FluxError.selector, uint16(2007)));
        _executeFluxPool();
    }

    function testFluxPoolRequiresVaultAllowlist() public {
        _setAllowed(FLUX_VAULT, VAULT_ALLOWLIST_SLOT, false);
        vm.expectRevert(abi.encodeWithSelector(FluxError.selector, uint16(4003)));
        _executeFluxPool();
    }

    function _executeFluxPool() private {
        bytes[] memory actions = ActionDataBuilder.build(
            _getDefaultFromPermit2Action(),
            abi.encodeCall(ISettlerActions.FLUXPOOL, (address(USDT), 1_000_000, POOL_ID, true, address(WBNB), 1))
        );
        ISettlerBase.AllowedSlippage memory slippage =
            ISettlerBase.AllowedSlippage({recipient: FROM, buyToken: WBNB, minAmountOut: 1});

        vm.prank(FROM);
        settler.execute(slippage, actions, bytes32(0));
    }

    function _setAllowed(address target, uint256 slot, bool allowed) private {
        vm.store(target, keccak256(abi.encode(address(settler), slot)), bytes32(uint256(allowed ? 1 : 0)));
    }
}
