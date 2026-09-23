// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";

import {BaseSettler} from "src/chains/Base/TakerSubmitted.sol";
import {BnbSettler} from "src/chains/Bnb/TakerSubmitted.sol";
import {FLUX_VAULT} from "src/core/FluxPool.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";
import {ActionDataBuilder} from "test/utils/ActionDataBuilder.sol";
import {SettlerBasePairTest} from "./SettlerBasePairTest.t.sol";

error FluxError(uint16 code);

abstract contract FluxPoolTest is SettlerBasePairTest {
    uint256 private constant FEE_MANAGER_ACCOUNT_SLOT = 2;
    uint256 private constant VAULT_ALLOWLIST_SLOT = 4;

    function fluxFeeManager() internal pure virtual returns (address);
    function poolId() internal pure virtual returns (bytes32);
    function expectedAmountOut() internal pure virtual returns (uint256);

    function setUp() public override {
        super.setUp();
        vm.etch(FROM, "");
        safeApproveIfBelow(fromToken(), FROM, address(PERMIT2), amount());

        _setAllowed(fluxFeeManager(), FEE_MANAGER_ACCOUNT_SLOT, true);
        _setAllowed(FLUX_VAULT, VAULT_ALLOWLIST_SLOT, true);
    }

    function testFluxPool() public {
        uint256 vaultBalanceBefore = fromToken().balanceOf(FLUX_VAULT);
        (ISettlerBase.AllowedSlippage memory slippage, bytes[] memory actions) = _fluxPoolCall(1);

        vm.prank(FROM);
        snapStartName("settler_fluxPool");
        settler.execute(slippage, actions, bytes32(0));
        snapEnd();

        assertEq(fromToken().balanceOf(FROM), 0);
        assertEq(fromToken().balanceOf(FLUX_VAULT) - vaultBalanceBefore, amount());
        assertEq(toToken().balanceOf(FROM), expectedAmountOut());
    }

    function testFluxPoolRequiresFeeManagerAllowlist() public {
        _setAllowed(fluxFeeManager(), FEE_MANAGER_ACCOUNT_SLOT, false);
        vm.expectRevert(abi.encodeWithSelector(FluxError.selector, uint16(2007)));
        _executeFluxPool(1);
    }

    function testFluxPoolRequiresVaultAllowlist() public {
        _setAllowed(FLUX_VAULT, VAULT_ALLOWLIST_SLOT, false);
        vm.expectRevert(abi.encodeWithSelector(FluxError.selector, uint16(4003)));
        _executeFluxPool(1);
    }

    function testFluxPoolEnforcesMinimumOutput() public {
        vm.expectRevert(abi.encodeWithSelector(FluxError.selector, uint16(3001)));
        _executeFluxPool(expectedAmountOut() + 1);
    }

    function _executeFluxPool(uint256 minBuyAmount) private {
        (ISettlerBase.AllowedSlippage memory slippage, bytes[] memory actions) = _fluxPoolCall(minBuyAmount);

        vm.prank(FROM);
        settler.execute(slippage, actions, bytes32(0));
    }

    function _fluxPoolCall(uint256 minBuyAmount)
        private
        returns (ISettlerBase.AllowedSlippage memory slippage, bytes[] memory actions)
    {
        actions = ActionDataBuilder.build(
            _getDefaultFromPermit2Action(),
            abi.encodeCall(ISettlerActions.FLUXPOOL, (address(fromToken()), 1_000_000, poolId(), true, minBuyAmount))
        );
        slippage = ISettlerBase.AllowedSlippage({recipient: FROM, buyToken: toToken(), minAmountOut: 1});
    }

    function _setAllowed(address target, uint256 slot, bool allowed) private {
        vm.store(target, keccak256(abi.encode(address(settler), slot)), bytes32(uint256(allowed ? 1 : 0)));
    }
}

contract BnbFluxPoolTest is FluxPoolTest {
    function _testName() internal pure override returns (string memory) {
        return "USDT-WBNB";
    }

    function _testChainId() internal pure override returns (string memory) {
        return "bnb";
    }

    function _testBlockNumber() internal pure override returns (uint256) {
        return 122229417;
    }

    function fromToken() internal pure override returns (IERC20) {
        return IERC20(0x55d398326f99059fF775485246999027B3197955);
    }

    function toToken() internal pure override returns (IERC20) {
        return IERC20(0xbb4CdB9CBd36B01bD1cBaEBF2De08d9173bc095c);
    }

    function amount() internal pure override returns (uint256) {
        return 1 ether;
    }

    function settlerInitCode() internal pure override returns (bytes memory) {
        return bytes.concat(type(BnbSettler).creationCode, abi.encode(bytes20(0)));
    }

    function fluxFeeManager() internal pure override returns (address) {
        return 0x25Ba19c2971C901aEd02c184a69a9ec311Ac41f2;
    }

    function poolId() internal pure override returns (bytes32) {
        return 0xa3b94efb3bde9749d7e2735e0dd4a4c9a7b502bb3c6c44ae30fd35b2563038ae;
    }

    function expectedAmountOut() internal pure override returns (uint256) {
        return 1403694867934358;
    }
}

contract BaseFluxPoolTest is FluxPoolTest {
    function _testName() internal pure override returns (string memory) {
        return "WETH-USDC";
    }

    function _testChainId() internal pure override returns (string memory) {
        return "base";
    }

    function _testBlockNumber() internal pure override returns (uint256) {
        return 51636805;
    }

    function fromToken() internal pure override returns (IERC20) {
        return IERC20(0x4200000000000000000000000000000000000006);
    }

    function toToken() internal pure override returns (IERC20) {
        return IERC20(0x833589fCD6eDb6E08f4c7C32D4f71b54bdA02913);
    }

    function amount() internal pure override returns (uint256) {
        return 0.001 ether;
    }

    function settlerInitCode() internal pure override returns (bytes memory) {
        return bytes.concat(type(BaseSettler).creationCode, abi.encode(bytes20(0)));
    }

    function fluxFeeManager() internal pure override returns (address) {
        return 0xe3F20402258FfE233c1172f04F38635C8D95716b;
    }

    function poolId() internal pure override returns (bytes32) {
        return 0x3c3d7b1b3f1024a4538562b741644a05e9d3efa556ce70f6d98adcd507b37188;
    }

    function expectedAmountOut() internal pure override returns (uint256) {
        return 2726979;
    }
}
