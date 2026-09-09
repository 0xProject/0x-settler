// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";

import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {ActionDataBuilder} from "../utils/ActionDataBuilder.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";
import {Settler} from "src/Settler.sol";

import {SafeTransferLib} from "src/vendor/SafeTransferLib.sol";

import {
    IEVC,
    IEulerSwap,
    EulerSwapLib,
    ParamsLib,
    FastEulerSwap,
    FastEvc,
    IEVault,
    FastEvault,
    IOracle,
    FastOracle
} from "src/core/EulerSwap.sol";

import {AllowanceHolderPairTest} from "./AllowanceHolderPairTest.t.sol";
import {IEulerSwapFactory} from "@eulerswap/interfaces/IEulerSwapFactory.sol";
import {IEulerSwap as IEulerSwapV1} from "@eulerswap/interfaces/IEulerSwap.sol";

IEVC constant EVC = IEVC(0x0C9a3dd6b8F28529d72d7f9cE918D493519EE383);

interface IEVCOperator {
    function setAccountOperator(address account, address operator, bool authorized) external payable;
}

abstract contract EulerSwapTest is AllowanceHolderPairTest {
    using SafeTransferLib for IERC20;
    using SafeTransferLib for IEVault;
    using ParamsLib for IEulerSwap;
    using ParamsLib for ParamsLib.Params;
    using FastEulerSwap for IEulerSwap;
    using FastEvc for IEVC;
    using FastEvault for IEVault;
    using FastOracle for IOracle;

    function eulerSwapPool() internal view virtual returns (address) {
        return address(0);
    }

    function eulerSwapBlock() internal view virtual returns (uint256) {
        return 0;
    }

    function eulerSwapAmount() internal view virtual returns (uint256) {
        return amount();
    }

    function reverseTestName() internal view virtual returns (string memory);

    modifier setEulerSwapBlock() {
        uint256 blockNumber = vm.getBlockNumber();
        vm.rollFork(eulerSwapBlock());
        vm.setEvmVersion("osaka");
        _;
        vm.rollFork(blockNumber);
        vm.setEvmVersion("osaka");
    }

    function _setEulerSwapLabels() private setEulerSwapBlock {
        vm.label(address(EVC), "EVC");
        vm.label(eulerSwapPool(), string.concat("EulerSwap ", _testName(), " pool"));
        IEulerSwap.Params memory params = IEulerSwap(eulerSwapPool()).getParams();
        vm.label(params.eulerAccount, "Euler Account");
        string memory vault0UnderlyingSymbol = IERC20(params.vault0.asset()).symbol();
        string memory vault1UnderlyingSymbol = IERC20(params.vault1.asset()).symbol();
        vm.label(address(params.vault0), string.concat("Euler Vault ", vault0UnderlyingSymbol));
        vm.label(address(params.vault1), string.concat("Euler Vault ", vault1UnderlyingSymbol));
        vm.label(address(params.vault0.dToken()), string.concat("Euler dToken ", vault0UnderlyingSymbol));
        vm.label(address(params.vault1.dToken()), string.concat("Euler dToken ", vault1UnderlyingSymbol));
    }

    function setUp() public virtual override {
        super.setUp();
        if (eulerSwapPool() != address(0)) {
            vm.makePersistent(address(PERMIT2));
            vm.makePersistent(address(allowanceHolder));
            vm.makePersistent(address(settler));
            vm.makePersistent(address(fromToken()));
            vm.makePersistent(address(toToken()));
            deal(address(toToken()), FROM, eulerSwapAmount());
            vm.prank(FROM, FROM);
            toToken().safeApprove(address(PERMIT2), type(uint256).max);
            _setEulerSwapLabels();
        }
    }

    function testEulerSwap() public skipIf(eulerSwapPool() == address(0)) setEulerSwapBlock {
        (ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig) =
            _getDefaultFromPermit2(eulerSwapAmount());

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.TRANSFER_FROM, (address(settler), permit, sig)),
            abi.encodeCall(ISettlerActions.EULERSWAP, (FROM, address(fromToken()), 1_000_000, eulerSwapPool(), true, 0))
        );

        ISettlerBase.AllowedSlippage memory allowedSlippage = ISettlerBase.AllowedSlippage({
            recipient: payable(address(0)), buyToken: IERC20(address(0)), minAmountOut: 0
        });
        Settler _settler = settler;
        uint256 beforeBalanceFrom = balanceOf(fromToken(), FROM);
        uint256 beforeBalanceTo = balanceOf(toToken(), FROM);

        vm.startPrank(FROM, FROM);
        snapStartName("settler_eulerSwap");
        _settler.execute(allowedSlippage, actions, bytes32(0));
        snapEnd();
        vm.stopPrank();

        uint256 afterBalanceTo = toToken().balanceOf(FROM);
        assertGt(afterBalanceTo, beforeBalanceTo);
        uint256 afterBalanceFrom = fromToken().balanceOf(FROM);
        assertEq(afterBalanceFrom + eulerSwapAmount(), beforeBalanceFrom);
    }

    function testEulerSwapReverse() public skipIf(eulerSwapPool() == address(0)) setEulerSwapBlock {
        (ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig) =
            _getDefaultFromPermit2(toToken(), eulerSwapAmount());

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.TRANSFER_FROM, (address(settler), permit, sig)),
            abi.encodeCall(ISettlerActions.EULERSWAP, (FROM, address(toToken()), 1_000_000, eulerSwapPool(), false, 0))
        );

        ISettlerBase.AllowedSlippage memory allowedSlippage = ISettlerBase.AllowedSlippage({
            recipient: payable(address(0)), buyToken: IERC20(address(0)), minAmountOut: 0
        });
        Settler _settler = settler;
        uint256 beforeBalanceFrom = balanceOf(toToken(), FROM);
        uint256 beforeBalanceTo = balanceOf(fromToken(), FROM);

        vm.startPrank(FROM, FROM);
        snapStart(string.concat("settler_eulerSwap_", reverseTestName()));
        _settler.execute(allowedSlippage, actions, bytes32(0));
        snapEnd();
        vm.stopPrank();

        uint256 afterBalanceTo = fromToken().balanceOf(FROM);
        assertGt(afterBalanceTo, beforeBalanceTo);
        uint256 afterBalanceFrom = toToken().balanceOf(FROM);
        assertEq(afterBalanceFrom + eulerSwapAmount(), beforeBalanceFrom);
    }

    function testEulerSwapCustody() public skipIf(eulerSwapPool() == address(0)) setEulerSwapBlock {
        (ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig) =
            _getDefaultFromPermit2(eulerSwapAmount());

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.TRANSFER_FROM, (eulerSwapPool(), permit, sig)),
            abi.encodeCall(ISettlerActions.EULERSWAP, (FROM, address(fromToken()), 0, eulerSwapPool(), true, 0))
        );

        ISettlerBase.AllowedSlippage memory allowedSlippage = ISettlerBase.AllowedSlippage({
            recipient: payable(address(0)), buyToken: IERC20(address(0)), minAmountOut: 0
        });
        Settler _settler = settler;
        uint256 beforeBalanceFrom = balanceOf(fromToken(), FROM);
        uint256 beforeBalanceTo = balanceOf(toToken(), FROM);

        vm.startPrank(FROM, FROM);
        snapStartName("settler_eulerSwapCustody");
        _settler.execute(allowedSlippage, actions, bytes32(0));
        snapEnd();
        vm.stopPrank();

        uint256 afterBalanceTo = toToken().balanceOf(FROM);
        assertGt(afterBalanceTo, beforeBalanceTo);
        uint256 afterBalanceFrom = fromToken().balanceOf(FROM);
        assertEq(afterBalanceFrom + eulerSwapAmount(), beforeBalanceFrom);
    }

    function _limits(IEulerSwap pool) private view returns (uint256 inLimit, uint256 outLimit) {
        (uint256 reserve0, uint256 reserve1) = pool.fastGetReserves();
        return EulerSwapLib.calcLimits(EVC, pool, true, pool.fastGetParams(), reserve0, reserve1);
    }

    function _deposit(IEVault vault, address receiver, uint256 amount) private {
        deal(address(vault.fastAsset()), address(this), amount);
        vault.fastAsset().safeApprove(address(vault), amount);
        vault.deposit(amount, receiver);
    }

    function _sellAtInputLimit(IEulerSwap pool) private returns (uint256 received) {
        (uint256 inLimit,) = _limits(pool);
        deal(address(fromToken()), FROM, inLimit + 1);
        (ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig) = _getDefaultFromPermit2(inLimit + 1);
        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.TRANSFER_FROM, (address(settler), permit, sig)),
            abi.encodeCall(ISettlerActions.EULERSWAP, (FROM, address(fromToken()), 1_000_000, address(pool), true, 0))
        );
        uint256 before = toToken().balanceOf(FROM);
        vm.prank(FROM, FROM);
        settler.execute(ISettlerBase.AllowedSlippage(payable(address(0)), IERC20(address(0)), 0), actions, bytes32(0));
        return toToken().balanceOf(FROM) - before;
    }

    // Leave headroom for the net input, but not its fee.
    function testEulerSwapAtSupplyCap() public skipIf(eulerSwapPool() == address(0)) setEulerSwapBlock {
        IEulerSwap pool = IEulerSwap(eulerSwapPool());
        ParamsLib.Params params = pool.fastGetParams();
        (uint256 grossBound,) = _limits(pool);
        uint256 headroom = params.vault0().fastMaxDeposit(params.eulerAccount());
        _deposit(params.vault0(), address(this), headroom - grossBound * (1e18 - params.fee()) / 1e18);
        assertGt(_sellAtInputLimit(pool), 0);
    }

    // At 1000:1, curve rounding quotes more than the output vault's cash.
    function testEulerSwapAtOutputCash() public skipIf(eulerSwapPool() == address(0)) setEulerSwapBlock {
        IEulerSwapV1.Params memory params = IEulerSwapV1(eulerSwapPool()).getParams();
        // Enough collateral for the account to borrow the whole output cash at the skewed price.
        _deposit(IEVault(params.vault0), params.eulerAccount, 40_000_000e6);
        (params.priceX, params.priceY) = (1000e18, 1e18);
        IEulerSwap pool = IEulerSwap(0xf462e46E0AF6cD3E5dD6231F5F8Fba562940A8a8);
        vm.startPrank(params.eulerAccount);
        IEVCOperator(address(EVC)).setAccountOperator(params.eulerAccount, eulerSwapPool(), false);
        IEVCOperator(address(EVC)).setAccountOperator(params.eulerAccount, address(pool), true);
        IEulerSwapFactory(0xb013be1D0D380C13B58e889f412895970A2Cf228)
            .deployPool(
                params,
                IEulerSwapV1.InitialState(params.equilibriumReserve0, params.equilibriumReserve1),
                bytes32(uint256(734)) // gives the address the hook flag bits (0x28a8) the factory requires
            );
        vm.stopPrank();
        (, uint256 outLimit) = _limits(pool);
        assertEq(_sellAtInputLimit(pool), outLimit);
    }

    function testSolvencyCheck() public skipIf(eulerSwapPool() == address(0)) setEulerSwapBlock {
        IEulerSwap pool = IEulerSwap(eulerSwapPool());
        ParamsLib.Params params = pool.fastGetParams();

        (uint256 reserve0, uint256 reserve1) = pool.fastGetReserves();
        uint256 amountOut = EulerSwapLib.findCurvePoint(eulerSwapAmount(), true, params, reserve0, reserve1);
        assertTrue(
            EulerSwapLib.checkSolvency(
                EVC,
                address(params.eulerAccount()),
                address(params.vault0()),
                address(params.vault1()),
                true,
                eulerSwapAmount(),
                amountOut
            ),
            "Account is insolvent after swap"
        );
    }

    function testSolvencyCheckReverse() public skipIf(eulerSwapPool() == address(0)) setEulerSwapBlock {
        IEulerSwap pool = IEulerSwap(eulerSwapPool());
        ParamsLib.Params params = pool.fastGetParams();

        (uint256 reserve0, uint256 reserve1) = pool.fastGetReserves();
        uint256 amountOut = EulerSwapLib.findCurvePoint(eulerSwapAmount(), false, params, reserve0, reserve1);
        assertTrue(
            EulerSwapLib.checkSolvency(
                EVC,
                address(params.eulerAccount()),
                address(params.vault0()),
                address(params.vault1()),
                false,
                eulerSwapAmount(),
                amountOut
            ),
            "Account is insolvent after swap"
        );
    }

    function testSolvencyCheckAtPoolLimit() public skipIf(eulerSwapPool() == address(0)) setEulerSwapBlock {
        IEulerSwap pool = IEulerSwap(eulerSwapPool());
        ParamsLib.Params params = pool.fastGetParams();

        (uint256 reserve0, uint256 reserve1) = pool.fastGetReserves();
        (uint256 amountIn, uint256 amountOut) = EulerSwapLib.calcLimits(EVC, pool, true, params, reserve0, reserve1);
        assertTrue(
            EulerSwapLib.checkSolvency(
                EVC,
                address(params.eulerAccount()),
                address(params.vault0()),
                address(params.vault1()),
                true,
                amountIn,
                amountOut
            ),
            "Account is insolvent after swapping at pool limit"
        );
    }

    function testSolvencyCheckAtPoolLimitReverse() public skipIf(eulerSwapPool() == address(0)) setEulerSwapBlock {
        IEulerSwap pool = IEulerSwap(eulerSwapPool());
        ParamsLib.Params params = pool.fastGetParams();

        (uint256 reserve0, uint256 reserve1) = pool.fastGetReserves();
        (uint256 amountIn, uint256 amountOut) = EulerSwapLib.calcLimits(EVC, pool, false, params, reserve0, reserve1);
        assertTrue(
            EulerSwapLib.checkSolvency(
                EVC,
                address(params.eulerAccount()),
                address(params.vault0()),
                address(params.vault1()),
                false,
                amountIn,
                amountOut
            ),
            "Account is insolvent after swapping at pool limit"
        );
    }

    function testSolvencyCheckFailsIfCollateralIsNotEnough()
        public
        skipIf(eulerSwapPool() == address(0))
        setEulerSwapBlock
    {
        IEulerSwap pool = IEulerSwap(eulerSwapPool());
        ParamsLib.Params params = pool.fastGetParams();
        address eulerAccount = address(params.eulerAccount());

        IEVault[] memory collaterals = EVC.fastGetCollaterals(eulerAccount);
        IEVault[] memory controllers = EVC.fastGetControllers(eulerAccount);
        assertEq(controllers.length, 1, "Multiple debt vaults");
        assertEq(address(controllers[0]), address(params.vault1()), "Debt vault is not vault1");

        IEVault debtVault = IEVault(controllers[0]);
        IOracle oracle = debtVault.fastOracle();
        IERC20 unitOfAccount = debtVault.fastUnitOfAccount();
        uint256 collateral;
        for (uint256 i = 0; i < collaterals.length; i++) {
            IEVault collateralVault = IEVault(collaterals[i]);
            (uint256 value,) = oracle.fastGetQuotes(
                collateralVault.fastConvertToAssets(collateralVault.fastBalanceOf(eulerAccount)),
                collateralVault.fastAsset(),
                unitOfAccount
            );

            collateral += (value * debtVault.fastLTVBorrow(collateralVault));
        }
        (, uint256 debt) =
            oracle.fastGetQuotes(debtVault.fastDebtOf(eulerAccount), debtVault.fastAsset(), unitOfAccount);
        uint256 amountOut = (collateral - debt * 1e4) / 1e4;

        assertFalse(
            EulerSwapLib.checkSolvency(
                EVC,
                address(params.eulerAccount()),
                address(params.vault0()),
                address(params.vault1()),
                true,
                0,
                amountOut + 1
            ),
            "Account should be insolvent"
        );
    }
}
