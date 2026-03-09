// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";

import {IPSM, WAD, DAI, USDS} from "src/core/MakerPSM.sol";

import {Shim} from "./SettlerBasePairTest.t.sol";
import {MainnetSettlerMetaTxn as SettlerMetaTxn} from "src/chains/Mainnet/MetaTxn.sol";

import {Settler} from "src/Settler.sol";
import {SettlerMetaTxnPairTest} from "./SettlerMetaTxnPairTest.t.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {ActionDataBuilder} from "../utils/ActionDataBuilder.sol";

IERC20 constant USDC = IERC20(0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48);

contract MakerPsmLiteTest is SettlerMetaTxnPairTest {
    function setUp() public virtual override {
        if (address(makerPsm()) != address(0)) {
            vm.makePersistent(address(fromToken()));
            vm.makePersistent(address(toToken()));
        }

        super.setUp();

        if (address(makerPsm()) != address(0)) {
            persistPsm();

            // DAI must be approved to the PSM
            // USDC must be approved to the gemJoin
            // This is pedantry because for the lite PSM, it is its own gemJoin
            if (makerPsmBuyGem()) {
                // `fromToken()` is DAI; `toToken()` is USDC
                vm.startPrank(address(settler));
                fromToken().approve(address(makerPsm()), type(uint256).max);
                toToken().approve(makerPsm().gemJoin(), type(uint256).max);
                vm.stopPrank();

                vm.startPrank(address(settlerMetaTxn));
                fromToken().approve(address(makerPsm()), type(uint256).max);
                toToken().approve(makerPsm().gemJoin(), type(uint256).max);
                vm.stopPrank();
            } else {
                // `fromToken()` is USDC; `toToken()` is DAI
                vm.startPrank(address(settler));
                fromToken().approve(makerPsm().gemJoin(), type(uint256).max);
                toToken().approve(address(makerPsm()), type(uint256).max);
                vm.stopPrank();

                vm.startPrank(address(settlerMetaTxn));
                fromToken().approve(makerPsm().gemJoin(), type(uint256).max);
                toToken().approve(address(makerPsm()), type(uint256).max);
                vm.stopPrank();
            }

            if (makerPsmBuyGem()) {
                _amountOut = (amount() * 10 ** toToken().decimals()) / WAD;
            } else {
                _amountOut = (amount() * WAD) / 10 ** fromToken().decimals();
            }

            vm.makePersistent(address(PERMIT2));
            vm.makePersistent(address(allowanceHolder));
            vm.makePersistent(address(settler));
            vm.makePersistent(address(settlerMetaTxn));
        }
    }

    function persistPsm() internal setMakerPsmLiteBlockNumber {
        vm.makePersistent(address(makerPsm()));
    }

    function makerPsmLiteBlockNumber() internal view virtual returns (uint256) {
        return 20569313;
    }

    modifier setMakerPsmLiteBlockNumber() {
        uint256 blockNumber = (new Shim()).blockNumber();
        vm.rollFork(makerPsmLiteBlockNumber());
        vm.setEvmVersion("osaka");
        assert(address(makerPsm()).code.length > 0);
        _;
        vm.rollFork(blockNumber);
        vm.setEvmVersion("osaka");
    }

    function makerPsm() internal view virtual returns (IPSM) {
        return IPSM(0xf6e72Db5454dd049d0788e411b06CfAF16853042);
    }

    function _testName() internal pure virtual override returns (string memory) {
        return "USDC-DAI";
    }

    function dai() internal pure virtual returns (IERC20) {
        return DAI;
    }

    function fromToken() internal pure virtual override returns (IERC20) {
        return USDC;
    }

    function toToken() internal pure virtual override returns (IERC20) {
        return dai();
    }

    function amount() internal pure virtual override returns (uint256) {
        return 1000e6;
    }

    function makerPsmBuyGem() internal view returns (bool) {
        return fromToken() == dai();
    }

    function uniswapV3Path() internal override returns (bytes memory) {
        return new bytes(0);
    }

    uint256 internal _amountOut;

    function amountOut() internal view virtual returns (uint256) {
        return _amountOut;
    }

    function testSettler_makerPsmLite() public skipIf(address(makerPsm()) == address(0)) setMakerPsmLiteBlockNumber {
        (ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig) = _getDefaultFromPermit2();

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.TRANSFER_FROM, (address(settler), permit, sig)),
            abi.encodeCall(
                ISettlerActions.MAKERPSM,
                (FROM, 10_000, makerPsmBuyGem(), amountOut(), address(makerPsm()), address(dai()))
            )
        );
        ISettlerBase.AllowedSlippage memory allowedSlippage = ISettlerBase.AllowedSlippage({
            recipient: payable(address(0)),
            buyToken: IERC20(address(0)),
            minAmountOut: 0
        });
        Settler _settler = settler;
        uint256 beforeBalanceFrom = balanceOf(fromToken(), FROM);
        uint256 beforeBalanceTo = balanceOf(toToken(), FROM);

        vm.startPrank(FROM, FROM);
        snapStartName(string.concat("settler_makerPsmLite_", makerPsmBuyGem() ? "buy" : "sell", "Gem"));
        _settler.execute(allowedSlippage, actions, bytes32(0));
        snapEnd();
        vm.stopPrank();

        uint256 afterBalanceTo = toToken().balanceOf(FROM);
        assertGt(afterBalanceTo, beforeBalanceTo);
        uint256 afterBalanceFrom = fromToken().balanceOf(FROM);
        assertEq(afterBalanceFrom + amount(), beforeBalanceFrom);
    }

    function testSettler_metaTxn_makerPsmLite()
        public
        skipIf(address(makerPsm()) == address(0))
        setMakerPsmLiteBlockNumber
    {
        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(fromToken()), amount(), PERMIT2_FROM_NONCE);

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.METATXN_TRANSFER_FROM, (address(settlerMetaTxn), permit)),
            abi.encodeCall(
                ISettlerActions.MAKERPSM,
                (FROM, 10_000, makerPsmBuyGem(), amountOut(), address(makerPsm()), address(dai()))
            )
        );
        ISettlerBase.AllowedSlippage memory allowedSlippage = ISettlerBase.AllowedSlippage({
            recipient: payable(address(0)),
            buyToken: IERC20(address(0)),
            minAmountOut: 0
        });

        bytes32[] memory actionHashes = new bytes32[](actions.length);
        for (uint256 i; i < actionHashes.length; i++) {
            actionHashes[i] = keccak256(actions[i]);
        }
        bytes32 actionsHash = keccak256(abi.encodePacked(actionHashes));
        bytes32 witness = keccak256(
            abi.encode(
                SLIPPAGE_AND_ACTIONS_TYPEHASH,
                allowedSlippage.recipient,
                allowedSlippage.buyToken,
                allowedSlippage.minAmountOut,
                actionsHash
            )
        );
        bytes memory sig = getPermitWitnessTransferSignature(
            permit, address(settlerMetaTxn), FROM_PRIVATE_KEY, FULL_PERMIT2_WITNESS_TYPEHASH, witness, permit2Domain
        );

        SettlerMetaTxn _settlerMetaTxn = settlerMetaTxn;
        uint256 beforeBalanceFrom = balanceOf(fromToken(), FROM);
        uint256 beforeBalanceTo = balanceOf(toToken(), FROM);

        snapStartName(string.concat("settler_metaTxn_makerPsmLite_", makerPsmBuyGem() ? "buy" : "sell", "Gem"));
        vm.startPrank(address(this), address(this));
        _settlerMetaTxn.executeMetaTxn(allowedSlippage, actions, bytes32(0), FROM, sig);
        snapEnd();
        vm.stopPrank();

        uint256 afterBalanceTo = toToken().balanceOf(FROM);
        assertGt(afterBalanceTo, beforeBalanceTo);
        uint256 afterBalanceFrom = fromToken().balanceOf(FROM);
        assertEq(afterBalanceFrom + amount(), beforeBalanceFrom);
    }
}

contract MakerPsmLiteTestBuyGem is MakerPsmLiteTest {
    function _testName() internal pure virtual override returns (string memory) {
        return "DAI-USDC";
    }

    function fromToken() internal pure override returns (IERC20) {
        return super.toToken();
    }

    function toToken() internal pure override returns (IERC20) {
        return super.fromToken();
    }

    function amount() internal pure override returns (uint256) {
        return 1000 * WAD;
    }
}

contract MakerSkyPSMTest is MakerPsmLiteTest {
    function dai() internal pure override returns (IERC20) {
        return USDS;
    }

    function makerPsm() internal pure override returns (IPSM) {
        return IPSM(0xA188EEC8F81263234dA3622A406892F3D630f98c);
    }

    function _testName() internal pure virtual override returns (string memory) {
        return "USDC-USDS";
    }

    function makerPsmLiteBlockNumber() internal pure override returns (uint256) {
        return 21668728;
    }

    function _testBlockNumber() internal pure override returns (uint256) {
        return 21668728;
    }
}

contract MakerSkyPsmLiteTestBuyGem is MakerSkyPSMTest {
    function _testName() internal pure virtual override returns (string memory) {
        return "USDS-USDC";
    }

    function fromToken() internal pure override returns (IERC20) {
        return super.toToken();
    }

    function toToken() internal pure override returns (IERC20) {
        return super.fromToken();
    }

    function amount() internal pure override returns (uint256) {
        return 1000 * WAD;
    }
}
