// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";

import {Shim} from "./SettlerBasePairTest.t.sol";
import {ActionDataBuilder} from "../utils/ActionDataBuilder.sol";
import {MainnetSettlerMetaTxn as SettlerMetaTxn} from "src/chains/Mainnet/MetaTxn.sol";
import {Settler} from "src/Settler.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {AddressDerivation} from "src/utils/AddressDerivation.sol";
import {IAllowanceHolder} from "src/allowanceholder/IAllowanceHolder.sol";
import {maverickV2InitHash, maverickV2Factory} from "src/core/MaverickV2.sol";

import {SettlerMetaTxnPairTest} from "./SettlerMetaTxnPairTest.t.sol";

abstract contract MaverickV2PairTest is SettlerMetaTxnPairTest {
    function setUp() public virtual override {
        super.setUp();
        if (maverickV2Salt() != bytes32(0)) {
            vm.makePersistent(address(PERMIT2));
            vm.makePersistent(address(allowanceHolder));
            vm.makePersistent(address(settler));
            vm.makePersistent(address(settlerMetaTxn));
            vm.makePersistent(address(fromToken()));
            vm.makePersistent(address(toToken()));
        }
    }

    function maverickV2BlockNumber() internal view virtual returns (uint256) {
        return 20421077;
    }

    modifier setMaverickV2Block() {
        uint256 blockNumber = (new Shim()).blockNumber();
        vm.rollFork(maverickV2BlockNumber());
        _;
        vm.rollFork(blockNumber);
    }

    function maverickV2Salt() internal view virtual returns (bytes32) {
        return bytes32(0);
    }

    function maverickV2Pool() internal view returns (address) {
        return AddressDerivation.deriveDeterministicContract(maverickV2Factory, maverickV2Salt(), maverickV2InitHash);
    }

    function maverickV2TokenAIn() internal view virtual returns (bool) {
        return false;
    }

    function testMaverickV2() public skipIf(maverickV2Salt() == bytes32(0)) setMaverickV2Block {
        (ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig) = _getDefaultFromPermit2();

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.TRANSFER_FROM, (address(settler), permit, sig)),
            abi.encodeCall(
                ISettlerActions.MAVERICKV2,
                (FROM, address(fromToken()), 10_000, maverickV2Pool(), maverickV2TokenAIn(), 0)
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
        snapStartName("settler_maverickV2");
        _settler.execute(allowedSlippage, actions, bytes32(0));
        snapEnd();
        vm.stopPrank();

        uint256 afterBalanceTo = toToken().balanceOf(FROM);
        assertGt(afterBalanceTo, beforeBalanceTo);
        uint256 afterBalanceFrom = fromToken().balanceOf(FROM);
        assertEq(afterBalanceFrom + amount(), beforeBalanceFrom);
    }

    function testMaverickV2ZeroBps() public skipIf(maverickV2Salt() == bytes32(0)) setMaverickV2Block {
        (ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig) = _getDefaultFromPermit2();

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.TRANSFER_FROM, (maverickV2Pool(), permit, sig)),
            abi.encodeCall(
                ISettlerActions.MAVERICKV2,
                (FROM, address(fromToken()), 0, maverickV2Pool(), maverickV2TokenAIn(), 0)
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
        snapStartName("settler_maverickV2_custody");
        _settler.execute(allowedSlippage, actions, bytes32(0));
        snapEnd();
        vm.stopPrank();

        uint256 afterBalanceTo = toToken().balanceOf(FROM);
        assertGt(afterBalanceTo, beforeBalanceTo);
        uint256 afterBalanceFrom = fromToken().balanceOf(FROM);
        assertEq(afterBalanceFrom + amount(), beforeBalanceFrom);
    }

    function testMaverickV2VIP() public skipIf(maverickV2Salt() == bytes32(0)) setMaverickV2Block {
        (ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig) = _getDefaultFromPermit2();

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(
                ISettlerActions.MAVERICKV2_VIP, (FROM, maverickV2Salt(), maverickV2TokenAIn(), permit, sig, 0)
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
        snapStartName("settler_maverickV2_VIP");
        _settler.execute(allowedSlippage, actions, bytes32(0));
        snapEnd();
        vm.stopPrank();

        uint256 afterBalanceTo = toToken().balanceOf(FROM);
        assertGt(afterBalanceTo, beforeBalanceTo);
        uint256 afterBalanceFrom = fromToken().balanceOf(FROM);
        assertEq(afterBalanceFrom + amount(), beforeBalanceFrom);
    }

    function testMaverickV2VIPAllowanceHolder() public skipIf(maverickV2Salt() == bytes32(0)) setMaverickV2Block {
        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(fromToken()), amount(), 0 /* nonce */ );
        bytes memory sig = new bytes(0);

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(
                ISettlerActions.MAVERICKV2_VIP, (FROM, maverickV2Salt(), maverickV2TokenAIn(), permit, sig, 0)
            )
        );
        ISettlerBase.AllowedSlippage memory allowedSlippage = ISettlerBase.AllowedSlippage({
            recipient: payable(address(0)),
            buyToken: IERC20(address(0)),
            minAmountOut: 0
        });
        IAllowanceHolder _allowanceHolder = allowanceHolder;
        Settler _settler = settler;
        IERC20 _fromToken = fromToken();
        uint256 _amount = amount();
        bytes memory ahData = abi.encodeCall(_settler.execute, (allowedSlippage, actions, bytes32(0)));

        uint256 beforeBalanceFrom = balanceOf(fromToken(), FROM);
        uint256 beforeBalanceTo = balanceOf(toToken(), FROM);

        vm.startPrank(FROM, FROM);
        snapStartName("allowanceHolder_maverickV2_VIP");
        _allowanceHolder.exec(address(_settler), address(_fromToken), _amount, payable(address(_settler)), ahData);
        snapEnd();
        vm.stopPrank();

        uint256 afterBalanceTo = toToken().balanceOf(FROM);
        assertGt(afterBalanceTo, beforeBalanceTo);
        uint256 afterBalanceFrom = fromToken().balanceOf(FROM);
        assertEq(afterBalanceFrom + amount(), beforeBalanceFrom);
    }

    function testMaverickV2MetaTxn() public skipIf(maverickV2Salt() == bytes32(0)) setMaverickV2Block {
        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(fromToken()), amount(), PERMIT2_FROM_NONCE);

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(
                ISettlerActions.METATXN_MAVERICKV2_VIP, (FROM, maverickV2Salt(), maverickV2TokenAIn(), permit, 0)
            )
        );
        ISettlerBase.AllowedSlippage memory allowedSlippage = ISettlerBase.AllowedSlippage({
            recipient: payable(address(0)),
            buyToken: IERC20(address(0)),
            minAmountOut: 0 ether
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

        vm.startPrank(address(this), address(this));
        snapStartName("settler_metaTxn_maverickV2");
        _settlerMetaTxn.executeMetaTxn(allowedSlippage, actions, bytes32(0), FROM, sig);
        snapEnd();
        vm.stopPrank();

        uint256 afterBalanceTo = toToken().balanceOf(FROM);
        assertGt(afterBalanceTo, beforeBalanceTo);
        uint256 afterBalanceFrom = fromToken().balanceOf(FROM);
        assertEq(afterBalanceFrom + amount(), beforeBalanceFrom);
    }
}

import {Test} from "@forge-std/Test.sol";
import {IMaverickV2Pool, FastMaverickV2Pool} from "src/core/MaverickV2.sol";
import {console} from "@forge-std/console.sol";

contract MaverickV2TxnTest is Test {
    using FastMaverickV2Pool for IMaverickV2Pool;

    function setUp() public {
        vm.createSelectFork("mainnet");
    }

    function fromToken() internal pure returns (IERC20) {
        return IERC20(0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48);
    }

    function toToken() internal pure returns (IERC20) {
        return IERC20(0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2);
    }

    function salt() internal pure returns (bytes32) {
        uint64 feeAIn = 100000000000000;
        uint64 feeBIn = 100000000000000;
        uint16 tickSpacing = 2232;
        uint32 lookback = 3600;
        IERC20 tokenA = fromToken();
        IERC20 tokenB = toToken();
        uint8 kinds = 1;
        bytes32 salt = keccak256(abi.encode(feeAIn, feeBIn, tickSpacing, lookback, tokenA, tokenB, kinds, address(0)));
        return salt;
    }

    IMaverickV2Pool public pool;

    function maverickV2SwapCallback(IERC20 tokenIn, uint256 amountIn, uint256 amountOut , bytes calldata data) external {
        console.log("requested ", amountIn);
        tokenIn.transfer(msg.sender, amountIn);
    }

    function testMaverickV2Txn() public {
        pool =
            IMaverickV2Pool(AddressDerivation.deriveDeterministicContract(maverickV2Factory, salt(), maverickV2InitHash));

        deal(address(fromToken()), address(this), 1000000 ether);
        // fromToken().transfer(address(pool), 1000000 ether);

        int32 tick = pool.fastGetTick();

        (uint256 sellAmount, uint256 buyAmount) = pool.swap(address(this), IMaverickV2Pool.SwapParams({
            amount: 1000000 ether,
            tokenAIn: true,
            exactOutput: false,
            tickLimit: tick
        }), new bytes(10));

        console.log("set amount", uint256(1000000 ether));
        console.log("sellAmount", sellAmount);
        console.log("buyAmount ", buyAmount);

        int32 newTick = pool.fastGetTick();
        assertEq(newTick, tick, "TICK IS NOT THE SAME");
    }
}