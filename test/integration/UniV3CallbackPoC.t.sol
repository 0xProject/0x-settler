// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {AllowanceHolder} from "src/allowanceholder/AllowanceHolderOld.sol";
import {IAllowanceHolder} from "src/allowanceholder/IAllowanceHolder.sol";
import {MainnetSettler as Settler} from "src/chains/Mainnet/TakerSubmitted.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {IUniswapV3Pool} from "src/core/UniswapV3Fork.sol";
import {AddressDerivation} from "src/utils/AddressDerivation.sol";

import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";
import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {uniswapV3MainnetFactory} from "src/core/univ3forks/UniswapV3.sol";

import {Utils} from "../unit/Utils.sol";
import {Permit2Signature} from "../utils/Permit2Signature.sol";
import {ActionDataBuilder} from "../utils/ActionDataBuilder.sol";

import {MockERC20} from "@solmate/test/utils/mocks/MockERC20.sol";

import {MainnetDefaultFork} from "./BaseForkTest.t.sol";

contract UniswapV3PoolDummy {
    bytes public RETURN_DATA;

    MockERC20 token0;
    MockERC20 token1;
    int256 amount0;
    int256 amount1;

    function setSwapData(MockERC20 token0_, MockERC20 token1_, int256 amount0_, int256 amount1_) public {
        token0 = token0_;
        token1 = token1_;
        amount0 = amount0_;
        amount1 = amount1_;
    }

    fallback(bytes calldata) external returns (bytes memory) {
        (address recipient,,,, bytes memory data) = abi.decode(msg.data[4:], (address, bool, int256, uint160, bytes));
        (bool ok,) = msg.sender.call(
            abi.encodeWithSignature("uniswapV3SwapCallback(int256,int256,bytes)", amount0, amount1, data)
        );
        require(ok, "UniV3Callback failure");
        if (amount0 > 0) token0.transfer(recipient, uint256(amount0));
        if (amount1 > 0) token1.transfer(recipient, uint256(amount1));
        return abi.encode(-amount0, -amount1);
    }
}

contract Shim {
    // forgefmt: disable-next-line
    function chainId() external returns (uint256) { // this is non-view (mutable) on purpose
        return block.chainid;
    }
}

contract UniV3CallbackPoC is Utils, Permit2Signature, MainnetDefaultFork {
    address internal constant ETH = 0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE;

    ISignatureTransfer permit2 = ISignatureTransfer(0x000000000022D473030F116dDEE9F6B43aC78BA3);
    bytes32 internal permit2Domain;

    IAllowanceHolder ah;
    Settler settler;
    address pool;

    address dai;
    address token;
    address payable alice;
    uint256 alicePk;
    address payable bob;
    uint256 bobPk;

    function setUp() public {
        vm.createSelectFork(_testChainId(), _testBlockNumber());
        vm.setEvmVersion("osaka");

        address alice_;
        (alice_, alicePk) = makeAddrAndKey("Alice");
        alice = payable(alice_);
        address bob_;
        (bob_, bobPk) = makeAddrAndKey("Bob");
        bob = payable(bob_);

        // Deploy dummy tokens
        dai = address(new MockERC20("DAI", "DAI", 18));
        token = address(new MockERC20("TKN", "TKN", 18));

        vm.label(dai, "DAI");
        vm.label(token, "TKN");

        permit2Domain = permit2.DOMAIN_SEPARATOR();

        // Deploy AllowanceHolder
        ah = IAllowanceHolder(0x0000000000001fF3684f28c67538d4D072C22734);
        {
            uint256 forkChainId = (new Shim()).chainId();
            vm.chainId(31337);
            vm.etch(address(ah), address(new AllowanceHolder()).code);
            vm.chainId(forkChainId);
        }

        // Deploy Settler.
        {
            uint256 forkChainId = (new Shim()).chainId();
            vm.chainId(31337);
            settler = new Settler(bytes20(0));
            vm.chainId(forkChainId);
        }

        // Deploy dummy pool.
        pool = _toPool(token, 500, dai);
        vm.etch(pool, type(UniswapV3PoolDummy).runtimeCode);

        // Give pool some tokens.
        MockERC20(dai).mint(pool, 100 ether);
        MockERC20(token).mint(pool, 100 ether);
    }

    function _toPool(address inputToken, uint24 fee, address outputToken) private view returns (address) {
        (address token0, address token1) =
            inputToken < outputToken ? (inputToken, outputToken) : (outputToken, inputToken);
        bytes32 salt;
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            mstore(0x00, token0)
            mstore(0x20, token1)
            mstore(0x40, fee)
            salt := keccak256(0x00, 0x60)
            mstore(0x40, ptr)
        }
        return AddressDerivation.deriveDeterministicContract(
            uniswapV3MainnetFactory, salt, 0xe34f199b19b2b4f47f68442619d555527d244f78a3297ea89325f843f87b8b54
        );
    }

    bytes32 private constant ACTIONS_AND_SLIPPAGE_TYPEHASH =
        keccak256("ActionsAndSlippage(address buyToken,address recipient,uint256 minAmountOut,bytes[] actions)");
    bytes32 private constant FULL_PERMIT2_WITNESS_TYPEHASH = keccak256(
        "PermitWitnessTransferFrom(TokenPermissions permitted,address spender,uint256 nonce,uint256 deadline,ActionsAndSlippage actionsAndSlippage)ActionsAndSlippage(address buyToken,address recipient,uint256 minAmountOut,bytes[] actions)TokenPermissions(address token,uint256 amount)"
    );

    function sqrtPriceLimitX96(IERC20 sellToken, IERC20 buyToken) internal view virtual returns (uint160) {
        bool zeroForOne = (sellToken == IERC20(ETH)) || ((buyToken != IERC20(ETH)) && (sellToken < buyToken));
        return zeroForOne ? 4295128740 : 1461446703485210103287273052203988822378723970341;
    }

    function testUniswapV3MetaTxFrontRun() public {
        MockERC20(dai).mint(alice, 100e18);

        vm.prank(alice);
        MockERC20(dai).approve(address(ah), type(uint256).max);
        vm.prank(alice);
        MockERC20(dai).approve(address(permit2), type(uint256).max);

        // Alice sets up the permit and transfer details.
        address operator = address(settler);
        uint256 amount = 777;

        ISignatureTransfer.PermitTransferFrom memory permit = defaultERC20PermitTransfer(dai, amount, 1);

        ISignatureTransfer.SignatureTransferDetails[] memory transferDetails =
            new ISignatureTransfer.SignatureTransferDetails[](1);
        transferDetails[0] = ISignatureTransfer.SignatureTransferDetails({to: operator, requestedAmount: amount});

        // Set UniswapV3 swap path.
        uint24 fee = 500;
        bytes memory uniswapV3Path = abi.encodePacked(dai, uint8(0), fee, sqrtPriceLimitX96(IERC20(dai), IERC20(token)), token);

        // Set up actions.
        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(
                ISettlerActions.METATXN_UNISWAPV3_VIP,
                (
                    address(settler), // recipient
                    permit,
                    uniswapV3Path, // (token0, fee, token1)
                    100 // amountOutMin
                )
            )
        );

        uint256 poolAmountOut = 5555;

        // Hash actions and sign.
        bytes32[] memory actionHashes = new bytes32[](1);
        actionHashes[0] = keccak256(actions[0]);

        Settler.AllowedSlippage memory slippage;

        slippage.recipient = alice;
        slippage.buyToken = IERC20(token);
        slippage.minAmountOut = poolAmountOut;

        bytes32 actionsHash = keccak256(abi.encodePacked(actionHashes));
        bytes32 witness = keccak256(abi.encode(ACTIONS_AND_SLIPPAGE_TYPEHASH, slippage, actionsHash));
        bytes memory sig = getPermitWitnessTransferSignature(
            permit, address(settler), alicePk, FULL_PERMIT2_WITNESS_TYPEHASH, witness, permit2Domain
        );

        // Set UniswapV3Pair dummy swap and return data.
        UniswapV3PoolDummy(pool).setSwapData(
            MockERC20(dai),
            MockERC20(token),
            int256(0), // amount0
            int256(poolAmountOut) // amount1 out of pool
        );

        // This would be Alice's normal flow.
        // This execution is front-run.

        // Settler(payable(address(settler))).executeMetaTxn(actions, slippage, bytes32(0), alice, sig);
        // return;

        // Bob front-runs the execution.

        bytes memory uniswapV3CallbackData = abi.encodePacked(
            uniswapV3Path,
            alice, // payer. This can be arbitrarily set!
            abi.encode(
                permit, // Bob uses Alice's permit.
                witness, // Re-use witness for Alice's actions
                false // isForwarded == false: pay with permit2
            ),
            sig
        );
        bytes memory poolCalldata = abi.encodeCall(
            IUniswapV3Pool.swap,
            (
                address(settler), // recipient
                false, // unused
                0, // unused
                0, // unused
                uniswapV3CallbackData
            )
        );
        actions = ActionDataBuilder.build(
            abi.encodeCall(
                ISettlerActions.BASIC,
                (
                    address(0), // sellToken
                    10_000, // proportion
                    pool, // pool
                    0, // offset
                    poolCalldata
                )
            )
        );

        // Bob is able to front-run the transaction
        // and take Alice's funds authorized via permit2.
        vm.startPrank(bob);
        slippage.recipient = bob;
        slippage.buyToken = IERC20(token);

        vm.expectRevert("UniV3Callback failure");
        settler.execute(slippage, actions, bytes32(0));
    }
}
