// SPDX-License-Identifier: MIT
pragma solidity ^0.8.17;

import {Test} from "forge-std/Test.sol";
import {GasSnapshot} from "forge-gas-snapshot/GasSnapshot.sol";

import {ERC20} from "solmate/src/tokens/ERC20.sol";

import {Settler} from "../../src/Settler.sol";
import {Permit2} from "permit2/src/Permit2.sol";
import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";
import {Permit2Signature} from "../utils/Permit2Signature.sol";

import {IZeroEx} from "./vendor/IZeroEx.sol";
import {IUniswapV3Router} from "./vendor/IUniswapV3Router.sol";

abstract contract TokenPairTest is Test, GasSnapshot, Permit2Signature {
    uint256 FROM_PRIVATE_KEY = 0x1337;
    address FROM = vm.addr(FROM_PRIVATE_KEY);

    function testName() internal virtual returns (string memory);
    function fromToken() internal virtual returns (ERC20);
    function toToken() internal virtual returns (ERC20);
    function amount() internal virtual returns (uint256);
    function uniswapV3Path() internal virtual returns (bytes memory);

    // 0x Settler
    Settler SETTLER;
    Permit2 PERMIT2 = Permit2(0x000000000022D473030F116dDEE9F6B43aC78BA3);
    uint48 EXPIRATION = uint48(block.timestamp + 1000);
    uint48 constant NONCE = 0;

    // 0x V4
    IZeroEx ZERO_EX = IZeroEx(0xDef1C0ded9bec7F1a1670819833240f027b25EfF);

    function setUp() public {
        vm.createSelectFork(vm.envString("MAINNET_RPC_URL"));
        SETTLER = new Settler(
            address(PERMIT2), 
            0x1F98431c8aD98523631AE4a59f267346ea31F984, // UniV3 Factory
            0xe34f199b19b2b4f47f68442619d555527d244f78a3297ea89325f843f87b8b54 // UniV3 pool init code hash
        );
        deal(address(fromToken()), address(SETTLER), 1);
    }

    /*
            0x Settler
     */
    function testSettler_uniswapV3VIP() public {
        bytes memory actions = abi.encodePacked(
            bytes4(keccak256("UNISWAPV3_PERMIT2_SWAP_EXACT_IN")) // Uniswap Swap
        );

        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(fromToken()), uint160(amount()), NONCE);
        bytes memory sig =
            getPermitTransferSignature(permit, address(SETTLER), FROM_PRIVATE_KEY, PERMIT2.DOMAIN_SEPARATOR());

        bytes[] memory datas = new bytes[](1);
        datas[0] = abi.encode(FROM, amount(), 1, uniswapV3Path(), abi.encode(permit, sig));

        vm.startPrank(FROM);
        deal(address(fromToken()), FROM, amount());
        fromToken().approve(address(PERMIT2), type(uint256).max);

        snapStartName("settler_permit2_uniswapV3VIP");
        SETTLER.execute(actions, datas);
        snapEnd();
    }

    function testSettler_uniswapV3_multiplex2() public warmPermit2Nonce {
        bytes memory actions = abi.encodePacked(
            bytes4(keccak256("PERMIT2_TRANSFER_FROM")), // Permit 2
            bytes4(keccak256("UNISWAPV3_SWAP_EXACT_IN")), // Uniswap Swap
            bytes4(keccak256("UNISWAPV3_SWAP_EXACT_IN")) // Uniswap Swap
        );

        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(fromToken()), uint160(amount()), NONCE + 1);
        bytes memory sig =
            getPermitTransferSignature(permit, address(SETTLER), FROM_PRIVATE_KEY, PERMIT2.DOMAIN_SEPARATOR());

        bytes[] memory datas = new bytes[](3);
        datas[0] = abi.encode(permit, sig);
        datas[1] = abi.encode(FROM, amount() / 2, 1, uniswapV3Path());
        datas[2] = abi.encode(FROM, amount() / 2, 1, uniswapV3Path());

        vm.startPrank(FROM);
        deal(address(fromToken()), FROM, amount());
        fromToken().approve(address(PERMIT2), type(uint256).max);

        snapStartName("settler_warm_permit2_uniswapV3_multiplex2");
        SETTLER.execute(actions, datas);
        snapEnd();
    }

    function testSettler_uniswapV3VIP_warm() public warmPermit2Nonce {
        deal(address(fromToken()), FROM, amount());
        bytes memory actions = abi.encodePacked(
            bytes4(keccak256("UNISWAPV3_PERMIT2_SWAP_EXACT_IN")) // Uniswap Swap
        );

        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(fromToken()), uint160(amount()), NONCE + 1);
        bytes memory sig =
            getPermitTransferSignature(permit, address(SETTLER), FROM_PRIVATE_KEY, PERMIT2.DOMAIN_SEPARATOR());

        bytes[] memory datas = new bytes[](1);
        datas[0] = abi.encode(FROM, amount(), 1, uniswapV3Path(), abi.encode(permit, sig));

        deal(address(fromToken()), FROM, amount());
        vm.startPrank(FROM);

        snapStartName("settler_warm_permit2_uniswapV3VIP");
        SETTLER.execute(actions, datas);
        snapEnd();
    }

    function testSettler_permit_uniswapV3() public {
        bytes memory actions = abi.encodePacked(
            bytes4(keccak256("PERMIT2_TRANSFER_FROM")), // Permit 2
            bytes4(keccak256("UNISWAPV3_SWAP_EXACT_IN")) // Uniswap Swap
        );

        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(fromToken()), uint160(amount()), NONCE);
        bytes memory sig =
            getPermitTransferSignature(permit, address(SETTLER), FROM_PRIVATE_KEY, PERMIT2.DOMAIN_SEPARATOR());

        bytes[] memory datas = new bytes[](2);
        datas[0] = abi.encode(permit, sig);
        datas[1] = abi.encode(FROM, amount(), 1, uniswapV3Path());

        vm.startPrank(FROM);
        deal(address(fromToken()), FROM, amount());
        fromToken().approve(address(PERMIT2), type(uint256).max);

        snapStartName("settler_permit2_uniswapV3");
        SETTLER.execute(actions, datas);
        snapEnd();
    }

    /*
            0x V4
     */
    function testZeroEx_uniswapV3() public {
        vm.startPrank(FROM);
        deal(address(fromToken()), FROM, amount());
        fromToken().approve(address(ZERO_EX), type(uint256).max);
        snapStartName("zeroEx_uniswapV3");
        ZERO_EX.sellTokenForTokenToUniswapV3(uniswapV3Path(), amount(), 1, FROM);
        snapEnd();
    }

    function testZeroEx_multiplex1_uniswapV3() public {
        IZeroEx.BatchSellSubcall[] memory calls = new IZeroEx.BatchSellSubcall[](1);
        calls[0] = IZeroEx.BatchSellSubcall({
            id: IZeroEx.MultiplexSubcall.UniswapV3,
            sellAmount: amount(),
            data: uniswapV3Path()
        });

        vm.startPrank(FROM);
        deal(address(fromToken()), FROM, amount());
        fromToken().approve(address(ZERO_EX), type(uint256).max);

        snapStartName("zeroEx_multiplex1_uniswapV3");
        ZERO_EX.multiplexBatchSellTokenForToken(fromToken(), toToken(), calls, amount(), 1);
        snapEnd();
    }

    function testZeroEx_multiplex2_uniswapV3() public {
        IZeroEx.BatchSellSubcall[] memory calls = new IZeroEx.BatchSellSubcall[](2);
        calls[0] = IZeroEx.BatchSellSubcall({
            id: IZeroEx.MultiplexSubcall.UniswapV3,
            sellAmount: amount() / 2,
            data: uniswapV3Path()
        });
        calls[1] = IZeroEx.BatchSellSubcall({
            id: IZeroEx.MultiplexSubcall.UniswapV3,
            sellAmount: amount() / 2,
            data: uniswapV3Path()
        });

        vm.startPrank(FROM);
        deal(address(fromToken()), FROM, amount());
        fromToken().approve(address(ZERO_EX), type(uint256).max);

        snapStartName("zeroEx_multiplex2_uniswapV3");
        ZERO_EX.multiplexBatchSellTokenForToken(fromToken(), toToken(), calls, amount(), 1);
        snapEnd();
    }

    /*
            Uniswap V3 Router
     */
    function testUniswapRouter() public {
        IUniswapV3Router UNISWAP_ROUTER = IUniswapV3Router(0xE592427A0AEce92De3Edee1F18E0157C05861564);

        vm.startPrank(FROM);
        deal(address(fromToken()), FROM, amount());
        fromToken().approve(address(UNISWAP_ROUTER), type(uint256).max);

        snapStartName("uniswapRouter_uniswapV3");
        UNISWAP_ROUTER.exactInput(
            IUniswapV3Router.ExactInputParams({
                path: uniswapV3Path(),
                recipient: FROM,
                deadline: block.timestamp + 1,
                amountIn: amount(),
                amountOutMinimum: 1
            })
        );
        snapEnd();
    }

    function snapStartName(string memory name) internal {
        snapStart(string.concat(name, "_", testName()));
    }

    modifier warmPermit2Nonce() {
        deal(address(fromToken()), FROM, amount());
        vm.prank(FROM);
        fromToken().approve(address(PERMIT2), type(uint256).max);

        // Warm up by consuming the 0 nonce
        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(fromToken()), uint160(amount()), NONCE);
        bytes memory sig =
            getPermitTransferSignature(permit, address(SETTLER), FROM_PRIVATE_KEY, PERMIT2.DOMAIN_SEPARATOR());
        ISignatureTransfer.SignatureTransferDetails memory transferDetails =
            ISignatureTransfer.SignatureTransferDetails({to: address(this), requestedAmount: permit.permitted.amount});

        vm.prank(address(SETTLER));
        PERMIT2.permitTransferFrom(permit, transferDetails, FROM, sig);
        _;
    }
}
