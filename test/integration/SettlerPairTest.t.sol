// SPDX-License-Identifier: MIT
pragma solidity ^0.8.17;

import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";
import {SafeTransferLib} from "solmate/src/utils/SafeTransferLib.sol";
import {ERC20} from "solmate/src/tokens/ERC20.sol";

import {BasePairTest} from "./BasePairTest.t.sol";

import {Settler} from "../../src/Settler.sol";

abstract contract SettlerPairTest is BasePairTest {
    using SafeTransferLib for ERC20;

    function uniswapV3Path() internal virtual returns (bytes memory);

    function testSettler_uniswapV3VIP() public {
        Settler settler = getSettler();
        bytes memory actions = abi.encodePacked(
            bytes4(keccak256("UNISWAPV3_PERMIT2_SWAP_EXACT_IN")) // Uniswap Swap
        );

        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(fromToken()), uint160(amount()), 0);
        bytes memory sig =
            getPermitTransferSignature(permit, address(settler), FROM_PRIVATE_KEY, PERMIT2.DOMAIN_SEPARATOR());

        bytes[] memory datas = new bytes[](1);
        datas[0] = abi.encode(FROM, amount(), 1, uniswapV3Path(), abi.encode(permit, sig));

        vm.startPrank(FROM);
        deal(address(fromToken()), FROM, amount());
        fromToken().safeApprove(address(PERMIT2), type(uint256).max);

        snapStartName("settler_uniswapV3VIP");
        settler.execute(actions, datas);
        snapEnd();
    }

    function testSettler_uniswapV3VIP_warm() public warmPermit2Nonce {
        Settler settler = getSettler();
        deal(address(fromToken()), FROM, amount());
        bytes memory actions = abi.encodePacked(
            bytes4(keccak256("UNISWAPV3_PERMIT2_SWAP_EXACT_IN")) // Uniswap Swap
        );

        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(fromToken()), uint160(amount()), 1);
        bytes memory sig =
            getPermitTransferSignature(permit, address(settler), FROM_PRIVATE_KEY, PERMIT2.DOMAIN_SEPARATOR());

        bytes[] memory datas = new bytes[](1);
        datas[0] = abi.encode(FROM, amount(), 1, uniswapV3Path(), abi.encode(permit, sig));

        deal(address(fromToken()), FROM, amount());
        vm.startPrank(FROM);

        snapStartName("settler_uniswapV3VIP_warmNonce");
        settler.execute(actions, datas);
        snapEnd();
    }

    function testSettler_uniswapV3_multiplex2() public warmPermit2Nonce {
        Settler settler = getSettler();
        bytes memory actions = abi.encodePacked(
            bytes4(keccak256("PERMIT2_TRANSFER_FROM")), // Permit 2
            bytes4(keccak256("UNISWAPV3_SWAP_EXACT_IN")), // Uniswap Swap
            bytes4(keccak256("UNISWAPV3_SWAP_EXACT_IN")) // Uniswap Swap
        );

        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(fromToken()), uint160(amount()), 1);
        bytes memory sig =
            getPermitTransferSignature(permit, address(settler), FROM_PRIVATE_KEY, PERMIT2.DOMAIN_SEPARATOR());

        bytes[] memory datas = new bytes[](3);
        datas[0] = abi.encode(permit, sig);
        datas[1] = abi.encode(FROM, amount() / 2, 1, uniswapV3Path());
        datas[2] = abi.encode(FROM, amount() / 2, 1, uniswapV3Path());

        vm.startPrank(FROM);
        deal(address(fromToken()), FROM, amount());
        fromToken().safeApprove(address(PERMIT2), type(uint256).max);

        snapStartName("settler_uniswapV3_multiplex2_warmNonce");
        settler.execute(actions, datas);
        snapEnd();
    }

    function testSettler_uniswapV3() public {
        Settler settler = getSettler();
        bytes memory actions = abi.encodePacked(
            bytes4(keccak256("PERMIT2_TRANSFER_FROM")), // Permit 2
            bytes4(keccak256("UNISWAPV3_SWAP_EXACT_IN")) // Uniswap Swap
        );

        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(fromToken()), uint160(amount()), 0);
        bytes memory sig =
            getPermitTransferSignature(permit, address(settler), FROM_PRIVATE_KEY, PERMIT2.DOMAIN_SEPARATOR());

        bytes[] memory datas = new bytes[](2);
        datas[0] = abi.encode(permit, sig);
        datas[1] = abi.encode(FROM, amount(), 1, uniswapV3Path());

        vm.startPrank(FROM);
        deal(address(fromToken()), FROM, amount());
        fromToken().safeApprove(address(PERMIT2), type(uint256).max);

        snapStartName("settler_uniswapV3");
        settler.execute(actions, datas);
        snapEnd();
    }

    function getSettler() private returns (Settler settler) {
        settler = new Settler(
            address(PERMIT2), 
            0x1F98431c8aD98523631AE4a59f267346ea31F984, // UniV3 Factory
            0xe34f199b19b2b4f47f68442619d555527d244f78a3297ea89325f843f87b8b54 // UniV3 pool init code hash
        );
    }
}
