// SPDX-License-Identifier: MIT
pragma solidity ^0.8.17;

import {ERC20} from "solmate/src/tokens/ERC20.sol";
import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";

import {BasePairTest} from "./BasePairTest.t.sol";
import {ICurveV2Pool} from "./vendor/ICurveV2Pool.sol";

import {SafeTransferLib} from "../../src/utils/SafeTransferLib.sol";
import {Settler} from "../../src/Settler.sol";

abstract contract SettlerPairTest is BasePairTest {
    using SafeTransferLib for ERC20;

    function uniswapV3Path() internal virtual returns (bytes memory);
    function getCurveV2PoolData() internal pure virtual returns (ICurveV2Pool.CurveV2PoolData memory);

    function getSettler() private returns (Settler settler) {
        settler = new Settler(
            address(PERMIT2), 
            0x1F98431c8aD98523631AE4a59f267346ea31F984, // UniV3 Factory
            0xe34f199b19b2b4f47f68442619d555527d244f78a3297ea89325f843f87b8b54 // UniV3 pool init code hash
        );
    }

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

        dealAndApprove(fromToken(), amount(), address(PERMIT2));
        snapStartName("settler_uniswapV3VIP");
        vm.startPrank(FROM);
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

        dealAndApprove(fromToken(), amount(), address(PERMIT2));
        snapStartName("settler_uniswapV3VIP_warmNonce");
        vm.startPrank(FROM);
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

        dealAndApprove(fromToken(), amount(), address(PERMIT2));
        snapStartName("settler_uniswapV3_multiplex2_warmNonce");
        vm.startPrank(FROM);
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

        dealAndApprove(fromToken(), amount(), address(PERMIT2));
        snapStartName("settler_uniswapV3");
        vm.startPrank(FROM);
        settler.execute(actions, datas);
        snapEnd();
    }

    function testSettler_curveV2VIP() public skipIf(getCurveV2PoolData().pool == address(0)) warmPermit2Nonce {
        Settler settler = getSettler();
        ICurveV2Pool.CurveV2PoolData memory poolData = getCurveV2PoolData();

        // For a fair comparison pre-set the approval (set once on first trade) for the Curve pool
        safeApproveIfBelow(fromToken(), address(settler), address(poolData.pool), amount());

        bytes memory actions = abi.encodePacked(
            bytes4(keccak256("PERMIT2_TRANSFER_FROM")), // Permit 2
            bytes4(keccak256("CURVE_UINT256_EXCHANGE")), // Curve V2
            bytes4(keccak256("TRANSFER_OUT"))
        );

        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(fromToken()), uint160(amount()), 1);
        bytes memory sig =
            getPermitTransferSignature(permit, address(settler), FROM_PRIVATE_KEY, PERMIT2.DOMAIN_SEPARATOR());

        bytes[] memory datas = new bytes[](3);
        datas[0] = abi.encode(permit, sig);
        datas[1] =
            abi.encode(address(poolData.pool), fromToken(), poolData.fromTokenIndex, poolData.toTokenIndex, amount(), 1);
        datas[2] = abi.encode(address(fromToken()));

        dealAndApprove(fromToken(), amount(), address(PERMIT2));
        snapStartName("settler_curveV2VIP_warmNonce");
        vm.startPrank(FROM);
        settler.execute(actions, datas);
        snapEnd();
    }
}
