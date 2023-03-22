// SPDX-License-Identifier: MIT
pragma solidity ^0.8.17;

import {ERC20} from "solmate/src/tokens/ERC20.sol";
import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";

import {BasePairTest} from "./BasePairTest.t.sol";
import {ICurveV2Pool} from "./vendor/ICurveV2Pool.sol";
import {IZeroEx} from "./vendor/IZeroEx.sol";

import {SafeTransferLib} from "../../src/utils/SafeTransferLib.sol";
import {Settler} from "../../src/Settler.sol";

abstract contract SettlerPairTest is BasePairTest {
    using SafeTransferLib for ERC20;

    function uniswapV3Path() internal virtual returns (bytes memory);
    function getCurveV2PoolData() internal pure virtual returns (ICurveV2Pool.CurveV2PoolData memory);

    IZeroEx private ZERO_EX = IZeroEx(0xDef1C0ded9bec7F1a1670819833240f027b25EfF);

    function getSettler() private returns (Settler settler) {
        settler = new Settler(
            address(PERMIT2), 
            address(ZERO_EX), // ZeroEx
            0x1F98431c8aD98523631AE4a59f267346ea31F984, // UniV3 Factory
            0xe34f199b19b2b4f47f68442619d555527d244f78a3297ea89325f843f87b8b54 // UniV3 pool init code hash
        );
    }

    function testSettler_zeroExOtcOrder() public warmPermit2Nonce {
        dealAndApprove(fromToken(), amount(), address(ZERO_EX));
        dealAndApprove(MAKER, toToken(), amount(), address(ZERO_EX));

        IZeroEx.OtcOrder memory order;
        order.makerToken = toToken();
        order.takerToken = fromToken();
        order.makerAmount = uint128(amount());
        order.takerAmount = uint128(amount());
        order.taker = address(0);
        order.txOrigin = FROM;
        order.expiryAndNonce = type(uint256).max;
        order.maker = MAKER;
        (uint8 v, bytes32 r, bytes32 s) = vm.sign(MAKER_PRIVATE_KEY, ZERO_EX.getOtcOrderHash(order));

        Settler settler = getSettler();
        bytes memory actions = abi.encodePacked(
            bytes4(keccak256("PERMIT2_TRANSFER_FROM")), // Permit 2
            bytes4(keccak256("ZERO_EX_OTC")) // 0x OTC
        );

        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(fromToken()), uint160(amount()), 1);
        bytes memory sig =
            getPermitTransferSignature(permit, address(settler), FROM_PRIVATE_KEY, PERMIT2.DOMAIN_SEPARATOR());

        bytes[] memory datas = new bytes[](2);
        datas[0] = abi.encode(permit, sig);
        datas[1] = abi.encode(order, IZeroEx.Signature(IZeroEx.SignatureType.EIP712, v, r, s), amount());

        dealAndApprove(fromToken(), amount(), address(PERMIT2));
        snapStartName("settler_zeroExOtc");
        vm.startPrank(FROM, FROM);
        settler.execute(actions, datas);
        snapEnd();
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

    struct ActionData {
        bytes actions;
        bytes data;
    }

    bytes32 constant FULL_PERMIT2_WITNESS_TYPEHASH = keccak256(
        "PermitWitnessTransferFrom(TokenPermissions permitted,address spender,uint256 nonce,uint256 deadline,ActionData actionData)ActionData(bytes actions,bytes data)TokenPermissions(address token,uint256 amount)"
    );
    string constant WITNESS_TYPE_STRING =
        "ActionData actionData)ActionData(bytes actions,bytes data)TokenPermissions(address token,uint256 amount)";

    function testSettler_metaTxn() public warmPermit2Nonce {
        Settler settler = getSettler();
        bytes memory actions = abi.encodePacked(
            bytes4(keccak256("PERMIT2_WITNESS_TRANSFER_FROM")), // Permit 2
            bytes4(keccak256("UNISWAPV3_SWAP_EXACT_IN")) // Uniswap Swap
        );

        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(fromToken()), uint160(amount()), 1);

        bytes[] memory datas = new bytes[](2);
        datas[0] = abi.encode(permit, FROM);
        datas[1] = abi.encode(FROM, amount(), 1, uniswapV3Path());

        ActionData memory actionData = ActionData(actions, abi.encode(datas));
        bytes32 witness = keccak256(abi.encode(actionData));
        bytes memory sig = getPermitWitnessTransferSignature(
            permit,
            address(settler),
            FROM_PRIVATE_KEY,
            FULL_PERMIT2_WITNESS_TYPEHASH,
            witness,
            PERMIT2.DOMAIN_SEPARATOR()
        );

        dealAndApprove(fromToken(), amount(), address(PERMIT2));
        snapStartName("settler_metaTxn_uniswapV3");
        // Submitted by third party
        settler.executeMetaTxn(actions, datas, sig);
        snapEnd();
    }
}
