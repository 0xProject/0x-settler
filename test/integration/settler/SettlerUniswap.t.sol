// SPDX-License-Identifier: MIT
pragma solidity ^0.8.17;

import {ERC20} from "solmate/src/tokens/ERC20.sol";
import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";

import {BasePairTest} from "./BasePairTest.t.sol";
import {ICurveV2Pool} from "./vendor/ICurveV2Pool.sol";
import {IZeroEx} from "./vendor/IZeroEx.sol";

import {SafeTransferLib} from "../../src/utils/SafeTransferLib.sol";
import {Settler} from "../../src/Settler.sol";

abstract contract SettlerUniswapPairTest is BasePairTest {
    using SafeTransferLib for ERC20;

    uint256 private PERMIT2_FROM_NONCE = 1;
    uint256 private PERMIT2_MAKER_NONCE = 1;

    Settler private settler;
    IZeroEx private ZERO_EX = IZeroEx(0xDef1C0ded9bec7F1a1670819833240f027b25EfF);

    // 0x V4 OTCOrder
    IZeroEx.OtcOrder private otcOrder;
    bytes32 private otcOrderHash;

    function setUp() public virtual override {
        super.setUp();
        settler = getSettler();
        safeApproveIfBelow(fromToken(), FROM, address(PERMIT2), amount());
        // Otc via ZeroEx
        safeApproveIfBelow(toToken(), MAKER, address(ZERO_EX), amount());
        // Otc inside of Settler
        safeApproveIfBelow(toToken(), MAKER, address(PERMIT2), amount());

        // First time inits for Settler
        // We set up allowances to contracts which are inited on the first trade for a fair comparison
        // e.g to a Curve Pool
        ICurveV2Pool.CurveV2PoolData memory poolData = getCurveV2PoolData();
        safeApproveIfBelow(fromToken(), address(settler), address(poolData.pool), amount());
        // ZeroEx for Settler using ZeroEx OTC
        safeApproveIfBelow(fromToken(), address(settler), address(ZERO_EX), amount());

        // Otc 0x v4 order
        otcOrder.makerToken = toToken();
        otcOrder.takerToken = fromToken();
        otcOrder.makerAmount = uint128(amount());
        otcOrder.takerAmount = uint128(amount());
        otcOrder.taker = address(0);
        otcOrder.txOrigin = FROM;
        otcOrder.expiryAndNonce = type(uint256).max;
        otcOrder.maker = MAKER;
        otcOrderHash = ZERO_EX.getOtcOrderHash(otcOrder);

        warmPermit2Nonce(FROM);
        warmPermit2Nonce(MAKER);
    }

    function uniswapV3Path() internal virtual returns (bytes memory);
    function getCurveV2PoolData() internal pure virtual returns (ICurveV2Pool.CurveV2PoolData memory);

    function getSettler() private returns (Settler settler) {
        settler = new Settler(
            address(PERMIT2), 
            address(ZERO_EX), // ZeroEx
            0x1F98431c8aD98523631AE4a59f267346ea31F984, // UniV3 Factory
            0xe34f199b19b2b4f47f68442619d555527d244f78a3297ea89325f843f87b8b54 // UniV3 pool init code hash
        );
    }

    function testSettler_zeroExOtcOrder() public {
        (uint8 v, bytes32 r, bytes32 s) = vm.sign(MAKER_PRIVATE_KEY, otcOrderHash);

        bytes memory actions = abi.encodePacked(
            bytes4(keccak256("PERMIT2_TRANSFER_FROM")), // Permit 2
            bytes4(keccak256("ZERO_EX_OTC")) // 0x OTC
        );

        bytes[] memory datas = new bytes[](2);
        datas[0] = _getDefaultPermit2DataEncoded();
        datas[1] = abi.encode(otcOrder, IZeroEx.Signature(IZeroEx.SignatureType.EIP712, v, r, s), amount());

        snapStartName("settler_zeroExOtc");
        vm.startPrank(FROM, FROM);
        settler.execute(actions, datas);
        snapEnd();
    }

    function testSettler_uniswapV3VIP() public {
        deal(address(fromToken()), FROM, amount());
        bytes memory actions = abi.encodePacked(
            bytes4(keccak256("UNISWAPV3_PERMIT2_SWAP_EXACT_IN")) // Uniswap Swap
        );

        bytes[] memory datas = new bytes[](1);
        datas[0] = abi.encode(FROM, amount(), 1, uniswapV3Path(), _getDefaultPermit2DataEncoded());

        snapStartName("settler_uniswapV3VIP");
        vm.startPrank(FROM);
        settler.execute(actions, datas);
        snapEnd();
    }

    function testSettler_uniswapV3_multiplex2() public {
        bytes memory actions = abi.encodePacked(
            bytes4(keccak256("PERMIT2_TRANSFER_FROM")), // Permit 2
            bytes4(keccak256("UNISWAPV3_SWAP_EXACT_IN")), // Uniswap Swap
            bytes4(keccak256("UNISWAPV3_SWAP_EXACT_IN")) // Uniswap Swap
        );

        bytes[] memory datas = new bytes[](3);
        datas[0] = _getDefaultPermit2DataEncoded();
        datas[1] = abi.encode(FROM, amount() / 2, 1, uniswapV3Path());
        datas[2] = abi.encode(FROM, amount() / 2, 1, uniswapV3Path());

        snapStartName("settler_uniswapV3_multiplex2");
        vm.startPrank(FROM);
        settler.execute(actions, datas);
        snapEnd();
    }

    function testSettler_uniswapV3() public {
        bytes memory actions = abi.encodePacked(
            bytes4(keccak256("PERMIT2_TRANSFER_FROM")), // Permit 2
            bytes4(keccak256("UNISWAPV3_SWAP_EXACT_IN")) // UniswapV3 Swap
        );

        bytes[] memory datas = new bytes[](2);
        datas[0] = _getDefaultPermit2DataEncoded();
        datas[1] = abi.encode(FROM, amount(), 1, uniswapV3Path());

        snapStartName("settler_uniswapV3");
        vm.startPrank(FROM);
        settler.execute(actions, datas);
        snapEnd();
    }

    function testSettler_uniswapV3_fee() public {
        bytes memory actions = abi.encodePacked(
            bytes4(keccak256("PERMIT2_TRANSFER_FROM")), // Permit 2
            bytes4(keccak256("UNISWAPV3_SWAP_EXACT_IN")), // UniswapV3 Swap
            bytes4(keccak256("TRANSFER_OUT")), // fee
            bytes4(keccak256("TRANSFER_OUT")) // payout
        );

        bytes[] memory datas = new bytes[](4);
        datas[0] = _getDefaultPermit2DataEncoded();
        datas[1] = abi.encode(address(settler), amount(), 1, uniswapV3Path()); // send to settler
        datas[2] = abi.encode(address(toToken()), BURN_ADDRESS, 1_000); // Fee
        datas[3] = abi.encode(address(toToken()), FROM, 10_000);

        snapStartName("settler_uniswapV3_fee");
        vm.startPrank(FROM);
        settler.execute(actions, datas);
        snapEnd();
    }

    function testSettler_curveV2VIP() public skipIf(getCurveV2PoolData().pool == address(0)) {
        ICurveV2Pool.CurveV2PoolData memory poolData = getCurveV2PoolData();

        bytes memory actions = abi.encodePacked(
            bytes4(keccak256("PERMIT2_TRANSFER_FROM")), // Permit 2
            bytes4(keccak256("CURVE_UINT256_EXCHANGE")), // Curve V2
            bytes4(keccak256("TRANSFER_OUT"))
        );

        bytes[] memory datas = new bytes[](3);
        datas[0] = _getDefaultPermit2DataEncoded();
        datas[1] =
            abi.encode(address(poolData.pool), fromToken(), poolData.fromTokenIndex, poolData.toTokenIndex, amount(), 1);
        datas[2] = abi.encode(address(toToken()), FROM, 10_000);

        snapStartName("settler_curveV2VIP");
        vm.startPrank(FROM);
        settler.execute(actions, datas);
        snapEnd();
    }

    function testSettler_curveV2_fee() public skipIf(getCurveV2PoolData().pool == address(0)) {
        ICurveV2Pool.CurveV2PoolData memory poolData = getCurveV2PoolData();

        bytes memory actions = abi.encodePacked(
            bytes4(keccak256("PERMIT2_TRANSFER_FROM")), // Permit 2
            bytes4(keccak256("CURVE_UINT256_EXCHANGE")), // Curve V2
            bytes4(keccak256("TRANSFER_OUT")), // Fee
            bytes4(keccak256("TRANSFER_OUT"))
        );

        bytes[] memory datas = new bytes[](4);
        datas[0] = _getDefaultPermit2DataEncoded();
        datas[1] =
            abi.encode(address(poolData.pool), fromToken(), poolData.fromTokenIndex, poolData.toTokenIndex, amount(), 1);
        datas[2] = abi.encode(address(toToken()), BURN_ADDRESS, 1_000); // Fee
        datas[3] = abi.encode(address(toToken()), FROM, 10_000);

        snapStartName("settler_curveV2_fee");
        vm.startPrank(FROM);
        settler.execute(actions, datas);
        snapEnd();
    }

    struct ActionData {
        bytes actions;
        bytes data;
    }

    bytes32 private constant FULL_PERMIT2_WITNESS_TYPEHASH = keccak256(
        "PermitWitnessTransferFrom(TokenPermissions permitted,address spender,uint256 nonce,uint256 deadline,ActionData actionData)ActionData(bytes actions,bytes data)TokenPermissions(address token,uint256 amount)"
    );

    function testSettler_metaTxn_uniswapV3() public {
        bytes memory actions = abi.encodePacked(
            bytes4(keccak256("PERMIT2_WITNESS_TRANSFER_FROM")), // Permit 2
            bytes4(keccak256("UNISWAPV3_SWAP_EXACT_IN")) // Uniswap Swap
        );

        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(fromToken()), uint160(amount()), PERMIT2_FROM_NONCE);

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

        snapStartName("settler_metaTxn_uniswapV3");
        // Submitted by third party
        settler.executeMetaTxn(actions, datas, sig);
        snapEnd();
    }

    bytes32 private constant OTC_PERMIT2_WITNESS_TYPEHASH = keccak256(
        "PermitWitnessTransferFrom(TokenPermissions permitted,address spender,uint256 nonce,uint256 deadline,OtcOrder order)OtcOrder(address makerToken,address takerToken,uint128 makerAmount,uint128 takerAmount,address maker,address taker,address txOrigin)TokenPermissions(address token,uint256 amount)"
    );

    struct OtcOrder {
        ERC20 makerToken;
        ERC20 takerToken;
        uint128 makerAmount;
        uint128 takerAmount;
        address maker;
        address taker;
        address txOrigin;
    }

    function testSettler_otc() public {
        ISignatureTransfer.PermitTransferFrom memory makerPermit =
            defaultERC20PermitTransfer(address(toToken()), uint160(amount()), PERMIT2_MAKER_NONCE);
        ISignatureTransfer.PermitTransferFrom memory takerPermit =
            defaultERC20PermitTransfer(address(fromToken()), uint160(amount()), PERMIT2_FROM_NONCE);

        OtcOrder memory order = OtcOrder({
            makerToken: toToken(),
            takerToken: fromToken(),
            makerAmount: uint128(amount()),
            takerAmount: uint128(amount()),
            maker: MAKER,
            taker: address(0),
            txOrigin: address(0)
        });
        bytes32 witness = keccak256(abi.encode(order));
        bytes memory makerSig = getPermitWitnessTransferSignature(
            makerPermit,
            address(settler),
            MAKER_PRIVATE_KEY,
            OTC_PERMIT2_WITNESS_TYPEHASH,
            witness,
            PERMIT2.DOMAIN_SEPARATOR()
        );

        bytes memory takerSig =
            getPermitTransferSignature(takerPermit, address(settler), FROM_PRIVATE_KEY, PERMIT2.DOMAIN_SEPARATOR());

        bytes memory actions = abi.encodePacked(
            bytes4(keccak256("SETTLER_OTC")) // Settler OTC
        );
        bytes[] memory datas = new bytes[](1);
        datas[0] = abi.encode(order, makerPermit, makerSig, takerPermit, takerSig, uint128(amount()));

        snapStartName("settler_otc");
        vm.startPrank(FROM);
        settler.execute(actions, datas);
        snapEnd();
    }

    function _getDefaultPermit2DataEncoded() private returns (bytes memory) {
        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(fromToken()), uint160(amount()), PERMIT2_FROM_NONCE);
        bytes memory sig =
            getPermitTransferSignature(permit, address(settler), FROM_PRIVATE_KEY, PERMIT2.DOMAIN_SEPARATOR());

        return abi.encode(permit, sig);
    }
}
