// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";
import {ISettlerTakerSubmitted} from "src/interfaces/ISettlerTakerSubmitted.sol";

import {
    Address,
    MakerTraits,
    Order,
    Swap,
    LIMIT_ORDER_PROTOCOL,
    LimitOrderFeeCollector
} from "src/LimitOrderFeeCollector.sol";

import {Test} from "@forge-std/Test.sol";

IERC20 constant WETH = IERC20(0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2);
IERC20 constant ETH = IERC20(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE);
IERC20 constant USDC = IERC20(0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48);
IERC20 constant USDT = IERC20(0xdAC17F958D2ee523a2206206994597C13D831ec7);

type TakerTraits is uint256;

interface ILimitOrderProtocol {
    function fillOrderArgs(
        Order calldata order,
        bytes32 r,
        bytes32 vs,
        uint256 amount,
        TakerTraits takerTraits,
        bytes calldata args
    ) external payable returns (uint256 makingAmount, uint256 takingAmount, bytes32 orderHash);

    function fillContractOrderArgs(
        Order calldata order,
        bytes calldata signature,
        uint256 amount,
        TakerTraits takerTraits,
        bytes calldata args
    ) external returns (uint256 makingAmount, uint256 takingAmount, bytes32 orderHash);
}

contract StupidERC1271 {
    function isValidSignature(bytes32 hash, bytes calldata signature) external view returns (bytes4) {
        (bytes32 r, bytes32 vs) = abi.decode(signature, (bytes32, bytes32));
        bytes32 s = vs & 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff;
        uint8 v = uint8(uint256(vs >> 255)) + 27;
        require(ecrecover(hash, v, r, s) == address(this));
        return this.isValidSignature.selector;
    }

    receive() external payable {}
}

contract LimitOrderFeeCollectorTest is Test {
    address private constant _TOEHOLD1 = 0x914d7Fec6aaC8cd542e72Bca78B30650d45643d7;

    uint256 internal MAKER_KEY;
    address payable internal MAKER;

    LimitOrderFeeCollector internal feeCollector;

    bytes32 internal constant LIMIT_ORDER_PROTOCOL_DOMAIN = keccak256(
        abi.encode(
            keccak256("EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)"),
            keccak256("1inch Aggregation Router"),
            keccak256("6"),
            uint256(1),
            LIMIT_ORDER_PROTOCOL
        )
    );
    bytes32 internal constant LIMIT_ORDER_TYPEHASH = keccak256(
        "Order(uint256 salt,address maker,address receiver,address makerAsset,address takerAsset,uint256 makingAmount,uint256 takingAmount,uint256 makerTraits)"
    );
    ILimitOrderProtocol internal constant LIMIT_ORDER_PROTOCOL_ = ILimitOrderProtocol(LIMIT_ORDER_PROTOCOL);

    uint256 internal constant makingAmount = 20_000 * 1e6;
    uint256 internal constant takingAmount = 10 * 1e18;
    uint16 internal constant feeBps = 2_500;

    address internal constant owner = 0x8E5DE7118a596E99B0563D3022039c11927f4827;
    ISettlerTakerSubmitted internal constant settler =
        ISettlerTakerSubmitted(0x0d0E364aa7852291883C162B22D6D81f6355428F);

    function setUp() public {
        vm.createSelectFork(vm.envString("MAINNET_RPC_URL"), 22282373);

        MAKER_KEY = uint256(keccak256("MAKER"));
        MAKER = payable(vm.addr(MAKER_KEY));
        deal(address(USDC), MAKER, makingAmount * 100);
        vm.prank(MAKER);
        require(USDC.approve(LIMIT_ORDER_PROTOCOL, type(uint256).max));

        deal(address(WETH), address(this), takingAmount * 100);
        require(WETH.approve(LIMIT_ORDER_PROTOCOL, type(uint256).max));

        (bool success, bytes memory returndata) = _TOEHOLD1.call(
            bytes.concat(
                bytes32(0),
                type(LimitOrderFeeCollector).creationCode,
                abi.encode(bytes20(keccak256("git commit")), address(this), WETH)
            )
        );
        require(success);
        require(returndata.length == 20);
        feeCollector = LimitOrderFeeCollector(payable(address(uint160(bytes20(returndata)))));
    }

    function testAcceptOwnership() public {
        vm.prank(owner);
        feeCollector.acceptOwnership();
        assertEq(feeCollector.owner(), owner);
    }

    function testSetFeeCollector() public {
        testAcceptOwnership();

        vm.prank(owner);
        feeCollector.setFeeCollector(address(0xdead));

        assertEq(feeCollector.feeCollector(), address(0xdead));
    }

    function _extension() internal view returns (bytes memory extension, uint160 extensionHash) {
        extension =
            bytes.concat(bytes4(uint32(22)), bytes28(0), bytes20(uint160(address(feeCollector))), bytes2(feeBps));
        extensionHash = uint160(uint256(keccak256(extension)));
    }

    function _order(uint160 extensionHash, bool unwrap) internal view returns (Order memory order) {
        uint256 unwrapFlag = (unwrap ? uint256(1) : uint256(0)) << 247;
        order.salt = extensionHash;
        order.maker = Address.wrap(uint256(uint160(address(MAKER))));
        order.receiver = Address.wrap(uint256(uint160(address(feeCollector))));
        order.makerAsset = Address.wrap(uint256(uint160(address(USDC))));
        order.takerAsset = Address.wrap(uint256(uint160(address(WETH))));
        order.makingAmount = makingAmount;
        order.takingAmount = takingAmount;
        order.makerTraits = MakerTraits.wrap((1 << 251) | (1 << 249) | unwrapFlag);
    }

    function _sign(Order memory order) internal view returns (bytes32 r, bytes32 vs) {
        bytes32 structHash = keccak256(bytes.concat(LIMIT_ORDER_TYPEHASH, abi.encode(order)));
        bytes32 signingHash = keccak256(bytes.concat(bytes2(0x1901), LIMIT_ORDER_PROTOCOL_DOMAIN, structHash));
        (r, vs) = vm.signCompact(MAKER_KEY, signingHash);
    }

    function _takerTraits(bytes memory extension) internal pure returns (TakerTraits) {
        return TakerTraits.wrap(extension.length << 224);
    }

    function testEOAUnwrap() public {
        (bytes memory extension, uint160 extensionHash) = _extension();
        Order memory order = _order(extensionHash, true);
        (bytes32 r, bytes32 vs) = _sign(order);

        TakerTraits takerTraits = _takerTraits(extension);

        vm.expectEmit(address(USDC));
        emit IERC20.Transfer(MAKER, address(this), makingAmount);
        vm.expectEmit(address(WETH));
        emit IERC20.Transfer(address(this), LIMIT_ORDER_PROTOCOL, takingAmount);

        LIMIT_ORDER_PROTOCOL_.fillOrderArgs(order, r, vs, takingAmount, takerTraits, extension);

        assertEq(MAKER.balance, takingAmount * (10_000 - feeBps) / 10_000);
        assertEq(USDC.balanceOf(address(this)), makingAmount);
    }

    function testEOANoWrap() public {
        (bytes memory extension, uint160 extensionHash) = _extension();
        Order memory order = _order(extensionHash, false);
        (bytes32 r, bytes32 vs) = _sign(order);

        TakerTraits takerTraits = _takerTraits(extension);

        vm.expectEmit(address(USDC));
        emit IERC20.Transfer(MAKER, address(this), makingAmount);
        vm.expectEmit(address(WETH));
        emit IERC20.Transfer(address(this), address(feeCollector), takingAmount);
        uint256 fee = takingAmount * feeBps / 10_000;
        uint256 takingAmountAfterFee = takingAmount - fee;
        emit IERC20.Transfer(address(feeCollector), MAKER, takingAmountAfterFee);

        LIMIT_ORDER_PROTOCOL_.fillOrderArgs(order, r, vs, takingAmount, takerTraits, extension);

        assertEq(WETH.balanceOf(MAKER), takingAmountAfterFee);
        assertEq(WETH.balanceOf(address(feeCollector)), fee);
        assertEq(USDC.balanceOf(address(this)), makingAmount);
    }

    function testContractUnwrap() public {
        (bytes memory extension, uint160 extensionHash) = _extension();
        Order memory order = _order(extensionHash, true);
        (bytes32 r, bytes32 vs) = _sign(order);

        TakerTraits takerTraits = _takerTraits(extension);

        vm.expectEmit(address(USDC));
        emit IERC20.Transfer(MAKER, address(this), makingAmount);
        vm.expectEmit(address(WETH));
        emit IERC20.Transfer(address(this), LIMIT_ORDER_PROTOCOL, takingAmount);

        vm.etch(MAKER, type(StupidERC1271).runtimeCode);
        LIMIT_ORDER_PROTOCOL_.fillContractOrderArgs(order, abi.encode(r, vs), takingAmount, takerTraits, extension);

        assertEq(MAKER.balance, takingAmount * (10_000 - feeBps) / 10_000);
        assertEq(USDC.balanceOf(address(this)), makingAmount);
    }

    function testContractNoWrap() public {
        (bytes memory extension, uint160 extensionHash) = _extension();
        Order memory order = _order(extensionHash, false);
        (bytes32 r, bytes32 vs) = _sign(order);

        TakerTraits takerTraits = _takerTraits(extension);

        vm.expectEmit(address(USDC));
        emit IERC20.Transfer(MAKER, address(this), makingAmount);
        vm.expectEmit(address(WETH));
        emit IERC20.Transfer(address(this), address(feeCollector), takingAmount);
        uint256 fee = takingAmount * feeBps / 10_000;
        uint256 takingAmountAfterFee = takingAmount - fee;
        emit IERC20.Transfer(address(feeCollector), MAKER, takingAmountAfterFee);

        vm.etch(MAKER, type(StupidERC1271).runtimeCode);
        LIMIT_ORDER_PROTOCOL_.fillContractOrderArgs(order, abi.encode(r, vs), takingAmount, takerTraits, extension);

        assertEq(WETH.balanceOf(MAKER), takingAmountAfterFee);
        assertEq(WETH.balanceOf(address(feeCollector)), fee);
        assertEq(USDC.balanceOf(address(this)), makingAmount);
    }

    function testSwap() public {
        deal(address(WETH), address(feeCollector), takingAmount);

        bytes[] memory actionsOriginal = new bytes[](1);
        actionsOriginal[0] = abi.encodeCall(
            ISettlerActions.UNISWAPV3_VIP,
            (
                address(settler),
                abi.encodePacked(WETH, uint8(0), uint24(500), USDC),
                ISignatureTransfer.PermitTransferFrom({
                    permitted: ISignatureTransfer.TokenPermissions({token: address(WETH), amount: type(uint256).max}),
                    nonce: 0,
                    deadline: block.timestamp + 5 minutes
                }),
                "",
                0
            )
        );

        bytes memory actions = abi.encode(actionsOriginal);
        assembly ("memory-safe") {
            let len := mload(actions)
            actions := add(0x20, actions)
            mstore(actions, sub(len, 0x20))
        }

        ISettlerBase.AllowedSlippage memory slippage =
            ISettlerBase.AllowedSlippage({recipient: payable(address(this)), buyToken: USDC, minAmountOut: 1 wei});

        vm.expectEmit(false, true, true, false, address(USDC));
        emit IERC20.Transfer(0xFFfFfFffFFfffFFfFFfFFFFFffFFFffffFfFFFfF, address(this), type(uint256).max);

        feeCollector.swap(settler, WETH, slippage, actions, bytes32(0));

        assertGt(USDC.balanceOf(address(this)), 0);
    }

    function testSwapFromEth() public {
        vm.deal(address(feeCollector), takingAmount);

        bytes[] memory actionsOriginal = new bytes[](2);
        actionsOriginal[0] = abi.encodeCall(
            ISettlerActions.BASIC,
            (
                address(ETH),
                10_000,
                address(WETH),
                0x04,
                bytes.concat(abi.encodeWithSignature("deposit()", 0 wei), bytes32(0))
            )
        );
        actionsOriginal[1] = abi.encodeCall(
            ISettlerActions.UNISWAPV3,
            (address(settler), 10_000, abi.encodePacked(WETH, uint8(0), uint24(500), USDC), 0)
        );

        bytes memory actions = abi.encode(actionsOriginal);
        assembly ("memory-safe") {
            let len := mload(actions)
            actions := add(0x20, actions)
            mstore(actions, sub(len, 0x20))
        }

        ISettlerBase.AllowedSlippage memory slippage =
            ISettlerBase.AllowedSlippage({recipient: payable(address(this)), buyToken: USDC, minAmountOut: 1 wei});

        vm.expectEmit(false, true, true, false, address(USDC));
        emit IERC20.Transfer(0xFFfFfFffFFfffFFfFFfFFFFFffFFFffffFfFFFfF, address(this), type(uint256).max);

        feeCollector.swap(settler, ETH, slippage, actions, bytes32(0));

        assertGt(USDC.balanceOf(address(this)), 0);
        assertEq(address(feeCollector).balance, 0);
    }

    function testSwapToEth() public {
        deal(address(USDC), address(feeCollector), makingAmount);

        bytes[] memory actionsOriginal = new bytes[](2);
        actionsOriginal[0] = abi.encodeCall(
            ISettlerActions.UNISWAPV3_VIP,
            (
                address(settler),
                abi.encodePacked(USDC, uint8(0), uint24(500), WETH),
                ISignatureTransfer.PermitTransferFrom({
                    permitted: ISignatureTransfer.TokenPermissions({token: address(USDC), amount: type(uint256).max}),
                    nonce: 0,
                    deadline: block.timestamp + 5 minutes
                }),
                "",
                0
            )
        );
        actionsOriginal[1] = abi.encodeCall(
            ISettlerActions.BASIC,
            (address(WETH), 10_000, address(WETH), 0x04, abi.encodeWithSignature("withdraw(uint256)", 0 wei))
        );

        bytes memory actions = abi.encode(actionsOriginal);
        assembly ("memory-safe") {
            let len := mload(actions)
            actions := add(0x20, actions)
            mstore(actions, sub(len, 0x20))
        }

        ISettlerBase.AllowedSlippage memory slippage =
            ISettlerBase.AllowedSlippage({recipient: payable(address(this)), buyToken: ETH, minAmountOut: 1 wei});

        uint256 beforeBalance = address(this).balance;

        feeCollector.swap(settler, USDC, slippage, actions, bytes32(0));

        assertGt(address(this).balance, beforeBalance);
    }

    function testMultiSwap() public {
        deal(address(WETH), address(feeCollector), takingAmount);
        deal(address(USDT), address(feeCollector), makingAmount);

        bytes[] memory actionsOriginal = new bytes[](1);
        actionsOriginal[0] = abi.encodeCall(
            ISettlerActions.UNISWAPV3_VIP,
            (
                address(settler),
                abi.encodePacked(WETH, uint8(0), uint24(500), USDC),
                ISignatureTransfer.PermitTransferFrom({
                    permitted: ISignatureTransfer.TokenPermissions({token: address(WETH), amount: type(uint256).max}),
                    nonce: 0,
                    deadline: block.timestamp + 5 minutes
                }),
                "",
                0
            )
        );

        bytes memory actions0 = abi.encode(actionsOriginal);
        assembly ("memory-safe") {
            let len := mload(actions0)
            actions0 := add(0x20, actions0)
            mstore(actions0, sub(len, 0x20))
        }

        actionsOriginal[0] = abi.encodeCall(
            ISettlerActions.UNISWAPV3_VIP,
            (
                address(settler),
                abi.encodePacked(USDT, uint8(0), uint24(100), USDC),
                ISignatureTransfer.PermitTransferFrom({
                    permitted: ISignatureTransfer.TokenPermissions({token: address(USDT), amount: type(uint256).max}),
                    nonce: 0,
                    deadline: block.timestamp + 5 minutes
                }),
                "",
                0
            )
        );

        bytes memory actions1 = abi.encode(actionsOriginal);
        assembly ("memory-safe") {
            let len := mload(actions1)
            actions1 := add(0x20, actions1)
            mstore(actions1, sub(len, 0x20))
        }

        Swap[] memory swaps = new Swap[](2);
        swaps[0].sellToken = WETH;
        swaps[0].minAmountOut = 1 wei;
        swaps[0].actions = actions0;
        swaps[0].zid = bytes32(0);
        swaps[1].sellToken = USDT;
        swaps[1].minAmountOut = 1 wei;
        swaps[1].actions = actions1;
        swaps[1].zid = bytes32(0);

        vm.expectEmit(false, true, true, false, address(USDC));
        emit IERC20.Transfer(0xFFfFfFffFFfffFFfFFfFFFFFffFFFffffFfFFFfF, address(this), type(uint256).max);
        vm.expectEmit(false, true, true, false, address(USDC));
        emit IERC20.Transfer(0xFFfFfFffFFfffFFfFFfFFFFFffFFFffffFfFFFfF, address(this), type(uint256).max);

        feeCollector.multiSwap(settler, payable(address(this)), USDC, swaps);

        assertGt(USDC.balanceOf(address(this)), 0);
    }

    function testCollectTokens() public {
        deal(address(WETH), address(feeCollector), takingAmount);
        deal(address(USDC), address(feeCollector), makingAmount);
        deal(address(USDT), address(feeCollector), makingAmount);
        IERC20[] memory tokens = new IERC20[](3);
        tokens[0] = WETH;
        tokens[1] = USDC;
        tokens[2] = USDT;

        vm.expectEmit(address(WETH));
        emit IERC20.Transfer(address(feeCollector), address(this), takingAmount);
        vm.expectEmit(address(USDC));
        emit IERC20.Transfer(address(feeCollector), address(this), makingAmount);
        vm.expectEmit(address(USDT));
        emit IERC20.Transfer(address(feeCollector), address(this), makingAmount);

        feeCollector.collectTokens(tokens, address(this));
    }

    function testCollectEth() public {
        vm.deal(address(feeCollector), takingAmount);

        uint256 beforeBalance = address(this).balance;
        feeCollector.collectEth(payable(this));

        assertGt(address(this).balance, beforeBalance);
    }

    receive() external payable {}
}
