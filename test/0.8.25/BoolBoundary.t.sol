// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Test} from "@forge-std/Test.sol";
import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";

import {FastLogic} from "src/utils/FastLogic.sol";
import {Ternary} from "src/utils/Ternary.sol";
import {UnsafeMath, Math} from "src/utils/UnsafeMath.sol";
import {FastPermit} from "src/utils/SafePermit.sol";
import {IDAIStylePermit} from "src/interfaces/IERC2612.sol";

import {IEVC, FastEvc, IEulerSwap, FastEulerSwap} from "src/core/EulerSwap.sol";
import {IUniV2Pair, fastUniswapV2Pool} from "src/core/UniswapV2.sol";
import {IHanjiPool, FastHanjiPool} from "src/core/Hanji.sol";
import {IMaverickV2Pool, FastMaverickV2Pool} from "src/core/MaverickV2.sol";
import {IEkuboCore, PoolKey as EkuboPoolKey, Config, SqrtRatio, UnsafeEkuboCore} from "src/core/EkuboV2.sol";
import {
    IPancakeInfinityCLPoolManager,
    IPancakeInfinityBinPoolManager,
    PoolKey as PancakePoolKey,
    IHooks,
    UnsafePancakeInfinityPoolManager,
    UnsafePancakeInfinityBinPoolManager
} from "src/core/PancakeInfinity.sol";
import {Encoder} from "src/core/FlashAccountingCommon.sol";
import {BalanceDelta} from "src/core/UniswapV4Types.sol";

contract MockDaiPermitToken {
    bool public lastAllowed;

    function permit(address, address, uint256, uint256, bool allowed, uint8, bytes32, bytes32) external returns (bool) {
        lastAllowed = allowed;
        return true;
    }
}

contract MockEvcBool {
    bytes internal response;

    function setResponse(bytes memory newResponse) external {
        response = newResponse;
    }

    fallback(bytes calldata) external returns (bytes memory) {
        return response;
    }
}

contract MockUniswapV2Pair is IUniV2Pair {
    uint112 internal reserve0;
    uint112 internal reserve1;

    uint256 public amount0Out;
    uint256 public amount1Out;
    address public recipient;
    bytes public swapData;

    function setReserves(uint112 reserve0_, uint112 reserve1_) external {
        reserve0 = reserve0_;
        reserve1 = reserve1_;
    }

    function token0() external pure returns (address) {
        return address(0);
    }

    function token1() external pure returns (address) {
        return address(0);
    }

    function getReserves() external view returns (uint112, uint112, uint32) {
        return (reserve0, reserve1, 0);
    }

    function swap(uint256 amount0Out_, uint256 amount1Out_, address recipient_, bytes calldata data_) external {
        amount0Out = amount0Out_;
        amount1Out = amount1Out_;
        recipient = recipient_;
        swapData = data_;
    }
}

contract MockEulerSwap {
    uint256 public amount0Out;
    uint256 public amount1Out;
    address public recipient;

    function swap(uint256 amount0Out_, uint256 amount1Out_, address to, bytes calldata) external {
        amount0Out = amount0Out_;
        amount1Out = amount1Out_;
        recipient = to;
    }
}

contract MockHanjiPool is IHanjiPool {
    bool public lastIsAsk;
    bytes4 public lastSelector;

    address internal tokenX;
    address internal tokenY;

    constructor(address tokenX_, address tokenY_) {
        tokenX = tokenX_;
        tokenY = tokenY_;
    }

    function placeOrder(bool isAsk, uint128, uint72, uint128, bool, bool, bool, uint256)
        external
        payable
        returns (uint64, uint128, uint128, uint128)
    {
        lastSelector = msg.sig;
        lastIsAsk = isAsk;
        return (0, 0, 0, 0);
    }

    function placeMarketOrderWithTargetValue(bool isAsk, uint128, uint72, uint128, bool, uint256)
        external
        payable
        returns (uint128, uint128, uint128)
    {
        lastSelector = msg.sig;
        lastIsAsk = isAsk;
        return (0, 0, 0);
    }

    function getConfig()
        external
        view
        returns (uint256, uint256, address, address, bool, bool, address, address, uint64, uint64, uint64, uint64, bool)
    {
        return (0, 0, tokenX, tokenY, false, false, address(0), address(0), 0, 0, 0, 0, false);
    }
}

contract MockMaverickPool {
    address public lastRecipient;
    uint256 public lastAmount;
    bool public lastTokenAIn;
    bool public lastExactOutput;
    int32 public lastTickLimit;
    bytes public lastData;

    function swap(address recipient, IMaverickV2Pool.SwapParams calldata params, bytes calldata data)
        external
        returns (uint256 amountIn, uint256 amountOut)
    {
        lastRecipient = recipient;
        lastAmount = params.amount;
        lastTokenAIn = params.tokenAIn;
        lastExactOutput = params.exactOutput;
        lastTickLimit = params.tickLimit;
        lastData = data;
        return (0, 0);
    }
}

contract MockEkuboCore is IEkuboCore {
    bool public lastIsToken1;

    function lock() external {}

    function swap_611415377(EkuboPoolKey memory, int128, bool isToken1, SqrtRatio, uint256)
        external
        payable
        returns (int128 delta0, int128 delta1)
    {
        lastIsToken1 = isToken1;
        return (0, 0);
    }

    function forward(address) external {}

    function pay(address) external pure returns (uint128 payment) {
        return 0;
    }

    function withdraw(address, address, uint128) external {}
}

contract MockPancakeClManager {
    bool public lastZeroForOne;
    bytes public lastHookData;

    function swap(
        PancakePoolKey memory,
        IPancakeInfinityCLPoolManager.SwapParams calldata params,
        bytes calldata hookData
    ) external returns (BalanceDelta delta) {
        lastZeroForOne = params.zeroForOne;
        lastHookData = hookData;
        return BalanceDelta.wrap(0);
    }
}

contract MockPancakeBinManager {
    bool public lastSwapForY;
    bytes public lastHookData;

    function swap(PancakePoolKey memory, bool swapForY, int128, bytes calldata hookData)
        external
        returns (BalanceDelta delta)
    {
        lastSwapForY = swapForY;
        lastHookData = hookData;
        return BalanceDelta.wrap(0);
    }
}

contract BoolBoundaryHarness {
    function fastIsAuthorized(IEVC evc) external view returns (bool) {
        return FastEvc.fastIsAccountOperatorAuthorized(evc, address(0x11), address(0x22));
    }

    function fastDaiPermit(IDAIStylePermit token) external returns (bool success) {
        bool allowed;
        assembly ("memory-safe") {
            allowed := 0x02
        }
        return
            FastPermit.fastDAIPermit(token, address(0x11), address(0x22), 0x33, 0x44, allowed, bytes32(0), bytes32(0));
    }

    function fastUniswapV2GetReserves(address pool) external view returns (uint256 sellReserve, uint256 buyReserve) {
        bool zeroForOne;
        assembly ("memory-safe") {
            zeroForOne := 0x02
        }
        return fastUniswapV2Pool.fastGetReserves(pool, zeroForOne);
    }

    function fastUniswapV2Swap(address pool, uint256 buyAmount, address recipient) external {
        bool zeroForOne;
        assembly ("memory-safe") {
            zeroForOne := 0x02
        }
        fastUniswapV2Pool.fastSwap(pool, zeroForOne, buyAmount, recipient);
    }

    function fastEulerSwap(IEulerSwap pool, uint256 amountOut, address recipient) external {
        bool zeroForOne;
        assembly ("memory-safe") {
            zeroForOne := 0x02
        }
        FastEulerSwap.fastSwap(pool, zeroForOne, amountOut, recipient);
    }

    function hanjiPlaceMarketOrder(IHanjiPool pool) external returns (uint256 executed) {
        bool isAsk;
        assembly ("memory-safe") {
            isAsk := 0x02
        }
        return FastHanjiPool.placeMarketOrder(pool, 0, isAsk, 7, 11);
    }

    function hanjiGetToken(IHanjiPool pool) external view returns (IERC20 token) {
        bool tokenY;
        assembly ("memory-safe") {
            tokenY := 0x02
        }
        return FastHanjiPool.getToken(pool, tokenY);
    }

    function maverickEncode(address recipient, uint256 amount, int256 tickLimit, bytes memory swapCallbackData)
        external
        pure
        returns (bytes memory data)
    {
        bool tokenAIn;
        assembly ("memory-safe") {
            tokenAIn := 0x02
        }
        return FastMaverickV2Pool.fastEncodeSwap(
            IMaverickV2Pool(address(0)), recipient, amount, tokenAIn, tickLimit, swapCallbackData
        );
    }

    function ekuboV2Swap(IEkuboCore core, EkuboPoolKey memory poolKey, int256 amount, SqrtRatio sqrtRatioLimit)
        external
        returns (int256 delta0, int256 delta1)
    {
        bool isToken1;
        assembly ("memory-safe") {
            isToken1 := 0x02
        }
        return UnsafeEkuboCore.unsafeSwap(core, poolKey, amount, isToken1, sqrtRatioLimit);
    }

    function pancakeClSwap(
        IPancakeInfinityCLPoolManager poolManager,
        PancakePoolKey memory key,
        int256 amountSpecified,
        uint256 sqrtPriceLimitX96,
        bytes calldata hookData
    ) external returns (BalanceDelta delta) {
        bool zeroForOne;
        assembly ("memory-safe") {
            zeroForOne := 0x02
        }
        return UnsafePancakeInfinityPoolManager.unsafeSwap(
            poolManager, key, zeroForOne, amountSpecified, sqrtPriceLimitX96, hookData
        );
    }

    function pancakeBinSwap(
        IPancakeInfinityBinPoolManager poolManager,
        PancakePoolKey memory key,
        int128 amountSpecified,
        bytes calldata hookData
    ) external returns (BalanceDelta delta) {
        bool swapForY;
        assembly ("memory-safe") {
            swapForY := 0x02
        }
        return UnsafePancakeInfinityBinPoolManager.unsafeSwap(poolManager, key, swapForY, amountSpecified, hookData);
    }

    function flashEncode(bytes memory fills) external view returns (bytes memory data) {
        bool feeOnTransfer;
        assembly ("memory-safe") {
            feeOnTransfer := 0x02
        }
        return Encoder.encode(0x12345678, address(0x11), IERC20(address(0x22)), 1, feeOnTransfer, 1, 2, fills, 3);
    }

    function flashEncodeVip(bytes memory fills, bytes memory sig) external pure returns (bytes memory data) {
        bool feeOnTransfer;
        bool isForwarded;
        assembly ("memory-safe") {
            feeOnTransfer := 0x02
            isForwarded := 0x03
        }
        ISignatureTransfer.PermitTransferFrom memory permit = ISignatureTransfer.PermitTransferFrom({
            permitted: ISignatureTransfer.TokenPermissions({token: address(0x33), amount: 4}), nonce: 5, deadline: 6
        });
        return Encoder.encodeVIP(0x12345678, address(0x11), feeOnTransfer, 1, 2, fills, permit, sig, isForwarded, 3);
    }
}

contract BoolBoundaryTest is Test {
    using FastLogic for bool;
    using Ternary for bool;
    using UnsafeMath for uint256;
    using Math for uint256;

    BoolBoundaryHarness internal harness;

    function setUp() public {
        harness = new BoolBoundaryHarness();
    }

    function testHelpersAcceptDirtyBools() public {
        bool dirtyTrue;
        assembly ("memory-safe") {
            dirtyTrue := 0x02
        }

        assertTrue(dirtyTrue.or(false));
        assertTrue(dirtyTrue.and(true));
        assertTrue(dirtyTrue.andNot(false));
        assertEq(dirtyTrue.toUint(), 1);

        assertEq(dirtyTrue.ternary(uint256(7), uint256(9)), 7);
        assertEq(dirtyTrue.ternary(int256(7), int256(9)), 7);
        assertEq(dirtyTrue.ternary(bytes4(0x01020304), bytes4(0x05060708)), bytes4(0x01020304));
        assertEq(dirtyTrue.ternary(address(0x11), address(0x22)), address(0x11));
        assertEq(dirtyTrue.orZero(13), 13);

        (uint256 a, uint256 b) = dirtyTrue.maybeSwap(uint256(1), uint256(2));
        assertEq(a, 2);
        assertEq(b, 1);

        (int256 x, int256 y) = dirtyTrue.maybeSwap(int256(3), int256(4));
        assertEq(x, 4);
        assertEq(y, 3);

        assertEq(uint256(5).unsafeInc(dirtyTrue), 6);
        assertEq(uint256(5).unsafeDec(dirtyTrue), 4);
        assertEq(uint256(5).inc(dirtyTrue), 6);
        assertEq(uint256(5).dec(dirtyTrue), 4);
        assertEq(Math.toInt(dirtyTrue), 1);
    }

    function testFastDaiPermitCanonicalizesDirtyBool() public {
        MockDaiPermitToken token = new MockDaiPermitToken();

        assertTrue(harness.fastDaiPermit(IDAIStylePermit(address(token))));
        assertTrue(token.lastAllowed());
    }

    function testFastEvcAcceptsCanonicalBool() public {
        MockEvcBool evc = new MockEvcBool();

        evc.setResponse(abi.encode(true));
        assertTrue(harness.fastIsAuthorized(IEVC(address(evc))));

        evc.setResponse(abi.encode(false));
        assertFalse(harness.fastIsAuthorized(IEVC(address(evc))));
    }

    function testFastEvcRejectsShortOrDirtyBool() public {
        MockEvcBool evc = new MockEvcBool();

        evc.setResponse(new bytes(31));
        vm.expectRevert(bytes(""));
        harness.fastIsAuthorized(IEVC(address(evc)));

        evc.setResponse(abi.encode(uint256(2)));
        vm.expectRevert(bytes(""));
        harness.fastIsAuthorized(IEVC(address(evc)));
    }

    function testUniswapV2BoundaryUsesCanonicalBit() public {
        MockUniswapV2Pair pool = new MockUniswapV2Pair();
        pool.setReserves(11, 22);

        (uint256 sellReserve, uint256 buyReserve) = harness.fastUniswapV2GetReserves(address(pool));
        assertEq(sellReserve, 11);
        assertEq(buyReserve, 22);

        harness.fastUniswapV2Swap(address(pool), 7, address(0x44));
        assertEq(pool.amount0Out(), 0);
        assertEq(pool.amount1Out(), 7);
        assertEq(pool.recipient(), address(0x44));
        assertEq(pool.swapData().length, 0);
    }

    function testEulerSwapBoundaryUsesCanonicalBit() public {
        MockEulerSwap pool = new MockEulerSwap();

        harness.fastEulerSwap(IEulerSwap(address(pool)), 9, address(0x55));
        assertEq(pool.amount0Out(), 0);
        assertEq(pool.amount1Out(), 9);
        assertEq(pool.recipient(), address(0x55));
    }

    function testHanjiBoundaryCanonicalizesDirtyBool() public {
        MockHanjiPool pool = new MockHanjiPool(address(0x11), address(0x22));

        harness.hanjiPlaceMarketOrder(IHanjiPool(address(pool)));
        assertTrue(pool.lastIsAsk());
        assertTrue(
            pool.lastSelector() == IHanjiPool.placeOrder.selector
                || pool.lastSelector() == IHanjiPool.placeMarketOrderWithTargetValue.selector
        );

        assertEq(address(harness.hanjiGetToken(IHanjiPool(address(pool)))), address(0x22));
    }

    function testMaverickEncodeCanonicalizesDirtyBool() public {
        MockMaverickPool pool = new MockMaverickPool();
        bytes memory data = harness.maverickEncode(address(0x66), 7, 9, hex"abcd");

        (bool success,) = address(pool).call(data);
        assertTrue(success);
        assertEq(pool.lastRecipient(), address(0x66));
        assertEq(pool.lastAmount(), 7);
        assertTrue(pool.lastTokenAIn());
        assertFalse(pool.lastExactOutput());
        assertEq(pool.lastTickLimit(), 9);
        assertEq(pool.lastData(), hex"abcd");
    }

    function testEkuboV2SwapCanonicalizesDirtyBool() public {
        MockEkuboCore core = new MockEkuboCore();
        EkuboPoolKey memory key = EkuboPoolKey({token0: address(0x11), token1: address(0x22), config: Config.wrap(0)});

        harness.ekuboV2Swap(IEkuboCore(address(core)), key, 7, SqrtRatio.wrap(9));
        assertTrue(core.lastIsToken1());
    }

    function testPancakeInfinityCanonicalizesDirtyBool() public {
        MockPancakeClManager cl = new MockPancakeClManager();
        MockPancakeBinManager bin = new MockPancakeBinManager();
        PancakePoolKey memory key = PancakePoolKey({
            currency0: IERC20(address(0x11)),
            currency1: IERC20(address(0x22)),
            hooks: IHooks.wrap(address(0x33)),
            poolManager: IPancakeInfinityCLPoolManager(address(cl)),
            fee: 500,
            parameters: bytes32(uint256(7))
        });

        harness.pancakeClSwap(IPancakeInfinityCLPoolManager(address(cl)), key, 1, 2, hex"ab");
        assertTrue(cl.lastZeroForOne());
        assertEq(cl.lastHookData(), hex"ab");

        harness.pancakeBinSwap(IPancakeInfinityBinPoolManager(address(bin)), key, 3, hex"cd");
        assertTrue(bin.lastSwapForY());
        assertEq(bin.lastHookData(), hex"cd");
    }

    function testFlashEncoderCanonicalizesDirtyBoolBytes() public {
        bytes memory data = harness.flashEncode(hex"010203");
        assertEq(uint8(data[0x88]), 1);

        bytes memory vipData = harness.flashEncodeVip(hex"040506", hex"deadbeef");
        assertEq(uint8(vipData[0x88]), 1);
        assertEq(uint8(vipData[0x111]), 1);
    }
}
