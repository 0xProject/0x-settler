// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Test} from "@forge-std/Test.sol";
import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {Utils} from "test/unit/Utils.sol";

import {FastLogic} from "src/utils/FastLogic.sol";
import {Ternary} from "src/utils/Ternary.sol";
import {UnsafeMath, Math} from "src/utils/UnsafeMath.sol";
import {FastPermit, SafePermit} from "src/utils/SafePermit.sol";
import {IERC20PermitCommon, IDAIStylePermit} from "src/interfaces/IERC2612.sol";

import {IEulerSwap, FastEulerSwap} from "src/core/EulerSwap.sol";
import {IUniV2Pair, FastUniswapV2Pool} from "src/core/UniswapV2.sol";
import {IUniswapV3Pool, FastUniswapV3Pool} from "src/core/UniswapV3Fork.sol";
import {IHanjiPool, FastHanjiPool} from "src/core/Hanji.sol";
import {IMaverickV2Pool, FastMaverickV2Pool} from "src/core/MaverickV2.sol";
import {IEkuboCore, PoolKey as EkuboPoolKey, Config, SqrtRatio, UnsafeEkuboCore} from "src/core/EkuboV2.sol";
import {
    IEkuboCore as IEkuboCoreV3,
    PoolKey as EkuboV3PoolKey,
    Config as EkuboV3Config,
    SqrtRatio as EkuboV3SqrtRatio,
    UnsafeEkuboCore as UnsafeEkuboV3Core
} from "src/core/EkuboV3.sol";
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

contract BoolBoundaryHarness {
    using SafePermit for IDAIStylePermit;

    function fastDaiPermit(IDAIStylePermit token) external returns (bool success) {
        bool allowed;
        assembly ("memory-safe") {
            allowed := 0x02
        }
        return
            FastPermit.fastDAIPermit(token, address(0x11), address(0x22), 0x33, 0x44, allowed, bytes32(0), bytes32(0));
    }

    function safeDaiPermit(IDAIStylePermit token, address owner, bytes32 vs, bytes32 r) external {
        bool allowed;
        assembly ("memory-safe") {
            allowed := 0x02
        }
        token.safePermit(owner, address(0x22), 0, 0, allowed, vs, r);
    }

    function fastUniswapV2GetReserves(address pool) external view returns (uint256 sellReserve, uint256 buyReserve) {
        bool zeroForOne;
        assembly ("memory-safe") {
            zeroForOne := 0x02
        }
        return FastUniswapV2Pool.fastGetReserves(pool, zeroForOne);
    }

    function fastUniswapV2Swap(address pool, uint256 buyAmount, address recipient) external {
        bool zeroForOne;
        assembly ("memory-safe") {
            zeroForOne := 0x02
        }
        FastUniswapV2Pool.fastSwap(pool, zeroForOne, buyAmount, recipient);
    }

    function fastEulerSwap(IEulerSwap pool, uint256 amountOut, address recipient) external {
        bool zeroForOne;
        assembly ("memory-safe") {
            zeroForOne := 0x02
        }
        FastEulerSwap.fastSwap(pool, zeroForOne, amountOut, recipient);
    }

    function uniswapV3Swap(
        IUniswapV3Pool pool,
        address recipient,
        uint256 sellAmount,
        uint160 sqrtPriceLimitX96,
        bytes memory callbackData
    ) external returns (bytes memory returndata) {
        bool zeroForOne;
        // Force a dirty true bool before calling the production encoder.
        assembly ("memory-safe") {
            zeroForOne := 0x02
        }
        (bytes memory data,) =
            FastUniswapV3Pool.fastEncodeSwap(recipient, zeroForOne, sellAmount, sqrtPriceLimitX96, callbackData);
        bool success;
        (success, returndata) = address(pool).call(data);
        require(success);
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

    function ekuboV3Swap(
        IEkuboCoreV3 core,
        EkuboV3PoolKey memory poolKey,
        int256 amount,
        EkuboV3SqrtRatio sqrtRatioLimit
    ) external returns (int256 delta0, int256 delta1) {
        bool isToken1;
        assembly ("memory-safe") {
            isToken1 := 0x02
        }
        return UnsafeEkuboV3Core.unsafeSwap(core, poolKey, amount, isToken1, sqrtRatioLimit);
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

contract BoolBoundaryTest is Utils, Test {
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
        address token = makeAddr("dai");
        _mockExpectCall(
            token,
            abi.encodeCall(
                IDAIStylePermit.permit,
                (address(0x11), address(0x22), uint256(0x33), uint256(0x44), true, uint8(27), bytes32(0), bytes32(0))
            ),
            abi.encode(true)
        );

        assertTrue(harness.fastDaiPermit(IDAIStylePermit(token)));
    }

    function testSafeDaiPermitFallbackCanonicalizesDirtyBool() public {
        uint256 ownerPrivateKey = 0xa11ce;
        address owner = vm.addr(ownerPrivateKey);
        address token = makeAddr("dai");
        bytes32 domainSeparator = keccak256(
            abi.encode(
                keccak256("EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)"),
                keccak256("MockDaiPermitToken"),
                keccak256("1"),
                block.chainid,
                token
            )
        );

        bytes32 structHash = keccak256(
            abi.encode(
                keccak256("Permit(address holder,address spender,uint256 nonce,uint256 expiry,bool allowed)"),
                owner,
                address(0x22),
                uint256(0),
                uint256(0),
                true
            )
        );
        bytes32 signingHash = keccak256(abi.encodePacked(hex"1901", domainSeparator, structHash));
        (uint8 v, bytes32 r, bytes32 s) = vm.sign(ownerPrivateKey, signingHash);
        bytes32 vs = bytes32(uint256(s) | (uint256(v - 27) << 255));

        _mockExpectCall(
            token,
            abi.encodeCall(IDAIStylePermit.permit, (owner, address(0x22), uint256(0), uint256(0), true, v, r, s)),
            abi.encode(false)
        );
        _mockExpectCall(token, abi.encodeCall(IERC20PermitCommon.nonces, (owner)), abi.encode(uint256(1)));
        _mockExpectCall(token, abi.encodeCall(IERC20.allowance, (owner, address(0x22))), abi.encode(type(uint256).max));
        _mockExpectCall(token, abi.encodeCall(IERC20PermitCommon.DOMAIN_SEPARATOR, ()), abi.encode(domainSeparator));

        harness.safeDaiPermit(IDAIStylePermit(token), owner, vs, r);
    }

    function testUniswapV2BoundaryUsesCanonicalBit() public {
        address pool = makeAddr("pool");
        _mockExpectCall(
            pool, abi.encodeCall(IUniV2Pair.getReserves, ()), abi.encode(uint112(11), uint112(22), uint32(0))
        );

        (uint256 sellReserve, uint256 buyReserve) = harness.fastUniswapV2GetReserves(pool);
        assertEq(sellReserve, 11);
        assertEq(buyReserve, 22);

        _mockExpectCall(pool, abi.encodeCall(IUniV2Pair.swap, (uint256(0), uint256(7), address(0x44), bytes(""))), "");
        harness.fastUniswapV2Swap(pool, 7, address(0x44));
    }

    function testEulerSwapBoundaryUsesCanonicalBit() public {
        address pool = makeAddr("pool");
        _mockExpectCall(pool, abi.encodeCall(IEulerSwap.swap, (0, 9, address(0x55), bytes(""))), bytes(""));
        harness.fastEulerSwap(IEulerSwap(pool), 9, address(0x55));
    }

    function testUniswapV3SwapCanonicalizesDirtyZeroForOne() public {
        address pool = makeAddr("pool");
        bytes memory callbackData = abi.encodePacked(address(0x55), address(0x66));
        bytes memory returnData = abi.encode(int256(0), int256(-7));
        bytes memory expectedCall = bytes.concat(
            abi.encodeWithSelector(IUniswapV3Pool.swap.selector, address(0x44), true, uint256(7), uint160(9)),
            bytes32(uint256(0xa0)),
            bytes32(callbackData.length),
            callbackData
        );
        uint256 zeroForOneWord;
        // Verify the expected calldata uses a canonical ABI bool word for `zeroForOne`.
        assembly ("memory-safe") {
            zeroForOneWord := mload(add(expectedCall, 0x44))
        }
        assertEq(zeroForOneWord, 1);

        _mockExpectCall(pool, expectedCall, returnData);
        assertEq(harness.uniswapV3Swap(IUniswapV3Pool(pool), address(0x44), 7, 9, callbackData), returnData);
    }

    function testHanjiBoundaryCanonicalizesDirtyBool() public {
        address pool = makeAddr("pool");
        _mockExpectCall(
            pool,
            abi.encodeCall(
                IHanjiPool.placeOrder,
                (true, uint128(7), uint72(11), type(uint128).max, true, false, true, type(uint256).max)
            ),
            abi.encode(uint64(0), uint128(0), uint128(0), uint128(0))
        );

        harness.hanjiPlaceMarketOrder(IHanjiPool(pool));

        _mockExpectCall(
            pool,
            abi.encodeCall(IHanjiPool.getConfig, ()),
            abi.encode(uint256(0), uint256(0), address(0x11), address(0x22))
        );
        assertEq(address(harness.hanjiGetToken(IHanjiPool(pool))), address(0x22));
    }

    function testMaverickEncodeCanonicalizesDirtyBool() public {
        bytes memory data = harness.maverickEncode(address(0x66), 7, 9, hex"abcd");

        assertEq(
            data,
            bytes.concat(
                abi.encodeWithSelector(
                    IMaverickV2Pool.swap.selector,
                    address(0x66),
                    uint256(7),
                    true,
                    false,
                    int32(9),
                    uint256(0xc0),
                    uint256(2)
                ),
                hex"abcd"
            )
        );
    }

    function testEkuboV2SwapCanonicalizesDirtyBool() public {
        address core = makeAddr("core");
        EkuboPoolKey memory key = EkuboPoolKey({token0: address(0x11), token1: address(0x22), config: Config.wrap(0)});
        _mockExpectCall(
            core,
            abi.encodeCall(IEkuboCore.swap_611415377, (key, int128(7), true, SqrtRatio.wrap(9), uint256(0))),
            abi.encode(int128(0), int128(0))
        );

        harness.ekuboV2Swap(IEkuboCore(core), key, 7, SqrtRatio.wrap(9));
    }

    function testEkuboV3SwapCanonicalizesDirtyBool() public {
        address core = makeAddr("core");
        EkuboV3PoolKey memory key =
            EkuboV3PoolKey({token0: address(0x11), token1: address(0x22), config: EkuboV3Config.wrap(0)});
        bytes memory expectedCall =
            bytes.concat(bytes4(0), abi.encode(key), abi.encodePacked(uint96(9), int128(7), uint32(0x80000000)));
        _mockExpectCall(core, expectedCall, abi.encode(bytes32(0)));

        harness.ekuboV3Swap(IEkuboCoreV3(core), key, 7, EkuboV3SqrtRatio.wrap(9));
    }

    function testPancakeInfinityCanonicalizesDirtyBool() public {
        address cl = makeAddr("cl");
        address bin = makeAddr("bin");
        PancakePoolKey memory key = PancakePoolKey({
            currency0: IERC20(address(0x11)),
            currency1: IERC20(address(0x22)),
            hooks: IHooks.wrap(address(0x33)),
            poolManager: IPancakeInfinityCLPoolManager(cl),
            fee: 500,
            parameters: bytes32(uint256(7))
        });

        _mockExpectCall(
            cl,
            bytes.concat(
                abi.encodeWithSelector(
                    IPancakeInfinityCLPoolManager.swap.selector,
                    key,
                    true,
                    int256(1),
                    uint160(2),
                    uint256(0x140),
                    uint256(1)
                ),
                hex"ab"
            ),
            abi.encode(BalanceDelta.wrap(0))
        );
        harness.pancakeClSwap(IPancakeInfinityCLPoolManager(cl), key, 1, 2, hex"ab");

        _mockExpectCall(
            bin,
            bytes.concat(
                abi.encodeWithSelector(
                    IPancakeInfinityBinPoolManager.swap.selector, key, true, int128(3), uint256(0x120), uint256(1)
                ),
                hex"cd"
            ),
            abi.encode(BalanceDelta.wrap(0))
        );
        harness.pancakeBinSwap(IPancakeInfinityBinPoolManager(bin), key, 3, hex"cd");
    }

    function testFlashEncoderCanonicalizesDirtyBoolBytes() public {
        bytes memory data = harness.flashEncode(hex"010203");
        assertEq(uint8(data[0x88]), 1);

        bytes memory vipData = harness.flashEncodeVip(hex"040506", hex"deadbeef");
        assertEq(uint8(vipData[0x88]), 1);
        assertEq(uint8(vipData[0x111]), 1);
    }
}
