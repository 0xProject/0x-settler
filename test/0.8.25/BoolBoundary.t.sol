// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Test} from "@forge-std/Test.sol";
import {IERC20} from "@forge-std/interfaces/IERC20.sol";
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
        view
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
}
