// SPDX-License-Identifier: GPL-2.0-or-later
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {SafeTransferLib} from "src/vendor/SafeTransferLib.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";

import {UniswapV4} from "src/core/UniswapV4.sol";
import {POOL_MANAGER, IUnlockCallback} from "src/core/UniswapV4Types.sol";
import {ItoA} from "src/utils/ItoA.sol";

import {IPoolManager} from "@uniswapv4/interfaces/IPoolManager.sol";
import {PoolKey} from "@uniswapv4/types/PoolKey.sol";
import {Currency} from "@uniswapv4/types/Currency.sol";
import {TickMath} from "@uniswapv4/libraries/TickMath.sol";
import {IHooks} from "@uniswapv4/interfaces/IHooks.sol";
import {PoolId, PoolIdLibrary} from "@uniswapv4/types/PoolId.sol";
import {SqrtPriceMath} from "@uniswapv4/libraries/SqrtPriceMath.sol";
import {BalanceDelta} from "@uniswapv4/types/BalanceDelta.sol";
import {StateLibrary} from "@uniswapv4/libraries/StateLibrary.sol";

import {SignatureExpired} from "src/core/SettlerErrors.sol";
import {Panic} from "src/utils/Panic.sol";
import {Revert} from "src/utils/Revert.sol";

import {ERC20} from "@solmate/tokens/ERC20.sol";

import {Test} from "@forge-std/Test.sol";
import {StdInvariant} from "@forge-std/StdInvariant.sol";
import {Vm} from "@forge-std/Vm.sol";

import {console} from "@forge-std/console.sol";

uint256 constant TOTAL_SUPPLY = 1 ether * 1 ether;
address constant testPrediction = 0x7FA9385bE102ac3EAc297483Dd6233D62b3e1496;
address constant stubPrediction = 0x5615dEB798BB3E4dFa0139dFa1b3D433Cc23b72f;

abstract contract InvariantAssume {
    uint256 private constant invariantAssumeDisabledSlot =
        0x802725342c64629bf019370b6b352d7d6f9d525d72b3bfcc7c8b0f79f510454d;

    constructor() {
        assert(invariantAssumeDisabledSlot == uint256(keccak256("invariant assume disabled")) - 1);
    }

    function disableInvariantAssume() internal {
        assembly ("memory-safe") {
            tstore(invariantAssumeDisabledSlot, 0x01)
        }
    }

    function invariantAssume(bool condition) internal view {
        assembly ("memory-safe") {
            if tload(invariantAssumeDisabledSlot) { revert(0x00, 0x00) }
            if iszero(condition) { stop() }
        }
    }
}

contract TestERC20 is ERC20, InvariantAssume {
    using ItoA for uint256;

    modifier onlyPredicted() {
        invariantAssume(
            msg.sender == testPrediction || msg.sender == stubPrediction || msg.sender == address(POOL_MANAGER)
        );
        _;
    }

    constructor()
        ERC20(
            string.concat("Token#", (uint256(uint160(address(this))) & 0xffffff).itoa()),
            string.concat("TKN", (uint256(uint160(address(this))) & 0xffffff).itoa()),
            18
        )
    {
        Vm(address(uint160(uint256(keccak256("hevm cheat code"))))).label(address(this), name);
        _mint(msg.sender, TOTAL_SUPPLY);
    }

    function approve(address spender, uint256 amount) public override onlyPredicted returns (bool) {
        return super.approve(spender, amount);
    }

    function permit(address owner, address spender, uint256 value, uint256 deadline, uint8 v, bytes32 r, bytes32 s)
        public
        override
        onlyPredicted
    {
        return super.permit(owner, spender, value, deadline, v, r, s);
    }

    // This is here because `require(amount != 0)` is a common defect in ERC20 implementations; we
    // want to make sure that Settler isn't accidentally triggering it.
    function transfer(address to, uint256 amount) public override onlyPredicted returns (bool) {
        require(amount != 0);
        return super.transfer(to, amount);
    }

    function transferFrom(address from, address to, uint256 amount) public override onlyPredicted returns (bool) {
        require(amount != 0);
        return super.transferFrom(from, to, amount);
    }
}

// TODO: create a FoT token variant

contract UniswapV4Stub is UniswapV4 {
    using Revert for bool;
    using SafeTransferLib for IERC20;

    function sellToUniswapV4(
        IERC20 sellToken,
        uint256 bps,
        bool feeOnTransfer,
        uint256 hashMul,
        uint256 hashMod,
        bytes memory fills,
        uint256 amountOutMin
    ) external payable returns (uint256) {
        require(_operator() == _msgSender());
        return super.sellToUniswapV4(_msgSender(), sellToken, bps, feeOnTransfer, hashMul, hashMod, fills, amountOutMin);
    }

    function sellToUniswapV4VIP(
        bool feeOnTransfer,
        uint256 hashMul,
        uint256 hashMod,
        bytes memory fills,
        ISignatureTransfer.PermitTransferFrom memory permit,
        bytes memory sig,
        uint256 amountOutMin
    ) external returns (uint256) {
        require(_operator() == _msgSender());
        return super.sellToUniswapV4VIP(_msgSender(), feeOnTransfer, hashMul, hashMod, fills, permit, sig, amountOutMin);
    }

    // bytes32(uint256(keccak256("operator slot")) - 1)
    bytes32 private constant _OPERATOR_SLOT = 0x009355806b743562f351db2e3726091207f49fa1cdccd5c65a7d4860ce3abbe9;

    function _setCallback(function (bytes calldata) internal returns (bytes memory) callback) private {
        assembly ("memory-safe") {
            tstore(_OPERATOR_SLOT, and(0xffff, callback))
        }
    }

    function _getCallback() private returns (function (bytes calldata) internal returns (bytes memory) callback) {
        assembly ("memory-safe") {
            callback := and(0xffff, tload(_OPERATOR_SLOT))
            tstore(_OPERATOR_SLOT, 0x00)
        }
    }

    fallback(bytes calldata) external returns (bytes memory) {
        require(_operator() == address(POOL_MANAGER));
        bytes calldata data = _msgData();
        require(uint32(bytes4(data)) == uint32(IUnlockCallback.unlockCallback.selector));
        data = data[4:];
        return _getCallback()(data);
    }

    address private immutable _deployer;

    constructor() {
        _deployer = msg.sender;
    }

    function _msgSender() internal view override returns (address) {
        return _deployer;
    }

    function _isForwarded() internal pure override returns (bool) {
        return false;
    }

    function _msgData() internal pure override returns (bytes calldata) {
        return msg.data;
    }

    function _hasMetaTxn() internal pure override returns (bool) {
        return false;
    }

    function _dispatch(uint256, bytes4, bytes calldata) internal pure override returns (bool) {
        revert("unimplemented");
    }

    function _isRestrictedTarget(address) internal pure override returns (bool) {
        revert("unimplemented");
    }

    function _operator() internal view override returns (address) {
        return msg.sender;
    }

    function _permitToSellAmountCalldata(ISignatureTransfer.PermitTransferFrom calldata permit)
        internal
        pure
        override
        returns (uint256)
    {
        return permit.permitted.amount;
    }

    function _permitToSellAmount(ISignatureTransfer.PermitTransferFrom memory)
        internal
        pure
        override
        returns (uint256)
    {
        revert("unimplemented");
    }

    function _permitToTransferDetails(ISignatureTransfer.PermitTransferFrom memory permit, address recipient)
        internal
        pure
        override
        returns (ISignatureTransfer.SignatureTransferDetails memory transferDetails, uint256 sellAmount)
    {
        transferDetails.to = recipient;
        transferDetails.requestedAmount = sellAmount = _permitToSellAmount(permit);
    }

    function _transferFromIKnowWhatImDoing(
        ISignatureTransfer.PermitTransferFrom memory,
        ISignatureTransfer.SignatureTransferDetails memory,
        address,
        bytes32,
        string memory,
        bytes memory,
        bool
    ) internal pure override {
        revert("unimplemented");
    }

    function _transferFromIKnowWhatImDoing(
        ISignatureTransfer.PermitTransferFrom memory permit,
        ISignatureTransfer.SignatureTransferDetails memory transferDetails,
        address from,
        bytes32 witness,
        string memory witnessTypeString,
        bytes memory sig
    ) internal pure override {
        return _transferFromIKnowWhatImDoing(
            permit, transferDetails, from, witness, witnessTypeString, sig, _isForwarded()
        );
    }

    function _transferFrom(
        ISignatureTransfer.PermitTransferFrom memory permit,
        ISignatureTransfer.SignatureTransferDetails memory transferDetails,
        bytes memory sig,
        bool isForwarded
    ) internal override {
        assert(!isForwarded);
        if (transferDetails.requestedAmount > permit.permitted.amount) {
            Panic.panic(Panic.ARITHMETIC_OVERFLOW);
        }
        if (permit.deadline < block.timestamp) {
            revert SignatureExpired(permit.deadline);
        }
        assert(permit.nonce == uint256(keccak256(sig)));
        IERC20(permit.permitted.token).safeTransferFrom(
            _msgSender(), transferDetails.to, transferDetails.requestedAmount
        );
    }

    function _transferFrom(
        ISignatureTransfer.PermitTransferFrom memory permit,
        ISignatureTransfer.SignatureTransferDetails memory transferDetails,
        bytes memory sig
    ) internal override {
        return _transferFrom(permit, transferDetails, sig, _isForwarded());
    }

    function _setOperatorAndCall(
        address target,
        bytes memory data,
        uint32 selector,
        function (bytes calldata) internal returns (bytes memory) callback
    ) internal override returns (bytes memory) {
        require(target == address(POOL_MANAGER));
        require(selector == uint32(IUnlockCallback.unlockCallback.selector));
        _setCallback(callback);
        (bool success, bytes memory returndata) = target.call(data);
        success.maybeRevert(returndata);
        return returndata;
    }

    modifier metaTx(address msgSender, bytes32 witness) override {
        revert("unimplemented");
        _;
    }

    modifier takerSubmitted() override {
        revert("unimplemented");
        _;
    }

    function _allowanceHolderTransferFrom(address, address, address, uint256) internal pure override {
        revert("unimplemented");
    }

    receive() external payable {}
}

abstract contract BaseUniswapV4UnitTest is Test {
    using Revert for bool;

    UniswapV4Stub internal stub;

    function _replaceAll(bytes memory haystack, bytes32 needle, bytes32 replace, bytes32 mask)
        internal
        pure
        returns (uint256 count)
    {
        assembly ("memory-safe") {
            let padding
            for {
                let x := and(mask, sub(0x00, mask))
                let i := 0x07
            } gt(i, 0x02) { i := sub(i, 0x01) } {
                let s := shl(i, 0x01) // [128, 64, 32, 16, 8]
                if shr(s, shr(padding, x)) { padding := add(s, padding) }
            }

            padding := add(0x01, shr(0x03, padding))
            needle := and(mask, needle)
            replace := and(mask, replace)

            for {
                let i := add(0x20, haystack)
                let end := add(padding, add(mload(haystack), haystack))
            } lt(i, end) { i := add(0x01, i) } {
                let word := mload(i)
                if eq(and(mask, word), needle) {
                    mstore(i, or(and(not(mask), word), replace))
                    count := add(0x01, count)
                }
            }
        }
    }

    function _deployStub() internal returns (address) {
        stub = new UniswapV4Stub();
        return address(stub);
    }

    function _deployPoolManager() internal returns (address poolManagerSrc) {
        poolManagerSrc = vm.deployCode("PoolManager.sol:PoolManager");
        require(poolManagerSrc != address(0));
        bytes memory poolManagerCode = poolManagerSrc.code;
        uint256 replaceCount = _replaceAll(
            poolManagerCode,
            bytes32(bytes20(uint160(poolManagerSrc))),
            bytes32(bytes20(uint160(address(POOL_MANAGER)))),
            bytes32(bytes20(type(uint160).max))
        );
        console.log("replaced", replaceCount, "occurrences of pool manager immutable address");
        vm.etch(address(POOL_MANAGER), poolManagerCode);
        vm.label(address(POOL_MANAGER), "PoolManager");

        vm.record();
        (bool success, bytes memory returndata) = address(POOL_MANAGER).staticcall(abi.encodeWithSignature("owner()"));
        success.maybeRevert(returndata);
        assert(abi.decode(returndata, (address)) == address(0));
        (bytes32[] memory readSlots,) = vm.accesses(address(POOL_MANAGER));
        assert(readSlots.length == 1);
        bytes32 ownerSlot = readSlots[0];
        assert(vm.load(address(POOL_MANAGER), ownerSlot) == bytes32(0));
        vm.store(address(POOL_MANAGER), ownerSlot, bytes32(uint256(uint160(address(this)))));
    }
}

contract BasicUniswapV4UnitTest is BaseUniswapV4UnitTest, IUnlockCallback {
    function unlockCallback(bytes calldata) external view override returns (bytes memory) {
        assert(msg.sender == address(POOL_MANAGER));
        return unicode"Hello, World!";
    }

    function setUp() public {
        _deployPoolManager();
    }

    function testNothing() public {
        assertEq(
            keccak256(POOL_MANAGER.unlock(new bytes(0))),
            0xacaf3289d7b601cbd114fb36c4d29c85bbfd5e133f14cb355c3fd8d99367964f
        );
    }
}

library CompatPoolIdLibrary {
    function toIdCompat(PoolKey memory poolKey) internal pure returns (PoolId result) {
        uint256 freePtr;
        assembly ("memory-safe") {
            freePtr := mload(0x40)
        }
        PoolKey memory poolKeyCopy = PoolKey({
            currency0: poolKey.currency0,
            currency1: poolKey.currency1,
            fee: poolKey.fee,
            tickSpacing: poolKey.tickSpacing,
            hooks: poolKey.hooks
        });
        if (poolKeyCopy.currency0 == Currency.wrap(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE)) {
            poolKeyCopy.currency0 = Currency.wrap(address(0));
        }
        result = poolKeyCopy.toId();
        assembly ("memory-safe") {
            mstore(0x40, freePtr)
        }
    }
}

contract UniswapV4BoundedInvariantTest is BaseUniswapV4UnitTest, IUnlockCallback, InvariantAssume {
    using CompatPoolIdLibrary for PoolKey;
    using StateLibrary for IPoolManager;
    using SafeTransferLib for IERC20;

    IERC20[] internal tokens;
    mapping(IERC20 => bool) internal isToken;
    PoolKey[] internal pools;
    mapping(PoolId => bool) internal isPool;

    address internal constant ETH = 0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE;

    receive() external payable {}

    function pushToken() public returns (IERC20 token, uint256 i) {
        disableInvariantAssume();
        token = IERC20(address(new TestERC20()));
        i = tokens.length;
        isToken[token] = true;
        tokens.push(token);
        token.approve(address(stub), type(uint256).max);
        excludeContract(address(token));
    }

    uint128 internal constant _DEFAULT_LIQUIDITY = 5421214632141316;

    function _calculateAmounts(uint160 sqrtPriceX96, uint128 liquidity, int24 tickLo, int24 tickHi)
        private
        pure
        returns (IPoolManager.ModifyLiquidityParams memory params, uint256 amount0, uint256 amount1)
    {
        params.tickLower = tickLo;
        params.tickUpper = tickHi;
        params.liquidityDelta = int128(liquidity);
        int24 tick = TickMath.getTickAtSqrtPrice(sqrtPriceX96);
        assertGe(tick, params.tickLower);
        assertLe(tick, params.tickUpper);
        if (tick == params.tickUpper) {
            // amount0 = 0;
            amount1 = SqrtPriceMath.getAmount1Delta(
                TickMath.getSqrtPriceAtTick(params.tickLower),
                TickMath.getSqrtPriceAtTick(params.tickUpper),
                liquidity,
                true
            );
        } else {
            amount0 = SqrtPriceMath.getAmount0Delta(
                sqrtPriceX96, TickMath.getSqrtPriceAtTick(params.tickUpper), liquidity, true
            );
            amount1 = SqrtPriceMath.getAmount1Delta(
                TickMath.getSqrtPriceAtTick(params.tickLower), sqrtPriceX96, liquidity, true
            );
        }
    }

    function _calculateAmounts(uint160 sqrtPriceX96, uint128 liquidity, int24 tickSpacing)
        private
        pure
        returns (IPoolManager.ModifyLiquidityParams memory params, uint256 amount0, uint256 amount1)
    {
        int24 tickLo = TickMath.MIN_TICK - TickMath.MIN_TICK % tickSpacing;
        int24 tickHi = TickMath.MAX_TICK - TickMath.MAX_TICK % tickSpacing;
        return _calculateAmounts(sqrtPriceX96, liquidity, tickLo, tickHi);
    }

    function testCalculateAmounts() public pure {
        uint160 sqrtPriceX96 = TickMath.MIN_SQRT_PRICE;
        (, uint256 amount0, uint256 amount1) =
            _calculateAmounts(sqrtPriceX96, _DEFAULT_LIQUIDITY, TickMath.MIN_TICK_SPACING);
        assertEq(amount1, 0);
        (, uint256 amount0Hi, uint256 amount1Hi) =
            _calculateAmounts(sqrtPriceX96, _DEFAULT_LIQUIDITY + 1, TickMath.MIN_TICK_SPACING);
        assertEq(amount1Hi, 0);
        assertLe(amount0, TOTAL_SUPPLY / 10);
        assertGt(amount0Hi, TOTAL_SUPPLY / 10);
    }

    function unlockCallback(bytes calldata data) external override returns (bytes memory) {
        assert(msg.sender == address(POOL_MANAGER));
        PoolKey memory poolKey = pools[pools.length - 1];
        if (Currency.unwrap(poolKey.currency0) == ETH) {
            poolKey.currency0 = Currency.wrap(address(0));

        }

        IPoolManager.ModifyLiquidityParams memory params;
        uint256 amount0;
        uint256 amount1;
        if (data.length == 128) {
            (uint160 sqrtPriceX96, uint128 liquidity, int24 tickLo, int24 tickHi) = abi.decode(data, (uint160, uint128, int24, int24));
            (params, amount0, amount1) = _calculateAmounts(sqrtPriceX96, liquidity, tickLo, tickHi);
        } else {
            assert(data.length == 64);
            (uint160 sqrtPriceX96, int24 tickSpacing) = abi.decode(data, (uint160, int24));
            (params, amount0, amount1) = _calculateAmounts(sqrtPriceX96, _DEFAULT_LIQUIDITY, tickSpacing);
        }

        (BalanceDelta callerDelta, BalanceDelta feesAccrued) =
            IPoolManager(address(POOL_MANAGER)).modifyLiquidity(poolKey, params, new bytes(0));

        assertEq(BalanceDelta.unwrap(feesAccrued), 0);
        assertEq(uint128(-callerDelta.amount0()), amount0);
        assertEq(uint128(-callerDelta.amount1()), amount1);

        if (amount0 != 0) {
            if (Currency.unwrap(poolKey.currency0) == address(0)) {
                POOL_MANAGER.settle{value: amount0}();
            } else {
                IERC20 token0 = IERC20(Currency.unwrap(poolKey.currency0));
                POOL_MANAGER.sync(token0);
                token0.safeTransfer(address(POOL_MANAGER), amount0);
                POOL_MANAGER.settle();
            }
        }
        if (amount1 != 0) {
            IERC20 token1 = IERC20(Currency.unwrap(poolKey.currency1));
            POOL_MANAGER.sync(token1);
            token1.safeTransfer(address(POOL_MANAGER), amount1);
            POOL_MANAGER.settle();
        }

        return new bytes(0);
    }

    function _sortTokens(IERC20 token0, IERC20 token1) private pure returns (IERC20, IERC20) {
        assertNotEq(address(token0), address(token1));
        if (token0 == IERC20(ETH)) {
            return (token0, token1);
        } else if (token1 == IERC20(ETH)) {
            return (token1, token0);
        } else if (token0 > token1) {
            return (token1, token0);
        } else {
            return (token0, token1);
        }
    }

    function _pushPoolRaw(
        uint256 tokenAIndex,
        uint256 tokenBIndex,
        uint24 fee,
        int24 tickSpacing,
        uint160 sqrtPriceX96,
        bool skipChecks
    ) private {
        (IERC20 token0, IERC20 token1) = _sortTokens(tokens[tokenAIndex], tokens[tokenBIndex]);
        if (!skipChecks) {
            invariantAssume(tokenAIndex != tokenBIndex);
            invariantAssume(_balanceOf(token0, address(this)) > TOTAL_SUPPLY / 10);
            invariantAssume(_balanceOf(token1, address(this)) > TOTAL_SUPPLY / 10);
        }

        PoolKey memory poolKey = PoolKey({
            currency0: Currency.wrap(address(token0)),
            currency1: Currency.wrap(address(token1)),
            fee: fee,
            tickSpacing: tickSpacing,
            hooks: IHooks(address(0))
        });
        PoolId poolId = poolKey.toIdCompat();
        if (!skipChecks) {
            invariantAssume(!isPool[poolId]);
        }

        disableInvariantAssume();
        isPool[poolId] = true;
        pools.push(poolKey);

        if (Currency.unwrap(poolKey.currency0) == ETH) {
            poolKey.currency0 = Currency.wrap(address(0));
        }
        IPoolManager(address(POOL_MANAGER)).initialize(poolKey, sqrtPriceX96, new bytes(0));
        POOL_MANAGER.unlock(abi.encode(sqrtPriceX96, tickSpacing));
    }

    function _pushPoolRaw(uint256 tokenAIndex, uint256 tokenBIndex, uint24 fee, int24 tickSpacing, uint160 sqrtPriceX96)
        private
    {
        return _pushPoolRaw(tokenAIndex, tokenBIndex, fee, tickSpacing, sqrtPriceX96, false);
    }

    function pushPool(uint256 tokenAIndex, uint256 tokenBIndex, uint24 fee, int24 tickSpacing, uint160 sqrtPriceX96)
        public
    {
        (tokenAIndex, tokenBIndex) =
            (bound(tokenAIndex, 0, tokens.length - 1), bound(tokenBIndex, 0, tokens.length - 1));
        invariantAssume(tokenAIndex != tokenBIndex);
        fee = uint24(bound(fee, 0, 1_000_000));
        tickSpacing = int24(bound(tickSpacing, TickMath.MIN_TICK_SPACING, TickMath.MAX_TICK_SPACING));
        {
            int24 initialTickLowerLimit = TickMath.MIN_TICK / 2;
            initialTickLowerLimit -= initialTickLowerLimit % tickSpacing;
            int24 initialTickUpperLimit = TickMath.MAX_TICK / 2;
            initialTickUpperLimit -= initialTickUpperLimit % tickSpacing;
            sqrtPriceX96 = uint160(
                bound(
                    sqrtPriceX96,
                    TickMath.getSqrtPriceAtTick(initialTickLowerLimit),
                    TickMath.getSqrtPriceAtTick(initialTickUpperLimit)
                )
            );
        }

        _pushPoolRaw(tokenAIndex, tokenBIndex, fee, tickSpacing, sqrtPriceX96);
    }

    function testPushPool() external {
        (, uint256 tokenAIndex) = pushToken();
        (, uint256 tokenBIndex) = pushToken();
        uint24 fee = 0;
        int24 tickSpacing = TickMath.MIN_TICK_SPACING;
        uint160 sqrtPriceX96 = TickMath.MIN_SQRT_PRICE;
        _pushPoolRaw(tokenAIndex, tokenBIndex, fee, tickSpacing, sqrtPriceX96, true);
    }

    function testPushPoolEth() external {
        uint256 tokenAIndex = 0;
        (, uint256 tokenBIndex) = pushToken();
        uint24 fee = 0;
        int24 tickSpacing = TickMath.MIN_TICK_SPACING;
        uint160 sqrtPriceX96 = TickMath.MIN_SQRT_PRICE;
        uint256 ethBefore = address(this).balance;
        _pushPoolRaw(tokenAIndex, tokenBIndex, fee, tickSpacing, sqrtPriceX96, true);
        uint256 ethAfter = address(this).balance;
        assertLt(ethAfter, ethBefore);
    }

    function _balanceOf(IERC20 token, address who) internal view returns (uint256) {
        try this.getBalanceOf(token, who) {}
        catch (bytes memory returndata) {
            return abi.decode(returndata, (uint256));
        }
        revert();
    }

    function getBalanceOf(IERC20 token, address who) external view {
        uint256 result;
        if (token == IERC20(ETH)) {
            result = who.balance;
        } else {
            result = token.balanceOf(who);
        }
        assembly ("memory-safe") {
            mstore(0x00, result)
            revert(0x00, 0x20)
        }
    }

    function _slot0(PoolId poolId)
        internal
        view
        returns (uint160 sqrtPriceX96, int24 tick, uint24 protocolFee, uint24 lpFee)
    {
        try this.getSlot0(poolId) {}
        catch (bytes memory returndata) {
            return abi.decode(returndata, (uint160, int24, uint24, uint24));
        }
        revert();
    }

    function getSlot0(PoolId poolId) external view {
        (uint160 sqrtPriceX96, int24 tick, uint24 protocolFee, uint24 lpFee) =
            IPoolManager(address(POOL_MANAGER)).getSlot0(poolId);
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            mstore(ptr, sqrtPriceX96)
            mstore(add(0x20, ptr), tick)
            mstore(add(0x40, ptr), protocolFee)
            mstore(add(0x60, ptr), lpFee)
            revert(ptr, 0x80)
        }
    }

    function _swapPre(uint256 poolIndex, uint256 sellAmount, bool feeOnTransfer, bool zeroForOne)
        private
        view
        returns (uint256, uint256, PoolKey memory, IERC20, IERC20, uint256, uint256, uint256, uint256, uint256)
    {
        poolIndex = bound(poolIndex, 0, pools.length - 1);
        PoolKey memory poolKey = pools[poolIndex];
        PoolId poolId = poolKey.toIdCompat();
        (IERC20 sellToken, IERC20 buyToken) = zeroForOne
            ? (IERC20(Currency.unwrap(poolKey.currency0)), IERC20(Currency.unwrap(poolKey.currency1)))
            : (IERC20(Currency.unwrap(poolKey.currency1)), IERC20(Currency.unwrap(poolKey.currency0)));
        invariantAssume(!(sellToken == IERC20(ETH) && feeOnTransfer));

        uint256 sellTokenBalanceBefore = _balanceOf(sellToken, address(this));
        uint256 buyTokenBalanceBefore = _balanceOf(buyToken, address(this));
        {
            uint256 maxSell = sellTokenBalanceBefore;
            if (maxSell > 1_000_000 ether) {
                maxSell = 1_000_000 ether;
            }
            (uint160 sqrtPriceCurrentX96,,,) = _slot0(poolId);
            uint160 sqrtPriceNextX96 = SqrtPriceMath.getNextSqrtPriceFromOutput(
                sqrtPriceCurrentX96, _DEFAULT_LIQUIDITY, 1_000_000 wei, zeroForOne
            );
            uint256 minSell = zeroForOne
                ? SqrtPriceMath.getAmount0Delta(sqrtPriceNextX96, sqrtPriceCurrentX96, _DEFAULT_LIQUIDITY, true)
                : SqrtPriceMath.getAmount1Delta(sqrtPriceCurrentX96, sqrtPriceNextX96, _DEFAULT_LIQUIDITY, true);
            invariantAssume(maxSell >= minSell);
            sellAmount = bound(sellAmount, minSell, maxSell);
        }

        uint256 hashMul = 1;
        uint256 hashMod = 8;

        return (
            poolIndex,
            sellAmount,
            poolKey,
            sellToken,
            buyToken,
            sellAmount,
            sellTokenBalanceBefore,
            buyTokenBalanceBefore,
            hashMul,
            hashMod
        );
    }

    function _swapPost(
        IERC20 sellToken,
        IERC20 buyToken,
        uint256 sellTokenBalanceBefore,
        uint256 buyTokenBalanceBefore,
        address _stub
    ) private view returns (uint256, uint256) {
        uint256 sellTokenBalanceAfter = _balanceOf(sellToken, address(this));
        uint256 buyTokenBalanceAfter = _balanceOf(buyToken, address(this));

        assertLt(sellTokenBalanceAfter, sellTokenBalanceBefore);
        assertGt(buyTokenBalanceAfter, buyTokenBalanceBefore);
        assertEq(_balanceOf(sellToken, _stub), 0);
        assertEq(_balanceOf(buyToken, _stub), 0);

        return (sellTokenBalanceAfter, buyTokenBalanceAfter);
    }

    function swapSingle(
        uint256 poolIndex,
        uint256 sellAmount,
        bool feeOnTransfer,
        bool zeroForOne,
        bytes memory hookData
    ) public {
        PoolKey memory poolKey;
        IERC20 sellToken;
        IERC20 buyToken;
        uint256 sellTokenBalanceBefore;
        uint256 buyTokenBalanceBefore;
        uint256 hashMul;
        uint256 hashMod;
        (
            poolIndex,
            sellAmount,
            poolKey,
            sellToken,
            buyToken,
            sellAmount,
            sellTokenBalanceBefore,
            buyTokenBalanceBefore,
            hashMul,
            hashMod
        ) = _swapPre(poolIndex, sellAmount, feeOnTransfer, zeroForOne);

        bytes memory fills = abi.encodePacked(
            uint16(10_000),
            bytes1(0x01),
            buyToken,
            poolKey.fee,
            poolKey.tickSpacing,
            poolKey.hooks,
            uint24(hookData.length),
            hookData
        );

        uint256 value;
        UniswapV4Stub _stub = stub;
        disableInvariantAssume();

        if (sellToken == IERC20(ETH)) {
            value = sellAmount;
        } else {
            // warms sell token and some storage slots; unavoidable
            sellToken.safeTransfer(address(_stub), sellAmount);
        }
        vm.startPrank(address(this), address(this));
        _stub.sellToUniswapV4{value: value}(sellToken, 10_000, feeOnTransfer, hashMul, hashMod, fills, 0);
        vm.stopPrank();

        _swapPost(sellToken, buyToken, sellTokenBalanceBefore, buyTokenBalanceBefore, address(_stub));
    }

    function testSwapSingle() public {
        swapSingle(1, TOTAL_SUPPLY / 1_000, false, true, new bytes(0));
    }

    function swapSingleVIP(
        uint256 poolIndex,
        uint256 sellAmount,
        bool feeOnTransfer,
        bool zeroForOne,
        bytes memory hookData,
        bytes memory sig
    ) public {
        PoolKey memory poolKey;
        IERC20 sellToken;
        IERC20 buyToken;
        uint256 sellTokenBalanceBefore;
        uint256 buyTokenBalanceBefore;
        uint256 hashMul;
        uint256 hashMod;
        (
            poolIndex,
            sellAmount,
            poolKey,
            sellToken,
            buyToken,
            sellAmount,
            sellTokenBalanceBefore,
            buyTokenBalanceBefore,
            hashMul,
            hashMod
        ) = _swapPre(poolIndex, sellAmount, feeOnTransfer, zeroForOne);
        invariantAssume(sellToken != IERC20(ETH));

        ISignatureTransfer.PermitTransferFrom memory permit = ISignatureTransfer.PermitTransferFrom({
            permitted: ISignatureTransfer.TokenPermissions({token: address(sellToken), amount: sellAmount}),
            nonce: uint256(keccak256(sig)),
            deadline: block.timestamp + 30 minutes
        });

        bytes memory fills = abi.encodePacked(
            uint16(10_000),
            bytes1(0x01),
            buyToken,
            poolKey.fee,
            poolKey.tickSpacing,
            poolKey.hooks,
            uint24(hookData.length),
            hookData
        );
        UniswapV4Stub _stub = stub;

        disableInvariantAssume();
        vm.startPrank(address(this), address(this));
        _stub.sellToUniswapV4VIP(feeOnTransfer, hashMul, hashMod, fills, permit, sig, 0);
        vm.stopPrank();

        _swapPost(sellToken, buyToken, sellTokenBalanceBefore, buyTokenBalanceBefore, address(_stub));
    }

    function testSwapSingleVIP() public {
        bytes memory sig = unicode"Hello, World!";
        swapSingleVIP(1, 1_000_001 wei, false, true, new bytes(0), sig);
    }

    function setUp() public {
        assert(address(this) == testPrediction);
        disableInvariantAssume();

        excludeContract(_deployStub());
        assert(address(stub) == stubPrediction);
        excludeContract(_deployPoolManager());
        excludeContract(address(POOL_MANAGER));

        excludeSender(ETH);
        excludeSender(testPrediction);
        excludeSender(stubPrediction);
        excludeSender(address(POOL_MANAGER));
        {
            FuzzSelector memory exclusion = FuzzSelector({addr: address(this), selectors: new bytes4[](9)});
            exclusion.selectors[0] = this.setUp.selector;
            exclusion.selectors[1] = this.getBalanceOf.selector;
            exclusion.selectors[2] = this.getSlot0.selector;
            exclusion.selectors[3] = this.unlockCallback.selector;
            exclusion.selectors[4] = this.testCalculateAmounts.selector;
            exclusion.selectors[5] = this.testPushPool.selector;
            exclusion.selectors[6] = this.testPushPoolEth.selector;
            exclusion.selectors[7] = this.testSwapSingle.selector;
            exclusion.selectors[8] = this.testSwapSingleVIP.selector;
            excludeSelector(exclusion);
        }

        vm.deal(address(this), TOTAL_SUPPLY);

        // Make some tokens (making sure to include ETH)
        tokens.push(IERC20(ETH));
        isToken[IERC20(ETH)] = true;
        pushToken();
        pushToken();

        // Make some pools; all 1:1 price
        _pushPoolRaw(0, 1, 0, TickMath.MAX_TICK_SPACING, 1 << 96, true);
        _pushPoolRaw(1, 2, 0, TickMath.MAX_TICK_SPACING, 1 << 96, true);
        _pushPoolRaw(2, 0, 0, TickMath.MAX_TICK_SPACING, 1 << 96, true);
    }

    function invariant_vacuous() external pure {}
}
