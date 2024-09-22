// SPDX-License-Identifier: GPL-2.0-or-later
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
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

import {SignatureExpired} from "src/core/SettlerErrors.sol";
import {Panic} from "src/utils/Panic.sol";
import {Revert} from "src/utils/Revert.sol";

import {ERC20} from "@solmate/tokens/ERC20.sol";

import {Test} from "@forge-std/Test.sol";
import {StdInvariant} from "@forge-std/StdInvariant.sol";
import {Vm} from "@forge-std/Vm.sol";

import {console} from "@forge-std/console.sol";

uint256 constant TOTAL_SUPPLY = 1 ether * 1 ether;

contract TestERC20 is ERC20 {
    using ItoA for uint256;

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
}

contract UniswapV4Stub is UniswapV4 {
    using Revert for bool;

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
        require(bytes4(data) == IPoolManager.unlock.selector);
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
        bytes memory,
        bool isForwarded
    ) internal override {
        assert(!isForwarded);
        if (transferDetails.requestedAmount > permit.permitted.amount) {
            Panic.panic(Panic.ARITHMETIC_OVERFLOW);
        }
        if (permit.deadline < block.timestamp) {
            revert SignatureExpired(permit.deadline);
        }
        assert(permit.nonce == 0);
        IERC20(permit.permitted.token).transferFrom(_msgSender(), transferDetails.to, transferDetails.requestedAmount);
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
        require(selector == uint32(IPoolManager.unlock.selector));
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

    function _deployStub() internal {
        stub = new UniswapV4Stub();
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

contract UniswapV4BoundedInvariantTest is BaseUniswapV4UnitTest, IUnlockCallback {
    using PoolIdLibrary for PoolKey;

    IERC20[] internal tokens;
    mapping(IERC20 => bool) internal isToken;
    PoolKey[] internal pools;
    mapping(PoolId => bool) internal isPool;

    address internal constant ETH = 0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE;

    function pushToken() public returns (IERC20 token, uint256 i) {
        token = IERC20(address(new TestERC20()));
        i = tokens.length;
        isToken[token] = true;
        tokens.push(token);
        token.approve(address(stub), type(uint256).max);
        excludeContract(address(token));
    }

    uint128 internal constant _DEFAULT_LIQUIDITY = 5421214632141316;

    function _calculateAmounts(uint160 sqrtPriceX96, uint128 liquidity) private pure returns (IPoolManager.ModifyLiquidityParams memory params, uint256 amount0, uint256 amount1) {
        params.tickLower = TickMath.MIN_TICK;
        params.tickUpper = TickMath.MAX_TICK;
        params.liquidityDelta = int128(liquidity);
        amount0 = SqrtPriceMath.getAmount0Delta(sqrtPriceX96, TickMath.getSqrtPriceAtTick(params.tickUpper), liquidity, true);
        amount1 = SqrtPriceMath.getAmount1Delta(TickMath.getSqrtPriceAtTick(params.tickLower), sqrtPriceX96, liquidity, true);
    }

    function testCalculateAmounts() public pure {
        uint160 sqrtPriceX96 = TickMath.MIN_SQRT_PRICE;
        (, uint256 amount0, uint256 amount1) = _calculateAmounts(sqrtPriceX96, _DEFAULT_LIQUIDITY);
        assertEq(amount1, 0);
        (, uint256 amount0Hi, uint256 amount1Hi) = _calculateAmounts(sqrtPriceX96, _DEFAULT_LIQUIDITY + 1);
        assertEq(amount1Hi, 0);
        assertLt(amount0, TOTAL_SUPPLY / 10);
        assertGt(amount0Hi, TOTAL_SUPPLY / 10);
    }

    function unlockCallback(bytes calldata data) external override returns (bytes memory) {
        assert(msg.sender == address(POOL_MANAGER));
        uint160 sqrtPriceX96 = abi.decode(data, (uint160));
        PoolKey memory poolKey = pools[pools.length - 1];
        if (Currency.unwrap(poolKey.currency0) == ETH) {
            poolKey.currency0 = Currency.wrap(address(0));
        }

        (IPoolManager.ModifyLiquidityParams memory params, uint256 amount0, uint256 amount1) = _calculateAmounts(sqrtPriceX96, _DEFAULT_LIQUIDITY);
        (BalanceDelta callerDelta, BalanceDelta feesAccrued) = IPoolManager(address(POOL_MANAGER)).modifyLiquidity(poolKey, params, new bytes(0));
        assertEq(uint128(-callerDelta.amount0()), amount0);
        assertEq(uint128(-callerDelta.amount1()), amount1);
        assertEq(BalanceDelta.unwrap(feesAccrued), 0);

        if (Currency.unwrap(poolKey.currency0) == address(0)) {
            POOL_MANAGER.settle{value: amount0}();
        } else {
            IERC20 token0 = IERC20(Currency.unwrap(poolKey.currency0));
            POOL_MANAGER.sync(token0);
            token0.transfer(address(POOL_MANAGER), amount0);
            POOL_MANAGER.settle();
        }
        {
            IERC20 token1 = IERC20(Currency.unwrap(poolKey.currency1));
            POOL_MANAGER.sync(token1);
            token1.transfer(address(POOL_MANAGER), amount1);
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

    function _pushPoolRaw(uint256 tokenAIndex, uint256 tokenBIndex, uint24 fee, int24 tickSpacing, uint160 sqrtPriceX96) private {
        vm.assume(tokenAIndex != tokenBIndex);
        (IERC20 token0, IERC20 token1) = _sortTokens(tokens[tokenAIndex], tokens[tokenBIndex]);
        vm.assume(_balanceOf(token0) > TOTAL_SUPPLY / 10);
        vm.assume(_balanceOf(token1) > TOTAL_SUPPLY / 10);

        PoolKey memory poolKey = PoolKey({
            currency0: Currency.wrap(address(token0)),
            currency1: Currency.wrap(address(token1)),
            fee: fee,
            tickSpacing: tickSpacing,
            hooks: IHooks(address(0))
        });
        PoolId poolId = poolKey.toId();
        vm.assume(!isPool[poolId]);
        isPool[poolId] = true;
        pools.push(poolKey);

        if (Currency.unwrap(poolKey.currency0) == ETH) {
            poolKey.currency0 = Currency.wrap(address(0));
        }
        IPoolManager(address(POOL_MANAGER)).initialize(poolKey, sqrtPriceX96, new bytes(0));
        POOL_MANAGER.unlock(abi.encode(sqrtPriceX96));
    }

    function pushPool(uint256 tokenAIndex, uint256 tokenBIndex, uint24 fee, int24 tickSpacing, uint160 sqrtPriceX96)
        public
    {
        (tokenAIndex, tokenBIndex) = (bound(tokenAIndex, 0, tokens.length), bound(tokenBIndex, 0, tokens.length));
        fee = uint24(bound(fee, 0, 1_000_000));
        tickSpacing = int24(bound(tickSpacing, TickMath.MIN_TICK_SPACING, TickMath.MAX_TICK_SPACING));
        sqrtPriceX96 = uint160(bound(sqrtPriceX96, TickMath.MIN_SQRT_PRICE + 1, TickMath.MAX_SQRT_PRICE - 1));

        _pushPoolRaw(tokenAIndex, tokenBIndex, fee, tickSpacing, sqrtPriceX96);
    }

    function testPushPool() external {
        (, uint256 tokenAIndex) = pushToken();
        (, uint256 tokenBIndex) = pushToken();
        uint24 fee = 0;
        int24 tickSpacing = TickMath.MIN_TICK_SPACING;
        uint160 sqrtPriceX96 = TickMath.MIN_SQRT_PRICE;
        _pushPoolRaw(tokenAIndex, tokenBIndex, fee, tickSpacing, sqrtPriceX96);
    }

    function testPushPoolEth() external {
        uint256 tokenAIndex = 0;
        (, uint256 tokenBIndex) = pushToken();
        uint24 fee = 0;
        int24 tickSpacing = TickMath.MIN_TICK_SPACING;
        uint160 sqrtPriceX96 = TickMath.MIN_SQRT_PRICE;
        uint256 ethBefore = address(this).balance;
        _pushPoolRaw(tokenAIndex, tokenBIndex, fee, tickSpacing, sqrtPriceX96);
        uint256 ethAfter = address(this).balance;
        assertLt(ethAfter, ethBefore);
    }

    function _balanceOf(IERC20 token) internal view returns (uint256) {
        if (token == IERC20(ETH)) {
            return address(this).balance;
        }
        try this.getBalanceOf(token) {}
        catch (bytes memory returndata) {
            return abi.decode(returndata, (uint256));
        }
        revert();
    }

    function getBalanceOf(IERC20 token) external view {
        uint256 result = token.balanceOf(address(this));
        assembly ("memory-safe") {
            mstore(0x00, result)
            revert(0x00, 0x20)
        }
    }

    function swapSingle(uint256 poolIndex, uint256 bps, bool feeOnTransfer, bool zeroForOne, bytes calldata hookData) public {
        poolIndex = bound(poolIndex, 0, pools.length);
        bps = bound(bps, 1, 1_000); // up to one tenth
        uint256 hashMul = 0;
        uint256 hashMod = 1;
        PoolKey memory poolKey = pools[poolIndex];
        (IERC20 sellToken, IERC20 buyToken) = zeroForOne
            ? (IERC20(Currency.unwrap(poolKey.currency0)), IERC20(Currency.unwrap(poolKey.currency1)))
            : (IERC20(Currency.unwrap(poolKey.currency1)), IERC20(Currency.unwrap(poolKey.currency0)));

        uint256 sellTokenBalanceBefore = _balanceOf(sellToken);
        uint256 buyTokenBalanceBefore = _balanceOf(buyToken);

        uint256 value;
        if (sellToken == IERC20(ETH)) {
            value = sellTokenBalanceBefore * bps / 10_000;
        }
        UniswapV4Stub _stub = stub;
        vm.startPrank(address(this), address(this));
        _stub.sellToUniswapV4{value: value}(
            sellToken, bps, feeOnTransfer, hashMul, hashMod, new bytes(0)/* TODO: fills */, 0
        );
        vm.stopPrank();

        uint256 sellTokenBalanceAfter = _balanceOf(sellToken);
        uint256 buyTokenBalanceAfter = _balanceOf(buyToken);

        assertLt(sellTokenBalanceAfter, sellTokenBalanceBefore);
        assertGt(buyTokenBalanceAfter, buyTokenBalanceBefore);
    }

    function setUp() public {
        _deployStub();
        excludeContract(address(stub));
        excludeContract(_deployPoolManager());
        excludeContract(address(POOL_MANAGER));

        excludeSender(ETH);
        {
            FuzzSelector memory exclusion = FuzzSelector({addr: address(this), selectors: new bytes4[](5)});
            exclusion.selectors[0] = this.getBalanceOf.selector;
            exclusion.selectors[1] = this.unlockCallback.selector;
            exclusion.selectors[2] = this.testCalculateAmounts.selector;
            exclusion.selectors[3] = this.testPushPool.selector;
            exclusion.selectors[4] = this.testPushPoolEth.selector;
            excludeSelector(exclusion);
        }
        vm.deal(address(this), TOTAL_SUPPLY);

        // Make some tokens (making sure to include ETH)
        tokens.push(IERC20(ETH));
        isToken[IERC20(ETH)] = true;
        pushToken();
        pushToken();

        // Make some pools; all 1:1 price
        _pushPoolRaw(0, 1, 0, 1, 1 << 96);
        _pushPoolRaw(1, 2, 0, 1, 1 << 96);
        _pushPoolRaw(2, 0, 0, 1, 1 << 96);
    }
}
