// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IUniswapV3Pool, UniswapV3Fork} from "src/core/UniswapV3Fork.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {AddressDerivation} from "src/utils/AddressDerivation.sol";
import {AllowanceHolderContext} from "src/allowanceholder/AllowanceHolderContext.sol";
import {uniswapV3InitHash, IUniswapV3Callback} from "src/core/univ3forks/UniswapV3.sol";
import {revertUnknownForkId} from "src/core/SettlerErrors.sol";
import {uint512} from "src/utils/512Math.sol";
import {AbstractContext} from "src/Context.sol";

import {IAllowanceHolder, ALLOWANCE_HOLDER} from "src/allowanceholder/IAllowanceHolder.sol";

import {Utils} from "../Utils.sol";
import {IERC20} from "@forge-std/interfaces/IERC20.sol";

import {Test} from "@forge-std/Test.sol";

ISignatureTransfer constant PERMIT2 = ISignatureTransfer(0x000000000022D473030F116dDEE9F6B43aC78BA3);

contract UniswapV3Dummy is AllowanceHolderContext, UniswapV3Fork {
    address internal immutable uniFactory;
    address private _payer;
    address private _callbackCaller;
    function(bytes calldata) internal returns (bytes memory) private _callback;

    constructor(address _uniFactory) {
        uniFactory = _uniFactory;
    }

    function _tokenId() internal pure override returns (uint256) {
        revert("unimplemented");
    }

    fallback(bytes calldata) external returns (bytes memory) {
        require(_operator() == _callbackCaller);
        bytes calldata data = _msgData();
        require(uint32(bytes4(data)) == uint32(IUniswapV3Callback.uniswapV3SwapCallback.selector));
        function(bytes calldata) internal returns (bytes memory) callback = _callback;
        delete _callback;
        delete _callbackCaller;
        return callback(data[4:]);
    }

    function sellSelf(address recipient, uint256 bps, bytes memory encodedPath, uint256 minBuyAmount)
        external
        takerSubmitted
        returns (uint256)
    {
        return super.sellToUniswapV3(recipient, bps, encodedPath, minBuyAmount);
    }

    function sell(
        address recipient,
        bytes memory encodedPath,
        ISignatureTransfer.PermitTransferFrom memory permit,
        bytes memory sig,
        uint256 minBuyAmount
    ) external takerSubmitted returns (uint256) {
        return super.sellToUniswapV3VIP(recipient, encodedPath, permit, sig, minBuyAmount);
    }

    function _hasMetaTxn() internal pure override returns (bool) {
        return false;
    }

    function _msgSender() internal view override(AbstractContext, AllowanceHolderContext) returns (address payer) {
        require((payer = _payer) != address(0));
    }

    function _operator() internal view override returns (address) {
        return super._msgSender();
    }

    function _dispatch(uint256, uint256, bytes calldata, AllowedSlippage memory) internal pure override returns (bool) {
        revert("unimplemented");
    }

    function _div512to256(uint512, uint512) internal view override returns (uint256) {
        revert("unimplemented");
    }

    function _uniV3ForkInfo(uint8 forkId)
        internal
        view
        override
        returns (address factory, bytes32 initHash, uint32 callbackSelector)
    {
        if (forkId == 0) {
            factory = uniFactory;
            initHash = uniswapV3InitHash;
            callbackSelector = uint32(IUniswapV3Callback.uniswapV3SwapCallback.selector);
        } else {
            revertUnknownForkId(forkId);
        }
    }

    function _isRestrictedTarget(address) internal pure override returns (bool) {
        return false;
    }

    function _permitToSellAmountCalldata(ISignatureTransfer.PermitTransferFrom calldata permit)
        internal
        pure
        override
        returns (uint256)
    {
        return permit.permitted.amount;
    }

    function _permitToSellAmount(ISignatureTransfer.PermitTransferFrom memory permit)
        internal
        pure
        override
        returns (uint256)
    {
        return permit.permitted.amount;
    }

    function _permitToTransferDetails(ISignatureTransfer.PermitTransferFrom memory permit, address recipient)
        internal
        pure
        override
        returns (ISignatureTransfer.SignatureTransferDetails memory transferDetails, uint256 sellAmount)
    {
        transferDetails.to = recipient;
        transferDetails.requestedAmount = sellAmount = permit.permitted.amount;
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
        ISignatureTransfer.PermitTransferFrom memory,
        ISignatureTransfer.SignatureTransferDetails memory,
        address,
        bytes32,
        string memory,
        bytes memory
    ) internal pure override {
        revert("unimplemented");
    }

    function _transferFrom(
        ISignatureTransfer.PermitTransferFrom memory permit,
        ISignatureTransfer.SignatureTransferDetails memory transferDetails,
        bytes memory sig,
        bool isForwarded
    ) internal override {
        if (isForwarded) {
            require(sig.length == 0);
            require(permit.nonce == 0);
            require(block.timestamp <= permit.deadline);
            _allowanceHolderTransferFrom(
                permit.permitted.token, _msgSender(), transferDetails.to, transferDetails.requestedAmount
            );
        } else {
            PERMIT2.permitTransferFrom(permit, transferDetails, _msgSender(), sig);
        }
    }

    function _transferFrom(
        ISignatureTransfer.PermitTransferFrom memory permit,
        ISignatureTransfer.SignatureTransferDetails memory transferDetails,
        bytes memory sig
    ) internal override {
        _transferFrom(permit, transferDetails, sig, _isForwarded());
    }

    function _setOperatorAndCall(
        address target,
        bytes memory data,
        uint32 selector,
        function(bytes calldata) internal returns (bytes memory) callback
    ) internal override returns (bytes memory) {
        _callback = callback;
        _callbackCaller = target;
        require(selector == uint32(IUniswapV3Callback.uniswapV3SwapCallback.selector));
        (bool success, bytes memory returndata) = target.call(data);
        if (!success) {
            assembly ("memory-safe") {
                revert(add(0x20, returndata), mload(returndata))
            }
        }
        return returndata;
    }

    modifier metaTx(address, bytes32) override {
        revert("unimplemented");
        _;
    }

    modifier takerSubmitted() override {
        _payer = _operator();
        _;
        delete _payer;
    }

    function _allowanceHolderTransferFrom(address token, address owner, address recipient, uint256 amount)
        internal
        override
    {
        require(ALLOWANCE_HOLDER.transferFrom(token, owner, recipient, amount));
    }
}

/// @dev We need a dummy to actually call our contract, so it needs an implementation which at the very least
/// calls the `uniswapV3SwapCallback`
contract UniswapV3PoolDummy {
    bytes public RETURN_DATA;

    constructor(bytes memory returnData) {
        RETURN_DATA = returnData;
    }

    fallback(bytes calldata) external payable returns (bytes memory) {
        (,,,, bytes memory data) = abi.decode(msg.data[4:], (address, bool, int256, uint160, bytes));
        msg.sender
            .call(abi.encodeWithSignature("uniswapV3SwapCallback(int256,int256,bytes)", int256(1), int256(1), data));
        return RETURN_DATA;
    }
}

contract UniswapV3PoolDirtyForwardedBoolDummy {
    bytes public RETURN_DATA;

    constructor(bytes memory returnData) {
        RETURN_DATA = returnData;
    }

    fallback(bytes calldata) external payable returns (bytes memory) {
        (,,,, bytes memory data) = abi.decode(msg.data[4:], (address, bool, int256, uint160, bytes));
        data[0x88] = bytes1(uint8(2));

        (bool success, bytes memory returndata) = msg.sender
            .call(abi.encodeWithSignature("uniswapV3SwapCallback(int256,int256,bytes)", int256(1), int256(1), data));
        if (!success) {
            assembly ("memory-safe") {
                revert(add(0x20, returndata), mload(returndata))
            }
        }
        return RETURN_DATA;
    }
}

contract UniswapV3UnitTest is Utils, Test {
    UniswapV3Dummy uni;
    address UNI_FACTORY = _createNamedRejectionDummy("UNI_FACTORY");

    address TOKEN0 = _createNamedRejectionDummy("TOKEN0");
    address TOKEN1 = _createNamedRejectionDummy("TOKEN1");
    address TOKEN2 = _createNamedRejectionDummy("TOKEN2");
    address RECIPIENT = _createNamedRejectionDummy("RECIPIENT");

    address POOL;
    bytes encodedPath;

    constructor() {
        address token0 = TOKEN0;
        address token1 = TOKEN1;
        bool zeroForOne = token0 < token1;
        uint160 sqrtPriceLimitX96 = zeroForOne ? 4295128740 : 1461446703485210103287273052203988822378723970341;
        encodedPath = abi.encodePacked(TOKEN0, uint8(0), uint24(500), sqrtPriceLimitX96, TOKEN1);

        (token0, token1) = zeroForOne ? (token0, token1) : (token1, token0);
        uint24 fee = 500;
        POOL = _etchNamedRejectionDummy(
            "POOL",
            AddressDerivation.deriveDeterministicContract(
                UNI_FACTORY,
                keccak256(abi.encode(token0, token1, fee)),
                0xe34f199b19b2b4f47f68442619d555527d244f78a3297ea89325f843f87b8b54
            )
        );
    }

    function setUp() public {
        _etchNamedRejectionDummy("PERMIT2", address(PERMIT2));
        _etchNamedRejectionDummy("ALLOWANCE_HOLDER", address(ALLOWANCE_HOLDER));
        uni = new UniswapV3Dummy(UNI_FACTORY);
    }

    function testUniswapV3SellSelfFunded() public {
        uint256 bps = 10_000;
        uint256 amount = 99999;
        uint256 minBuyAmount = amount;

        _mockExpectCall(TOKEN0, abi.encodeWithSelector(IERC20.balanceOf.selector, address(uni)), abi.encode(amount));
        bool zeroForOne = TOKEN0 < TOKEN1;

        deployCodeTo(
            "UniswapV3UnitTest.t.sol:UniswapV3PoolDummy",
            abi.encode(abi.encode(zeroForOne ? int256(0) : -int256(amount), zeroForOne ? -int256(amount) : int256(0))),
            POOL
        );
        bytes memory callbackData = abi.encodePacked(address(uni), TOKEN0);
        bytes memory data = bytes.concat(
            abi.encodeWithSelector(
                IUniswapV3Pool.swap.selector,
                RECIPIENT,
                zeroForOne,
                amount,
                zeroForOne ? 4295128740 : 1461446703485210103287273052203988822378723970341
            ),
            bytes32(uint256(0xa0)),
            bytes32(callbackData.length),
            callbackData
        );

        vm.expectCall(POOL, data);
        _mockExpectCall(TOKEN0, abi.encodeCall(IERC20.transfer, (POOL, 1)), abi.encode(true));

        uni.sellSelf(RECIPIENT, bps, encodedPath, minBuyAmount);
    }

    function testUniswapV3SellSlippage() public {
        uint256 bps = 10_000;
        uint256 amount = 99999;
        uint256 minBuyAmount = amount + 1;

        _mockExpectCall(TOKEN0, abi.encodeWithSelector(IERC20.balanceOf.selector, address(uni)), abi.encode(amount));
        bool zeroForOne = TOKEN0 < TOKEN1;

        deployCodeTo(
            "UniswapV3UnitTest.t.sol:UniswapV3PoolDummy",
            abi.encode(abi.encode(zeroForOne ? int256(0) : -int256(amount), zeroForOne ? -int256(amount) : int256(0))),
            POOL
        );

        bytes memory callbackData = abi.encodePacked(address(uni), TOKEN0);
        bytes memory data = bytes.concat(
            abi.encodeWithSelector(
                IUniswapV3Pool.swap.selector,
                RECIPIENT,
                zeroForOne,
                amount,
                zeroForOne ? 4295128740 : 1461446703485210103287273052203988822378723970341
            ),
            bytes32(uint256(0xa0)),
            bytes32(callbackData.length),
            callbackData
        );

        vm.expectCall(POOL, data);
        _mockExpectCall(TOKEN0, abi.encodeCall(IERC20.transfer, (POOL, 1)), abi.encode(true));

        vm.expectRevert(
            abi.encodeWithSignature("TooMuchSlippage(address,uint256,uint256)", TOKEN1, minBuyAmount, amount)
        );
        uni.sellSelf(RECIPIENT, bps, encodedPath, minBuyAmount);
    }

    function testUniswapV3SellPermit2() public {
        uint256 amount = 99999;
        uint256 minBuyAmount = amount;

        // Override the UniswapV3 pool code to callback our contract
        // There's probably a smarter way to do this tbh
        deployCodeTo(
            "UniswapV3UnitTest.t.sol:UniswapV3PoolDummy",
            abi.encode(abi.encodePacked(-int256(amount), -int256(amount))),
            POOL
        );

        ISignatureTransfer.TokenPermissions memory permitted =
            ISignatureTransfer.TokenPermissions({token: TOKEN0, amount: amount});
        ISignatureTransfer.PermitTransferFrom memory permitTransfer =
            ISignatureTransfer.PermitTransferFrom({permitted: permitted, nonce: 0, deadline: 0});
        ISignatureTransfer.SignatureTransferDetails memory transferDetails =
            ISignatureTransfer.SignatureTransferDetails({to: POOL, requestedAmount: 1});

        // permitTransferFrom(((address,uint256),uint256,uint256),(address,uint256),address,bytes) 30f28b7a
        // cannot use abi.encodeWithSelector due to the selector overload and ambiguity
        _mockExpectCall(
            address(PERMIT2),
            bytes.concat(
                abi.encodeWithSelector(
                    bytes4(0x30f28b7a), permitTransfer, transferDetails, address(this), uint256(0x100)
                ),
                abi.encodePacked(uint256(4), hex"deadbeef")
            ),
            new bytes(0)
        );

        uni.sell(RECIPIENT, encodedPath, permitTransfer, hex"deadbeef", minBuyAmount);
    }

    function testUniswapV3SellAllowanceHolder() public {
        uint256 amount = 99999;
        uint256 minBuyAmount = amount;

        // Override the UniswapV3 pool code to callback our contract
        // There's probably a smarter way to do this tbh
        deployCodeTo(
            "UniswapV3UnitTest.t.sol:UniswapV3PoolDummy",
            abi.encode(abi.encodePacked(-int256(amount), -int256(amount))),
            POOL
        );

        ISignatureTransfer.PermitTransferFrom memory permitTransfer = ISignatureTransfer.PermitTransferFrom({
            permitted: ISignatureTransfer.TokenPermissions({token: TOKEN0, amount: amount}),
            nonce: 0,
            deadline: block.timestamp
        });

        _mockExpectCall(
            address(ALLOWANCE_HOLDER),
            abi.encodeCall(IAllowanceHolder.transferFrom, (TOKEN0, address(this), POOL, 1)),
            abi.encode(true)
        );

        vm.prank(address(ALLOWANCE_HOLDER));
        address(uni)
            .call(
                abi.encodePacked(
                    abi.encodeCall(uni.sell, (RECIPIENT, encodedPath, permitTransfer, hex"", minBuyAmount)),
                    address(this) // Forward on true msg.sender
                )
            );
        // uni.sell(RECIPIENT, encodedPath, minBuyAmount, permitTransfer, hex"");
    }

    function testUniswapV3SellPermit2RejectsDirtyForwardedBool() public {
        uint256 amount = 99999;

        deployCodeTo(
            "UniswapV3UnitTest.t.sol:UniswapV3PoolDirtyForwardedBoolDummy",
            abi.encode(abi.encodePacked(-int256(amount), -int256(amount))),
            POOL
        );

        ISignatureTransfer.TokenPermissions memory permitted =
            ISignatureTransfer.TokenPermissions({token: TOKEN0, amount: amount});
        ISignatureTransfer.PermitTransferFrom memory permitTransfer =
            ISignatureTransfer.PermitTransferFrom({permitted: permitted, nonce: 0, deadline: 0});

        vm.expectRevert(bytes(""));
        uni.sell(RECIPIENT, encodedPath, permitTransfer, hex"deadbeef", amount);
    }
}
