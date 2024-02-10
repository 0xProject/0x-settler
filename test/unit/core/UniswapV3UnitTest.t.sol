// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {UniswapV3, IUniswapV3Pool} from "src/core/UniswapV3.sol";
import {Permit2Payment} from "src/core/Permit2Payment.sol";
import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";
import {AddressDerivation} from "src/utils/AddressDerivation.sol";

import {IAllowanceHolder} from "src/allowanceholder/IAllowanceHolder.sol";

import {Utils} from "../Utils.sol";
import {IERC20} from "src/IERC20.sol";

import {Test} from "forge-std/Test.sol";

contract UniswapV3Dummy is Permit2Payment, UniswapV3 {
    constructor(address uniFactory, bytes32 poolInit, address permit2, address allowanceHolder)
        UniswapV3(uniFactory, poolInit)
        Permit2Payment(permit2, allowanceHolder)
    {}

    function sellTokenForTokenSelf(address recipient, bytes memory encodedPath, uint256 bips, uint256 minBuyAmount)
        external
        returns (uint256)
    {
        return super.sellTokenForTokenToUniswapV3(recipient, encodedPath, bips, minBuyAmount);
    }

    function sellTokenForToken(
        address recipient,
        bytes memory encodedPath,
        uint256 sellAmount,
        uint256 minBuyAmount,
        address payer,
        ISignatureTransfer.PermitTransferFrom memory permit,
        bytes memory sig
    ) external returns (uint256) {
        return super.sellTokenForTokenToUniswapV3(recipient, encodedPath, sellAmount, minBuyAmount, payer, permit, sig);
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
        msg.sender.call(abi.encodeWithSelector(UniswapV3.uniswapV3SwapCallback.selector, int256(1), int256(1), data));
        return RETURN_DATA;
    }
}

contract UniswapV3UnitTest is Utils, Test {
    UniswapV3Dummy uni;
    address UNI_FACTORY = _createNamedRejectionDummy("UNI_FACTORY");
    address PERMIT2 = _createNamedRejectionDummy("PERMIT2");
    address ALLOWANCE_HOLDER = _createNamedRejectionDummy("ALLOWANCE_HOLDER");

    address TOKEN0 = _createNamedRejectionDummy("TOKEN0");
    address TOKEN1 = _createNamedRejectionDummy("TOKEN1");
    address TOKEN2 = _createNamedRejectionDummy("TOKEN2");
    address RECIPIENT = _createNamedRejectionDummy("RECIPIENT");

    address POOL;

    constructor() {
        address token0 = TOKEN0;
        address token1 = TOKEN1;
        (token0, token1) = token0 < token1 ? (token0, token1) : (token1, token0);
        uint24 fee = 500;
        POOL = _etchNamedRejectionDummy(
            "POOL",
            AddressDerivation.deriveDeterministicContract(
                UNI_FACTORY, keccak256(abi.encode(token0, token1, fee)), keccak256(abi.encodePacked("POOL_INIT"))
            )
        );
    }

    function setUp() public {
        uni = new UniswapV3Dummy(UNI_FACTORY, keccak256(abi.encodePacked("POOL_INIT")), PERMIT2, ALLOWANCE_HOLDER);
    }

    function testUniswapV3SellSelfFunded() public {
        uint256 bips = 10_000;
        uint256 amount = 99999;
        uint256 minBuyAmount = amount;

        bytes memory data = abi.encodePacked(TOKEN0, uint24(500), TOKEN1);

        _mockExpectCall(TOKEN0, abi.encodeWithSelector(IERC20.balanceOf.selector, address(uni)), abi.encode(amount));
        bool zeroForOne = TOKEN0 < TOKEN1;
        _mockExpectCall(
            POOL,
            abi.encodeWithSelector(
                IUniswapV3Pool.swap.selector,
                RECIPIENT,
                zeroForOne,
                amount,
                zeroForOne ? 4295128740 : 1461446703485210103287273052203988822378723970341,
                abi.encodePacked(TOKEN0, uint24(500), TOKEN1, address(uni))
            ),
            abi.encode(zeroForOne ? int256(0) : -int256(amount), zeroForOne ? -int256(amount) : int256(0))
        );

        uni.sellTokenForTokenSelf(RECIPIENT, data, bips, minBuyAmount);
    }

    function testUniswapV3SellSlippage() public {
        uint256 bips = 10_000;
        uint256 amount = 99999;
        uint256 minBuyAmount = amount + 1;

        bytes memory data = abi.encodePacked(TOKEN0, uint24(500), TOKEN1);

        _mockExpectCall(TOKEN0, abi.encodeWithSelector(IERC20.balanceOf.selector, address(uni)), abi.encode(amount));
        bool zeroForOne = TOKEN0 < TOKEN1;
        _mockExpectCall(
            POOL,
            abi.encodeWithSelector(
                IUniswapV3Pool.swap.selector,
                RECIPIENT,
                zeroForOne,
                amount,
                zeroForOne ? 4295128740 : 1461446703485210103287273052203988822378723970341,
                abi.encodePacked(TOKEN0, uint24(500), TOKEN1, address(uni))
            ),
            abi.encode(zeroForOne ? int256(0) : -int256(amount), zeroForOne ? -int256(amount) : int256(0))
        );

        vm.expectRevert(
            abi.encodeWithSignature("TooMuchSlippage(address,uint256,uint256)", TOKEN1, minBuyAmount, amount)
        );
        uni.sellTokenForTokenSelf(RECIPIENT, data, bips, minBuyAmount);
    }

    function testUniswapV3SellPermit2() public {
        uint256 amount = 99999;
        uint256 minBuyAmount = amount;

        bytes memory data = abi.encodePacked(TOKEN0, uint24(500), TOKEN1);
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
            ISignatureTransfer.SignatureTransferDetails({to: POOL, requestedAmount: amount});

        // permitTransferFrom(((address,uint256),uint256,uint256),(address,uint256),address,bytes) 30f28b7a
        // cannot use abi.encodeWithSelector due to the selector overload and ambiguity
        _mockExpectCall(
            PERMIT2,
            abi.encodeWithSelector(bytes4(0x30f28b7a), permitTransfer, transferDetails, address(this), hex"deadbeef"),
            new bytes(0)
        );

        uni.sellTokenForToken(RECIPIENT, data, amount, minBuyAmount, address(this), permitTransfer, hex"deadbeef");
    }

    function testUniswapV3SellAllowanceHolder() public {
        uint256 amount = 99999;
        uint256 minBuyAmount = amount;

        bytes memory data = abi.encodePacked(TOKEN0, uint24(500), TOKEN1);
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
            deadline: 0
        });

        _mockExpectCall(
            ALLOWANCE_HOLDER,
            abi.encodeCall(IAllowanceHolder.transferFrom, (TOKEN0, address(this), POOL, amount)),
            abi.encode(true)
        );

        vm.prank(ALLOWANCE_HOLDER);
        address(uni).call(
            abi.encodePacked(
                abi.encodeCall(
                    uni.sellTokenForToken, (RECIPIENT, data, amount, minBuyAmount, address(this), permitTransfer, hex"")
                ),
                address(this)
            ) // Forward on true msg.sender
        );
        // uni.sellTokenForToken(RECIPIENT, data, amount, minBuyAmount, address(this), permitTransfer, hex"");
    }
}
