// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {UniswapV3, IUniswapV3Pool} from "../../../src/core/UniswapV3.sol";
import {Permit2Payment} from "../../../src/core/Permit2Payment.sol";
import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";

import {IAllowanceHolder} from "../../../src/IAllowanceHolder.sol";

import {Utils} from "../Utils.sol";
import {IERC20} from "../../../src/IERC20.sol";

import {Test} from "forge-std/Test.sol";
import {VmSafe} from "forge-std/Vm.sol";

contract UniswapV3Dummy is UniswapV3, Permit2Payment {
    constructor(address uniFactory, bytes32 poolInit, address permit2, address feeRecipient, address allowanceHolder)
        UniswapV3(uniFactory, poolInit)
        Permit2Payment(permit2, feeRecipient, allowanceHolder)
    {}

    function sellTokenForTokenSelf(address recipient, bytes memory encodedPath, uint256 bips, uint256 minBuyAmount)
        external
        returns (uint256 buyAmount)
    {
        super.sellTokenForTokenToUniswapV3(recipient, encodedPath, bips, minBuyAmount);
    }

    function sellTokenForToken(
        address recipient,
        bytes memory encodedPath,
        uint256 sellAmount,
        uint256 minBuyAmount,
        address payer,
        ISignatureTransfer.PermitTransferFrom memory permit,
        bytes memory sig
    ) external returns (uint256 buyAmount) {
        super.sellTokenForTokenToUniswapV3(recipient, encodedPath, sellAmount, minBuyAmount, payer, permit, sig);
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
    address FEE_RECIPIENT = _createNamedRejectionDummy("FEE_RECIPIENT");
    address ALLOWANCE_HOLDER = _createNamedRejectionDummy("ALLOWANCE_HOLDER");

    address TOKEN0 = _createNamedRejectionDummy("TOKEN0");
    address TOKEN1 = _createNamedRejectionDummy("TOKEN1");
    address TOKEN2 = _createNamedRejectionDummy("TOKEN2");
    address RECIPIENT = _createNamedRejectionDummy("RECIPIENT");

    address POOL = _etchNamedRejectionDummy("POOL", 0x33da22E66cE9c37747B80804c14dCE4a5aBD33a5); // created from TOKEN0/TOKEN1 combo

    function setUp() public {
        uni = new UniswapV3Dummy(
            UNI_FACTORY, keccak256(abi.encodePacked("POOL_INIT")), PERMIT2, FEE_RECIPIENT, ALLOWANCE_HOLDER
        );
    }

    function testUniswapV3SellSelfFunded() public {
        uint256 bips = 10_000;
        uint256 amount = 99999;
        uint256 minBuyAmount = amount;

        bytes memory data = abi.encodePacked(TOKEN0, uint24(500), TOKEN1);

        _mockExpectCall(TOKEN0, abi.encodeWithSelector(IERC20.balanceOf.selector, address(uni)), abi.encode(amount));
        _mockExpectCall(
            POOL,
            abi.encodeWithSelector(
                IUniswapV3Pool.swap.selector,
                RECIPIENT,
                false,
                amount,
                1461446703485210103287273052203988822378723970341,
                abi.encodePacked(TOKEN1, uint24(500), TOKEN0, address(uni)) /* token1 and token0 swapped due to univ3 ordering */
            ),
            abi.encode(-int256(amount), 0)
        );

        uni.sellTokenForTokenSelf(RECIPIENT, data, bips, minBuyAmount);
    }

    function testUniswapV3SellSlippage() public {
        uint256 bips = 10_000;
        uint256 amount = 99999;
        uint256 minBuyAmount = amount + 1;

        bytes memory data = abi.encodePacked(TOKEN0, uint24(500), TOKEN1);

        _mockExpectCall(TOKEN0, abi.encodeWithSelector(IERC20.balanceOf.selector, address(uni)), abi.encode(amount));
        _mockExpectCall(
            POOL,
            abi.encodeWithSelector(
                IUniswapV3Pool.swap.selector,
                RECIPIENT,
                false,
                amount,
                1461446703485210103287273052203988822378723970341,
                abi.encodePacked(TOKEN1, uint24(500), TOKEN0, address(uni)) /* token1 and token0 swapped due to univ3 ordering */
            ),
            abi.encode(-int256(amount), 0)
        );

        vm.expectRevert();
        uni.sellTokenForTokenSelf(RECIPIENT, data, bips, minBuyAmount);
    }

    function testUniswapV3SellPermit2() public {
        uint256 bips = 10_000;
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
        uint256 bips = 10_000;
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

        IAllowanceHolder.TransferDetails[] memory transferDetails = new IAllowanceHolder.TransferDetails[](1);
        transferDetails[0] = IAllowanceHolder.TransferDetails({token: TOKEN0, recipient: POOL, amount: amount});

        _mockExpectCall(
            ALLOWANCE_HOLDER,
            abi.encodeCall(IAllowanceHolder.holderTransferFrom, (address(this), transferDetails)),
            abi.encode(true)
        );

        vm.prank(ALLOWANCE_HOLDER);
        uni.sellTokenForToken(RECIPIENT, data, amount, minBuyAmount, address(this), permitTransfer, hex"");
    }
}
