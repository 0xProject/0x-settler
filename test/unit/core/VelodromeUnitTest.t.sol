// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";

import {Velodrome} from "src/core/Velodrome.sol";

import {Test} from "forge-std/Test.sol";

abstract contract VelodromeStub is Velodrome {
    function _msgSender() internal pure override returns (address) {
        revert("unimplemented");
    }

    function _msgData() internal pure override returns (bytes calldata) {
        revert("unimplemented");
    }

    function _isForwarded() internal pure override returns (bool) {
        revert("unimplemented");
    }

    function _hasMetaTxn() internal pure override returns (bool) {
        revert("unimplemented");
    }

    function _dispatch(uint256, bytes4, bytes calldata) internal pure override returns (bool) {
        revert("unimplemented");
    }

    function _isRestrictedTarget(address) internal pure override returns (bool) {
        revert("unimplemented");
    }

    function _operator() internal pure override returns (address) {
        revert("unimplemented");
    }

    function _permitToSellAmountCalldata(ISignatureTransfer.PermitTransferFrom calldata)
        internal
        pure
        override
        returns (uint256)
    {
        revert("unimplemented");
    }

    function _permitToSellAmount(ISignatureTransfer.PermitTransferFrom memory)
        internal
        pure
        override
        returns (uint256)
    {
        revert("unimplemented");
    }

    function _permitToTransferDetails(ISignatureTransfer.PermitTransferFrom memory, address)
        internal
        pure
        override
        returns (ISignatureTransfer.SignatureTransferDetails memory, uint256)
    {
        revert("unimplemented");
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
        ISignatureTransfer.PermitTransferFrom memory,
        ISignatureTransfer.SignatureTransferDetails memory,
        bytes memory,
        bool
    ) internal pure override {
        revert("unimplemented");
    }

    function _transferFrom(
        ISignatureTransfer.PermitTransferFrom memory,
        ISignatureTransfer.SignatureTransferDetails memory,
        bytes memory
    ) internal pure override {
        revert("unimplemented");
    }

    function _setOperatorAndCall(
        address,
        bytes memory,
        uint32,
        function (bytes calldata) internal returns (bytes memory)
    ) internal pure override returns (bytes memory) {
        revert("unimplemented");
    }

    modifier metaTx(address, bytes32) override {
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


contract VelodromeDebug is Test, VelodromeStub {
    uint256 sellBasis;
    uint256 buyBasis;
    uint256 sellReserve;
    uint256 buyReserve;

    function setUp() external {
        (sellBasis, buyBasis, sellReserve, buyReserve) = (1 ether, 1 ether, 698615693324774, 1388675884925384);
    }

    function testInfusionExample() external {
        uint256 buyAmountExpected = 1388675882582425; // computed by hand
        uint256 sellAmount = 1000000000000000000;
        uint256 feeBps = 5;

        uint256 x = sellReserve * 1 ether / sellBasis;
        uint256 y = buyReserve * 1 ether / buyBasis;
        uint256 k = _k(x, y);

        // Credit the buy amount to the reserve; this simulates the transfer from Settler to the pool
        x += sellAmount - sellAmount * feeBps / 10_000;

        // Sanity checks that the hand-computed amount is precisely the optimal buy amount
        assertGe(_k(x, y - buyAmountExpected), k);
        assertLt(_k(x, y - buyAmountExpected - 1), k);

        // Compute the buy amount using Settler's code
        uint256 buyAmountActual = y - _get_y(x, k, y);

        assertEq(buyAmountActual, buyAmountExpected);
    }
}
