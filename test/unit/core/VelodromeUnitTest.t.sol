// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";

import {Velodrome} from "src/core/Velodrome.sol";

import {Test} from "@forge-std/Test.sol";

contract VelodromeConvergenceDummy is Velodrome {
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

    function _dispatch(uint256, uint256, bytes calldata) internal pure override returns (bool) {
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

    function get_y(uint256 x, uint256 dx, uint256 y) external pure returns (uint256 dy) {
        return y - _get_y(x, dx, y);
    }

    function k(uint256 x, uint256 y) external pure returns (uint256) {
        return _k(x, y);
    }

    function VELODROME_BASIS() external pure returns (uint256) {
        return _VELODROME_TOKEN_BASIS;
    }

    function VELODROME_MAX_BALANCE() external pure returns (uint256) {
        return _VELODROME_MAX_BALANCE;
    }
}

contract VelodromeUnitTest is Test {
    VelodromeConvergenceDummy private dummy;

    function setUp() external {
        dummy = new VelodromeConvergenceDummy();
    }

    function testVelodrome_convergence() external view {
        uint256 x_basis = 1000000000000000000;
        uint256 y_basis = 1000000;
        uint256 x_reserve = 3294771369917525;
        uint256 y_reserve = 25493740;
        uint256 x_transfer = 24990000000000;

        uint256 fee_bps = 5;
        uint256 _FEE_BASIS = 10_000;
        uint256 _VELODROME_BASIS = dummy.VELODROME_BASIS();

        uint256 dx = x_transfer;
        dx -= dx * fee_bps / _FEE_BASIS;
        dx *= _VELODROME_BASIS;
        dx /= x_basis;
        uint256 x = x_reserve * _VELODROME_BASIS / x_basis;
        uint256 y = y_reserve * _VELODROME_BASIS / y_basis;

        dummy.get_y(x, dx, y);
    }

    function testVelodrome_fuzzConvergence(uint256 x, uint256 dx, uint256 y) external view {
        uint256 _VELODROME_BASIS = dummy.VELODROME_BASIS();
        uint256 _VELODROME_MAX_BALANCE = dummy.VELODROME_MAX_BALANCE() / 2;

        x = bound(x, _VELODROME_BASIS, _VELODROME_MAX_BALANCE);
        y = bound(y, _VELODROME_BASIS, _VELODROME_MAX_BALANCE);
        uint256 max_dx = x * 10;
        if (max_dx > _VELODROME_MAX_BALANCE - x) {
            max_dx = _VELODROME_MAX_BALANCE - x;
        }
        vm.assume(max_dx >= _VELODROME_BASIS);
        dx = bound(dx, _VELODROME_BASIS, max_dx);

        uint256 k = dummy.k(x, y);
        assertGe(k, _VELODROME_BASIS);
        uint256 dy = dummy.get_y(x, dx, y);

        assertGe(dummy.k(x + dx, y - dy), k);
        assertLt(dummy.k(x + dx, y - dy - 1), k);
    }
}
