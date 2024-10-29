// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";

import {Velodrome} from "src/core/Velodrome.sol";
import {uint512} from "src/utils/512Math.sol";

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

    function k(uint256 x, uint256 x_basis, uint256 y, uint256 y_basis) external pure returns (uint512 memory k_out) {
        _k(k_out, x, x_basis, y, y_basis);
    }

    function new_y(uint256 x, uint256 dx, uint256 x_basis, uint256 y, uint256 y_basis) external view returns (uint256 r) {
        r = _get_y(x, dx, x_basis, y, y_basis);
    }

    function VELODROME_BASIS() external pure returns (uint256) {
        return _VELODROME_TOKEN_BASIS;
    }

    function MAX_BALANCE() external pure returns (uint256) {
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

        dummy.new_y(x, dx, _VELODROME_BASIS, y, _VELODROME_BASIS);
    }

    function testVelodrome_fuzzConvergence(uint256 x, uint256 dx, uint256 y) external view {
        uint256 _VELODROME_BASIS = dummy.VELODROME_BASIS();
        uint256 _MAX_BALANCE = dummy.MAX_BALANCE() * 2 / 3;

        x = bound(x, _VELODROME_BASIS, _MAX_BALANCE);
        y = bound(y, _VELODROME_BASIS, _MAX_BALANCE);
        uint256 max_dx = x * 100;
        if (max_dx > _MAX_BALANCE - x) {
            max_dx = _MAX_BALANCE - x;
        }
        vm.assume(max_dx >= _VELODROME_BASIS);
        dx = bound(dx, _VELODROME_BASIS, max_dx);

        dummy.new_y(x, dx, _VELODROME_BASIS, y, _VELODROME_BASIS);
    }

    function testVelodrome_fuzzKIncrease(uint256 x, uint256 dx, uint256 y) external view {
        uint256 _VELODROME_BASIS = dummy.VELODROME_BASIS();
        uint256 _MAX_BALANCE = dummy.MAX_BALANCE() * 2 / 3;

        x = bound(x, _VELODROME_BASIS, _MAX_BALANCE);
        y = bound(y, _VELODROME_BASIS, _MAX_BALANCE);
        uint256 max_dx = x * 100;
        if (max_dx > _MAX_BALANCE - x) {
            max_dx = _MAX_BALANCE - x;
        }
        vm.assume(max_dx >= _VELODROME_BASIS);
        dx = bound(dx, _VELODROME_BASIS, max_dx);

        uint256 new_y = dummy.new_y(x, dx, _VELODROME_BASIS, y, _VELODROME_BASIS);

        uint512 memory k_before = dummy.k(x, _VELODROME_BASIS, y, _VELODROME_BASIS);
        uint512 memory k_after = dummy.k(x + dx, _VELODROME_BASIS, new_y, _VELODROME_BASIS);
        uint512 memory k_less = dummy.k(x + dx, _VELODROME_BASIS, new_y - 1, _VELODROME_BASIS);
        assertTrue(k_after.ge(k_before));
        assertTrue(k_less.lt(k_before));
    }

    function solidly_ref_k(uint256 x, uint256 y) internal pure returns (uint256) {
        return (x * ((((y * y) / 1e18) * y) / 1e18)) / 1e18 + (((((x * x) / 1e18) * x) / 1e18) * y) / 1e18;
    }

    function velodrome_ref_k(uint256 x, uint256 y) internal pure returns (uint256) {
        uint256 _a = (x * y) / 1e18;
        uint256 _b = ((x * x) / 1e18 + (y * y) / 1e18);
        return (_a * _b) / 1e18;
    }

    function testVelodrome_fuzzRefVelodrome(uint256 x, uint256 dx, uint8 x_decimals, uint256 y, uint8 y_decimals) external view {
        x_decimals = uint8(bound(x_decimals, 0, 18));
        y_decimals = uint8(bound(y_decimals, 0, 18));
        uint256 x_basis = 10 ** x_decimals;
        uint256 y_basis = 10 ** y_decimals;

        uint256 _VELODROME_BASIS = dummy.VELODROME_BASIS();
        uint256 _MAX_BALANCE = dummy.MAX_BALANCE() * 2 / 3;

        x = bound(x, x_basis, _MAX_BALANCE * x_basis / _VELODROME_BASIS);
        y = bound(y, y_basis, _MAX_BALANCE * y_basis / _VELODROME_BASIS);
        uint256 max_dx = x * 100;
        if (max_dx > _MAX_BALANCE - x) {
            max_dx = _MAX_BALANCE - x;
        }
        vm.assume(max_dx >= x_basis);
        dx = bound(dx, x_basis, max_dx);

        uint256 new_y = dummy.new_y(x, dx, x_basis, y, y_basis);
        uint256 dy = y - new_y;

        uint256 velodrome_k_before = velodrome_ref_k(x * _VELODROME_BASIS / x_basis, y * _VELODROME_BASIS / y_basis);
        uint256 velodrome_k_after = velodrome_ref_k((x + dx) * _VELODROME_BASIS / x_basis, (y - dy) * _VELODROME_BASIS / y_basis);
        assertGe(velodrome_k_after, velodrome_k_before);
    }

    /*
    function testVelodrome_fuzzRefSolidly(uint256 x, uint256 dx, uint256 y) external view {
        uint256 _MAX_BALANCE = dummy.MAX_BALANCE() * 2 / 3;
        _MAX_BALANCE = dummy.to_compat(_MAX_BALANCE);

        x = bound(x, _VELODROME_BASIS, _MAX_BALANCE);
        y = bound(y, _VELODROME_BASIS, _MAX_BALANCE);
        uint256 max_dx = x * 100;
        if (max_dx > _MAX_BALANCE - x) {
            max_dx = _MAX_BALANCE - x;
        }
        vm.assume(max_dx >= _VELODROME_BASIS);
        dx = bound(dx, _VELODROME_BASIS, max_dx);

        uint256 dy = dummy.to_compat(dummy.dy(dummy.from_compat(x), dummy.from_compat(dx), dummy.from_compat(y)));

        uint256 solidly_k_before = solidly_ref_k(x, y);
        uint256 solidly_k_after = solidly_ref_k(x + dx, y - dy);
        assertGe(solidly_k_after, solidly_k_before);
    }
    */
}
