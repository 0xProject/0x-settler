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

    function k(uint256 x, uint256 y) external pure returns (uint256) {
        return _k(x, y);
    }

    function new_y(uint256 x, uint256 dx, uint256 y) external pure returns (uint256 r) {
        r = _get_y(x, dx, y);
        assert(_k(x + dx, r) >= _k(x, y));
    }

    function from_compat(uint256 x) external pure returns (uint256) {
        return _from_compat(x);
    }

    function from_compat_k(uint256 x) external pure returns (uint256) {
        return _from_compat_k(x);
    }

    function to_compat_down(uint256 x) external pure returns (uint256) {
        return _to_compat_down(x);
    }

    function to_compat_up(uint256 x) external pure returns (uint256) {
        return _to_compat_up(x);
    }

    function INTERNAL_BASIS() external pure returns (uint256) {
        return _VELODROME_TOKEN_BASIS;
    }

    function MAX_BALANCE() external pure returns (uint256) {
        return _VELODROME_MAX_BALANCE;
    }

    function FUDGE() external pure returns (uint256) {
        return _VELODROME_K_FUDGE;
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
        uint256 _INTERNAL_BASIS = dummy.INTERNAL_BASIS();

        uint256 dx = x_transfer;
        dx -= dx * fee_bps / _FEE_BASIS;
        dx *= _INTERNAL_BASIS;
        dx /= x_basis;
        uint256 x = x_reserve * _INTERNAL_BASIS / x_basis;
        uint256 y = y_reserve * _INTERNAL_BASIS / y_basis;

        dummy.new_y(x, dx, y);
    }

    function testVelodrome_fuzzConvergence(uint256 x, uint256 dx, uint256 y) external view {
        uint256 _INTERNAL_BASIS = dummy.INTERNAL_BASIS();
        uint256 _MAX_BALANCE = dummy.MAX_BALANCE() * 2 / 3;

        x = bound(x, _INTERNAL_BASIS, _MAX_BALANCE);
        y = bound(y, _INTERNAL_BASIS, _MAX_BALANCE);
        uint256 max_dx = x * 100;
        if (max_dx > _MAX_BALANCE - x) {
            max_dx = _MAX_BALANCE - x;
        }
        vm.assume(max_dx >= _INTERNAL_BASIS);
        dx = bound(dx, _INTERNAL_BASIS, max_dx);

        dummy.new_y(x, dx, y);
    }

    function testVelodrome_fuzzCompatRounding(uint256 x, uint256 dx, uint256 y) external view {
        uint256 _MAX_BALANCE = dummy.MAX_BALANCE() * 2 / 3;
        _MAX_BALANCE = dummy.to_compat_down(_MAX_BALANCE);

        x = bound(x, 1 ether, _MAX_BALANCE);
        y = bound(y, 1 ether, _MAX_BALANCE);
        uint256 max_dx = x * 100;
        if (max_dx > _MAX_BALANCE - x) {
            max_dx = _MAX_BALANCE - x;
        }
        vm.assume(max_dx >= 1 ether);
        dx = bound(dx, 1 ether, max_dx);

        x = dummy.from_compat(x);
        dx = dummy.from_compat(dx);
        y = dummy.from_compat(y);

        uint256 new_y = dummy.new_y(x, dx, y);
        new_y = dummy.from_compat(dummy.to_compat_down(new_y));

        assertGe(dummy.k(x + dx, new_y), dummy.k(x, y));
    }

    function solidly_ref_k(uint256 x, uint256 y) internal pure returns (uint256) {
        return (x * ((((y * y) / 1e18) * y) / 1e18)) / 1e18 + (((((x * x) / 1e18) * x) / 1e18) * y) / 1e18;
    }

    function velodrome_ref_k(uint256 x, uint256 y) internal pure returns (uint256) {
        uint256 _a = (x * y) / 1e18;
        uint256 _b = ((x * x) / 1e18 + (y * y) / 1e18);
        return (_a * _b) / 1e18;
    }

    function testVelodrome_fudge(uint256 x, uint256 y) external {
        uint256 _MAX_BALANCE = dummy.MAX_BALANCE() * 2 / 3;
        _MAX_BALANCE = dummy.to_compat_down(_MAX_BALANCE);
        uint256 _FUDGE = dummy.FUDGE();

        x = bound(x, 1 ether, _MAX_BALANCE);
        y = bound(y, 1 ether, _MAX_BALANCE);

        uint256 k = dummy.k(dummy.from_compat(x), dummy.from_compat(y));
        uint256 k_solidly = dummy.from_compat_k(solidly_ref_k(x, y));
        uint256 k_velodrome = dummy.from_compat_k(velodrome_ref_k(x, y));

        assertGe(k + _FUDGE, k_solidly);
        assertGe(k + _FUDGE, k_velodrome);
    }

    /*
    function testVelodrome_fuzzK(uint256 x, uint256 y) external view {
        uint256 _MAX_BALANCE = dummy.MAX_BALANCE() * 2 / 3;
        _MAX_BALANCE = dummy.to_compat_down(_MAX_BALANCE);

        x = bound(x, 1 ether, _MAX_BALANCE);
        y = bound(y, 1 ether, _MAX_BALANCE);

        uint256 solidly_k = dummy.from_compat_k(solidly_ref_k(x, y));
        uint256 velodrome_k = dummy.from_compat_k(velodrome_ref_k(x, y));
        uint256 k = dummy.k(dummy.from_compat(x), dummy.from_compat(y));
        uint256 k_x = dummy.k(dummy.from_compat(x - 1), dummy.from_compat(y));
        uint256 k_y = dummy.k(dummy.from_compat(x), dummy.from_compat(y - 1));

        assertGe(k, solidly_k, "SolidlyV1 reference implementation too low");
        assertLt(k_x, solidly_k, "SolidlyV1 reference implementation too high x");
        assertLt(k_y, solidly_k, "SolidlyV1 reference implementation too high y");

        assertGe(k, velodrome_k, "VelodromeV2 reference implementation too low");
        assertLt(k_x, velodrome_k, "VelodromeV2 reference implementation too high x");
        assertLt(k_y, velodrome_k, "VelodromeV2 reference implementation too high y");
    }
    */

    function testVelodrome_fuzzRefVelodrome(uint256 x, uint256 dx, uint256 y) external view {
        uint256 _MAX_BALANCE = dummy.MAX_BALANCE() * 2 / 3;
        _MAX_BALANCE = dummy.to_compat_down(_MAX_BALANCE);

        x = bound(x, 1 ether, _MAX_BALANCE);
        y = bound(y, 1 ether, _MAX_BALANCE);
        uint256 max_dx = x * 100;
        if (max_dx > _MAX_BALANCE - x) {
            max_dx = _MAX_BALANCE - x;
        }
        vm.assume(max_dx >= 1 ether);
        dx = bound(dx, 1 ether, max_dx);

        uint256 new_y = dummy.new_y(dummy.from_compat(x), dummy.from_compat(dx), dummy.from_compat(y));
        uint256 dy = y - dummy.to_compat_down(new_y);

        uint256 velodrome_k_before = velodrome_ref_k(x, y);
        uint256 velodrome_k_after = velodrome_ref_k(x + dx, y - dy);
        assertGe(velodrome_k_after, velodrome_k_before);
    }

    /*
    function testVelodrome_fuzzRefSolidly(uint256 x, uint256 dx, uint256 y) external view {
        uint256 _MAX_BALANCE = dummy.MAX_BALANCE() * 2 / 3;
        _MAX_BALANCE = dummy.to_compat(_MAX_BALANCE);

        x = bound(x, 1 ether, _MAX_BALANCE);
        y = bound(y, 1 ether, _MAX_BALANCE);
        uint256 max_dx = x * 100;
        if (max_dx > _MAX_BALANCE - x) {
            max_dx = _MAX_BALANCE - x;
        }
        vm.assume(max_dx >= 1 ether);
        dx = bound(dx, 1 ether, max_dx);

        uint256 dy = dummy.to_compat(dummy.dy(dummy.from_compat(x), dummy.from_compat(dx), dummy.from_compat(y)));

        uint256 solidly_k_before = solidly_ref_k(x, y);
        uint256 solidly_k_after = solidly_ref_k(x + dx, y - dy);
        assertGe(solidly_k_after, solidly_k_before);
    }
    */
}
