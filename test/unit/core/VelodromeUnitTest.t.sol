// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";

//import {Velodrome} from "src/core/VelodromeAlt.sol";
import {Velodrome} from "src/core/Velodrome.sol";
import {uint512/*, uint512_external, alloc*/} from "src/utils/512Math.sol";

import {Test} from "@forge-std/Test.sol";

contract VelodromeConvergenceDummy is Velodrome {
    function _tokenId() internal pure override returns (uint256) {
        revert("unimplemented");
    }

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

    function _div512to256(uint512 n, uint512 d) internal view override returns (uint256) {
        return n.div(d);
    }

    /*
    function k(uint256 x, uint256 x_basis, uint256 y, uint256 y_basis)
        external
        pure
        returns (uint512_external memory)
    {
        uint512 k_out = alloc();
        _k(k_out, x, x_basis, y, y_basis);
        return k_out.toExternal();
    }
    */

    function k(uint256 x, uint256 x_basis, uint256 y, uint256 y_basis) external pure returns (uint256) {
        assert(x_basis == _VELODROME_TOKEN_BASIS);
        assert(y_basis == _VELODROME_TOKEN_BASIS);
        return _k_compat(x, y);
    }

    /*
    function new_y(uint256 x, uint256 dx, uint256 x_basis, uint256 y, uint256 y_basis)
        external
        view
        returns (uint256 r)
    {
        r = _get_y(x, dx, x_basis, y, y_basis);
    }
    */

    function new_y(uint256 x, uint256 dx, uint256 x_basis, uint256 y, uint256 y_basis)
        external
        pure
        returns (uint256)
    {
        return _get_y(
            x * _VELODROME_TOKEN_BASIS / x_basis,
            dx * _VELODROME_TOKEN_BASIS / x_basis,
            y * _VELODROME_TOKEN_BASIS / y_basis
        ) * y_basis / _VELODROME_TOKEN_BASIS;
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

    uint256 internal constant _MIN_BALANCE = 100;
    uint256 internal constant _MIN_K = 10 ** 10;
    uint256 internal constant _MAX_SWAP_SIZE_REL = 10_000;
    uint256 internal constant _MAX_IMBALANCE = 1_000;
    uint8 internal constant _MIN_DECIMALS = 0;
    uint8 internal constant _MAX_DECIMALS = 31;
    uint256 internal constant _MIN_BALANCE_TOKENS_RECIP = 3;

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
        uint256 _MAX_BALANCE = dummy.MAX_BALANCE();

        x = bound(x, _MIN_BALANCE, _MAX_BALANCE);
        y = bound(y, _MIN_BALANCE, _MAX_BALANCE);
        vm.assume(dummy.k(x, _VELODROME_BASIS, y, _VELODROME_BASIS) >= _MIN_K);
        uint256 max_dx = x * _MAX_SWAP_SIZE_REL;
        if (max_dx > _MAX_BALANCE - x) {
            max_dx = _MAX_BALANCE - x;
        }
        vm.assume(max_dx >= _MIN_BALANCE);
        dx = bound(dx, 1, max_dx);

        dummy.new_y(x, dx, _VELODROME_BASIS, y, _VELODROME_BASIS);
    }

    function testVelodrome_fuzzKIncrease(uint256 x, uint256 dx, uint256 y) external view {
        uint256 _VELODROME_BASIS = dummy.VELODROME_BASIS();
        uint256 _MAX_BALANCE = dummy.MAX_BALANCE();

        x = bound(x, _MIN_BALANCE, _MAX_BALANCE);
        y = bound(y, _MIN_BALANCE, _MAX_BALANCE);
        vm.assume(dummy.k(x, _VELODROME_BASIS, y, _VELODROME_BASIS) >= _MIN_K);
        uint256 max_dx = x * _MAX_SWAP_SIZE_REL;
        if (max_dx > _MAX_BALANCE - x) {
            max_dx = _MAX_BALANCE - x;
        }
        vm.assume(max_dx >= _MIN_BALANCE);
        dx = bound(dx, 1, max_dx);

        uint256 new_y = dummy.new_y(x, dx, _VELODROME_BASIS, y, _VELODROME_BASIS);

        uint256 k_before = dummy.k(x, _VELODROME_BASIS, y, _VELODROME_BASIS);
        uint256 k_after = dummy.k(x + dx, _VELODROME_BASIS, new_y, _VELODROME_BASIS);
        uint256 k_less = dummy.k(x + dx, _VELODROME_BASIS, new_y - 1, _VELODROME_BASIS);
        assertGe(k_after, k_before);

        if (x + dx >= 1e12) {
            // This check is commented-out because it is not possible to satisfy this requirement in
            // the same implementation that satisfies both reference implementations of the same
            // constant-function. Therefore, we adopt the relaxed form of the check that you see
            // below.
            //assertLt(k_less, k_before);
            assertLe(k_less, k_before);
        }
    }

    /*
    function solidly_ref_k(uint256 x, uint256 y) internal pure returns (uint256) {
        return (x * ((((y * y) / 1e18) * y) / 1e18)) / 1e18 + (((((x * x) / 1e18) * x) / 1e18) * y) / 1e18;
    }
    */

    function velodrome_ref_k(uint256 x, uint256 y) internal pure returns (uint256) {
        uint256 _a = (x * y) / 1e18;
        uint256 _b = ((x * x) / 1e18 + (y * y) / 1e18);
        return (_a * _b) / 1e18;
    }

    function testVelodrome_bounds_refVelodrome() external view {
        uint256 _MAX_BALANCE = dummy.MAX_BALANCE();
        velodrome_ref_k(_MAX_BALANCE, _MAX_BALANCE);
    }

    function _testVelodrome_outOfBounds_refVelodrome(uint256 x, uint256 y) external pure returns (uint256) {
        return velodrome_ref_k(x, y);
    }

    function testVelodrome_outOfBounds_refVelodrome() external view {
        uint256 _MAX_BALANCE_PLUS_ONE = dummy.MAX_BALANCE() + 1;
        try this._testVelodrome_outOfBounds_refVelodrome(_MAX_BALANCE_PLUS_ONE, _MAX_BALANCE_PLUS_ONE) returns (uint256) {
            assert(false);
        } catch {}
    }

    function testVelodrome_fuzzRangeRefVelodrome(uint256 x, uint256 y) external view {
        uint256 _VELODROME_BASIS = dummy.VELODROME_BASIS();
        uint256 _MAX_BALANCE = dummy.MAX_BALANCE();

        x = bound(x, _VELODROME_BASIS, _MAX_BALANCE);
        y = bound(y, _VELODROME_BASIS, _MAX_BALANCE);

        velodrome_ref_k(x, y);
    }

    function testVelodrome_fuzzK(uint256 x, uint256 y) external view {
        uint256 _VELODROME_BASIS = dummy.VELODROME_BASIS();
        uint256 _MAX_BALANCE = dummy.MAX_BALANCE();
        x = bound(x, _VELODROME_BASIS, _MAX_BALANCE);
        y = bound(y, _VELODROME_BASIS, _MAX_BALANCE);

        uint256 velodrome_k = velodrome_ref_k(x, y);
        uint256 k = dummy.k(x, _VELODROME_BASIS, y, _VELODROME_BASIS);
        uint256 k_x = dummy.k(x - 1, _VELODROME_BASIS, y, _VELODROME_BASIS);
        uint256 k_y = dummy.k(x, _VELODROME_BASIS, y - 1, _VELODROME_BASIS);

        assertGe(k, velodrome_k, "VelodromeV2 reference implementation too low");
        assertLt(k_x, velodrome_k, "VelodromeV2 reference implementation too high x");
        assertLt(k_y, velodrome_k, "VelodromeV2 reference implementation too high y");
    }

    function _fuzzRef(
        uint256 x,
        uint256 dx,
        uint8 x_decimals,
        uint256 y,
        uint8 y_decimals,
        function (uint256, uint256) internal pure returns (uint256) ref_k,
        uint256 fudge
    ) internal view {
        x_decimals = uint8(bound(x_decimals, _MIN_DECIMALS, _MAX_DECIMALS));
        y_decimals = uint8(bound(y_decimals, _MIN_DECIMALS, _MAX_DECIMALS));
        uint256 x_basis = 10 ** x_decimals;
        uint256 y_basis = 10 ** y_decimals;

        uint256 _VELODROME_BASIS = dummy.VELODROME_BASIS();
        uint256 _MAX_BALANCE = dummy.MAX_BALANCE();

        uint256 min_x =
            x_basis / _MIN_BALANCE_TOKENS_RECIP > _MIN_BALANCE ? x_basis / _MIN_BALANCE_TOKENS_RECIP : _MIN_BALANCE;
        x = bound(x, min_x, _MAX_BALANCE * x_basis / _VELODROME_BASIS);
        {
            uint256 min_y = x * y_basis / (x_basis * _MAX_IMBALANCE);
            if (min_y < _MIN_BALANCE) {
                min_y = _MIN_BALANCE;
            }
            if (min_y < y_basis / _MIN_BALANCE_TOKENS_RECIP) {
                min_y = y_basis / _MIN_BALANCE_TOKENS_RECIP;
            }
            uint256 max_y = x * y_basis * _MAX_IMBALANCE / x_basis;
            if (max_y > _MAX_BALANCE * y_basis / _VELODROME_BASIS) {
                max_y = _MAX_BALANCE * y_basis / _VELODROME_BASIS;
            }
            vm.assume(min_y <= max_y);
            y = bound(y, min_y, max_y);
        }
        {
            uint256 max_dx = x * _MAX_SWAP_SIZE_REL;
            if (max_dx > _MAX_BALANCE * x_basis / _VELODROME_BASIS - x) {
                max_dx = _MAX_BALANCE * x_basis / _VELODROME_BASIS - x;
            }
            vm.assume(min_x <= max_dx);
            dx = bound(dx, min_x, max_dx);
        }
        assertLe(x + dx, _MAX_BALANCE * x_basis / _VELODROME_BASIS, "dx too large; balance overflow");

        uint256 new_y = dummy.new_y(
            x_basis > _VELODROME_BASIS ? x / (x_basis / _VELODROME_BASIS) : x,
            x_basis > _VELODROME_BASIS ? dx / (x_basis / _VELODROME_BASIS) : dx,
            x_basis > _VELODROME_BASIS ? _VELODROME_BASIS : x_basis,
            y_basis > _VELODROME_BASIS ? y / (y_basis / _VELODROME_BASIS) : y,
            y_basis > _VELODROME_BASIS ? _VELODROME_BASIS : y_basis
        );
        assertLe(
            y_basis > _VELODROME_BASIS ? new_y * (y_basis / _VELODROME_BASIS) : new_y,
            _MAX_BALANCE * y_basis / _VELODROME_BASIS,
            "dy too large; balance overflow"
        );
        new_y += fudge;
        if (x < x_basis || y < y_basis) {
            new_y += fudge;
        }
        if (y_basis > _VELODROME_BASIS) {
            new_y *= y_basis / _VELODROME_BASIS;
        }
        vm.assume(new_y <= _MAX_BALANCE * y_basis / _VELODROME_BASIS);

        uint256 k_before = ref_k(x * _VELODROME_BASIS / x_basis, y * _VELODROME_BASIS / y_basis);
        uint256 k_after = ref_k((x + dx) * _VELODROME_BASIS / x_basis, new_y * _VELODROME_BASIS / y_basis);
        assertGe(k_after, k_before, "k decreased");
    }

    function testVelodrome_fuzzRefVelodrome(uint256 x, uint256 dx, uint8 x_decimals, uint256 y, uint8 y_decimals)
        external
        view
    {
        _fuzzRef(x, dx, x_decimals, y, y_decimals, velodrome_ref_k, 1);
    }
}
