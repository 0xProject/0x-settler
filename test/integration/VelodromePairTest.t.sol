// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {BasePairTest} from "./BasePairTest.t.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {ActionDataBuilder} from "../utils/ActionDataBuilder.sol";
import {BaseSettler as Settler} from "src/chains/Base.sol";
import {SettlerBase} from "src/SettlerBase.sol";
import {Shim} from "./SettlerBasePairTest.t.sol";

import {Velodrome} from "src/core/Velodrome.sol";

import {AllowanceHolder} from "src/allowanceholder/AllowanceHolder.sol";
import {IAllowanceHolder} from "src/allowanceholder/IAllowanceHolder.sol";

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

    function checkConvergence(uint256 x, uint256 dx, uint256 y) external pure returns (uint256 dy) {
        return y - _get_y(x + dx, _k(x, y), y);
    }
}

contract VelodromePairTest is BasePairTest {
    function testName() internal pure override returns (string memory) {
        return "USDT-USDC";
    }

    Settler internal settler;
    IAllowanceHolder internal allowanceHolder;
    uint256 private _amount;

    function setUp() public override {
        // the pool specified below doesn't have very much liquidity, so we only swap a small amount
        IERC20 sellToken = IERC20(address(fromToken()));
        _amount = 10 ** sellToken.decimals() * 100;

        super.setUp();
        safeApproveIfBelow(fromToken(), FROM, address(PERMIT2), amount());
        warmPermit2Nonce(FROM);

        allowanceHolder = IAllowanceHolder(0x0000000000001fF3684f28c67538d4D072C22734);

        uint256 forkChainId = (new Shim()).chainId();
        vm.chainId(31337);
        settler = new Settler(bytes20(0));
        vm.etch(address(allowanceHolder), address(new AllowanceHolder()).code);
        vm.chainId(forkChainId);

        // USDT is obnoxious about throwing errors, so let's check here before
        // we run into something inscrutable. Do this here to avoid incorrectly
        // warming storage.
        assertGe(fromToken().balanceOf(FROM), amount());
        assertGe(fromToken().allowance(FROM, address(PERMIT2)), amount());
    }

    function fromToken() internal pure override returns (IERC20) {
        return IERC20(0xdAC17F958D2ee523a2206206994597C13D831ec7); // USDT
    }

    function toToken() internal pure override returns (IERC20) {
        return IERC20(0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48); // USDC
    }

    function velodromePool() internal pure returns (address) {
        return 0x63A65a174Cc725824188940255aD41c371F28F28; // actually solidlyv2 (velodrome does not exist on mainnet)
    }

    function amount() internal view override returns (uint256) {
        return _amount;
    }

    function testSettler_velodrome() public skipIf(velodromePool() == address(0)) {
        ISignatureTransfer.PermitTransferFrom memory permit = ISignatureTransfer.PermitTransferFrom({
            permitted: ISignatureTransfer.TokenPermissions({token: address(fromToken()), amount: amount()}),
            nonce: 1,
            deadline: block.timestamp + 30 seconds
        });
        bytes memory sig = getPermitTransferSignature(permit, address(settler), FROM_PRIVATE_KEY, permit2Domain);
        uint24 swapInfo = (2 << 8) | (0 << 1) | (0);
        // fees = 2 bp; internally, solidly uses ppm
        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.TRANSFER_FROM, (velodromePool(), permit, sig)),
            abi.encodeCall(ISettlerActions.VELODROME, (FROM, 0, velodromePool(), swapInfo, 0))
        );

        Settler _settler = settler;

        uint256 beforeBalance = balanceOf(toToken(), FROM);
        vm.startPrank(FROM, FROM);
        snapStartName("settler_velodrome");
        _settler.execute(
            SettlerBase.AllowedSlippage({recipient: address(0), buyToken: IERC20(address(0)), minAmountOut: 0}),
            actions,
            bytes32(0)
        );
        snapEnd();
        uint256 afterBalance = toToken().balanceOf(FROM);

        assertGt(afterBalance, beforeBalance);
    }

    function testVelodrome_convergence() public skipIf(velodromePool() == address(0)) {
        uint256 x_basis = 1000000000000000000;
        uint256 y_basis = 1000000;
        uint256 x_reserve = 3294771369917525;
        uint256 y_reserve = 25493740;

        uint256 _BASIS = 1 ether;

        uint256 dx = 24990000000000 * _BASIS / x_basis;
        uint256 x = x_reserve * _BASIS / x_basis;
        uint256 y = y_reserve * _BASIS / y_basis;

        VelodromeConvergenceDummy dummy = new VelodromeConvergenceDummy();
        dummy.checkConvergence(x, dx, y);
    }
}
