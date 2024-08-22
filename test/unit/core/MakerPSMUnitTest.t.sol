// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {MakerPSM, IPSM} from "src/core/MakerPSM.sol";

import {IERC20} from "forge-std/interfaces/IERC20.sol";
import {Utils} from "../Utils.sol";

import {Test} from "forge-std/Test.sol";

import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";

contract MakerPSMDummy is MakerPSM {
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

    function _permitToSellAmount(ISignatureTransfer.PermitTransferFrom memory)
        internal
        pure
        override
        returns (uint256 sellAmount)
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

    function sellToPool(address recipient, address gemToken, uint256 bps, address psm) public {
        super.sellToMakerPsm(recipient, IERC20(gemToken), bps, IPSM(psm), false, 0);
    }

    function buyFromPool(address recipient, address gemToken, uint256 bps, address psm) public {
        super.sellToMakerPsm(recipient, IERC20(gemToken), bps, IPSM(psm), true, 0);
    }
}

contract MakerPSMUnitTest is Utils, Test {
    MakerPSMDummy psm;
    address POOL = _createNamedRejectionDummy("POOL");
    address RECIPIENT = _createNamedRejectionDummy("RECIPIENT");
    address PSM = _createNamedRejectionDummy("PSM");
    address DAI = _etchNamedRejectionDummy("DAI", 0x6B175474E89094C44Da98b954EedeAC495271d0F);
    address TOKEN = _createNamedRejectionDummy("TOKEN");

    function setUp() public {
        psm = new MakerPSMDummy();
    }

    function testMakerPSMSell() public {
        uint256 bps = 10_000;
        uint256 amount = 99999;

        _mockExpectCall(TOKEN, abi.encodeWithSelector(IERC20.balanceOf.selector, address(psm)), abi.encode(amount));
        _mockExpectCall(TOKEN, abi.encodeWithSelector(IERC20.allowance.selector, address(psm), PSM), abi.encode(amount));
        _mockExpectCall(PSM, abi.encodeWithSelector(IPSM.gemJoin.selector), abi.encode(PSM));
        _mockExpectCall(PSM, abi.encodeWithSelector(IPSM.sellGem.selector, RECIPIENT, amount), abi.encode(true));

        psm.sellToPool(RECIPIENT, TOKEN, bps, PSM);
    }

    function testMakerPSMBuy() public {
        uint256 bps = 10_000;
        uint256 amount = 99999;

        _mockExpectCall(DAI, abi.encodeWithSelector(IERC20.balanceOf.selector, address(psm)), abi.encode(amount));
        _mockExpectCall(DAI, abi.encodeWithSelector(IERC20.allowance.selector, address(psm), PSM), abi.encode(amount));
        _mockExpectCall(TOKEN, abi.encodeWithSelector(IERC20.decimals.selector), abi.encode(18));
        _mockExpectCall(PSM, abi.encodeWithSelector(IPSM.tout.selector), abi.encode(100));
        _mockExpectCall(PSM, abi.encodeWithSelector(IPSM.buyGem.selector, RECIPIENT, 99998), abi.encode(true));

        psm.buyFromPool(RECIPIENT, TOKEN, bps, PSM);
    }
}
