// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {MakerPSM, IPSM} from "src/core/MakerPSM.sol";

import {uint512} from "src/utils/512Math.sol";

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {Utils} from "../Utils.sol";

import {Test} from "@forge-std/Test.sol";

import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";

contract MakerPSMDummy is MakerPSM {
    IPSM psm;
    IERC20 dai;

    constructor(IPSM _psm, IERC20 _dai) {
        psm = _psm;
        dai = _dai;
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

    function _tokenId() internal pure override returns (uint256) {
        revert("unimplemented");
    }

    function _hasMetaTxn() internal pure override returns (bool) {
        revert("unimplemented");
    }

    function _dispatch(uint256, uint256, bytes calldata) internal pure override returns (bool) {
        revert("unimplemented");
    }

    function _div512to256(uint512, uint512) internal view override returns (uint256) {
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

    function sellToPool(address recipient, uint256 bps) public {
        super.sellToMakerPsm(recipient, bps, false, 0, psm, dai);
    }

    function buyFromPool(address recipient, uint256 bps) public {
        super.sellToMakerPsm(recipient, bps, true, 0, psm, dai);
    }
}

contract MakerPSMUnitTest is Utils, Test {
    MakerPSMDummy psm;
    address POOL = _createNamedRejectionDummy("POOL");
    address RECIPIENT = _createNamedRejectionDummy("RECIPIENT");
    address LITE_PSM = _etchNamedRejectionDummy("LitePSM", 0xf6e72Db5454dd049d0788e411b06CfAF16853042);
    address SKY_PSM = _etchNamedRejectionDummy("SkyPSM", 0xA188EEC8F81263234dA3622A406892F3D630f98c);
    address DAI = _etchNamedRejectionDummy("DAI", 0x6B175474E89094C44Da98b954EedeAC495271d0F);
    address USDC = _etchNamedRejectionDummy("USDC", 0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48);
    address USDS = _etchNamedRejectionDummy("USDS", 0xdC035D45d973E3EC169d2276DDab16f1e407384F);
    address PSM = LITE_PSM;
    address PSM_DAI = DAI;

    function setUp() public virtual {
        _mockExpectCall(
            address(DAI), abi.encodeWithSelector(IERC20.approve.selector, LITE_PSM, type(uint256).max), abi.encode(true)
        );
        _mockExpectCall(
            address(USDC),
            abi.encodeWithSelector(IERC20.approve.selector, LITE_PSM, type(uint256).max),
            abi.encode(true)
        );
        _mockExpectCall(
            address(USDS), abi.encodeWithSelector(IERC20.approve.selector, SKY_PSM, type(uint256).max), abi.encode(true)
        );
        _mockExpectCall(
            address(USDC), abi.encodeWithSelector(IERC20.approve.selector, SKY_PSM, type(uint256).max), abi.encode(true)
        );
        _mockExpectCall(address(USDC), abi.encodeWithSelector(IERC20.decimals.selector), abi.encode(6));
        psm = new MakerPSMDummy(IPSM(PSM), IERC20(PSM_DAI));
    }

    function testMakerPSMBuy() public {
        uint256 bps = 10_000;
        uint256 amount = 99999;

        _mockExpectCall(
            PSM_DAI, abi.encodeWithSelector(IERC20.balanceOf.selector, address(psm)), abi.encode(amount * 1 ether / 1e6)
        );
        //_mockExpectCall(PSM_DAI, abi.encodeWithSelector(IERC20.allowance.selector, address(psm), PSM), abi.encode(amount));
        //_mockExpectCall(USDC, abi.encodeWithSelector(IERC20.decimals.selector), abi.encode(6));
        _mockExpectCall(PSM, abi.encodeWithSelector(IPSM.tout.selector), abi.encode(100));
        _mockExpectCall(PSM, abi.encodeWithSelector(IPSM.buyGem.selector, RECIPIENT, 99998), abi.encode(amount));

        psm.buyFromPool(RECIPIENT, bps);
    }

    function testMakerPSMSell() public {
        uint256 bps = 10_000;
        uint256 amount = 99999;

        _mockExpectCall(USDC, abi.encodeWithSelector(IERC20.balanceOf.selector, address(psm)), abi.encode(amount));
        //_mockExpectCall(USDC, abi.encodeWithSelector(IERC20.allowance.selector, address(psm), PSM), abi.encode(amount));
        //_mockExpectCall(PSM, abi.encodeWithSelector(IPSM.gemJoin.selector), abi.encode(PSM));
        _mockExpectCall(PSM, abi.encodeWithSelector(IPSM.sellGem.selector, RECIPIENT, amount), abi.encode(99998));

        psm.sellToPool(RECIPIENT, bps);
    }
}

contract MakerSkyPSMUnitTest is MakerPSMUnitTest {
    function setUp() public override {
        PSM = SKY_PSM;
        PSM_DAI = USDS;
        super.setUp();
    }
}
