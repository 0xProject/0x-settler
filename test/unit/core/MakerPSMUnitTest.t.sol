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

    function _dispatch(uint256, uint256, bytes calldata, AllowedSlippage memory) internal pure override returns (bool) {
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
        function(bytes calldata) internal returns (bytes memory)
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

    function sellToPool(address recipient, uint256 bps, uint256 amountOutMin) public {
        super.sellToMakerPsm(recipient, bps, false, amountOutMin, psm, dai);
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
    address USDT = _etchNamedRejectionDummy("USDT", 0xdAC17F958D2ee523a2206206994597C13D831ec7);
    address USDD = _etchNamedRejectionDummy("USDD", 0x4f8e5DE400DE08B164E7421B3EE387f461beCD1A);
    address USDD_PSM = _etchNamedRejectionDummy("UsddPSM", 0xcE355440c00014A229bbEc030A2B8f8EB45a2897);
    address USDD_GEM_JOIN = _etchNamedRejectionDummy("UsddGemJoin", 0x217e42CEB2eAE9ECB788fDF0e31c806c531760A3);
    address PSM = LITE_PSM;
    address PSM_DAI = DAI;
    address PSM_GEM = USDC;

    function setUp() public virtual {
        // LitePSM approvals
        _mockExpectCall(
            address(DAI), abi.encodeWithSelector(IERC20.approve.selector, LITE_PSM, type(uint256).max), abi.encode(true)
        );
        _mockExpectCall(
            address(USDC),
            abi.encodeWithSelector(IERC20.approve.selector, LITE_PSM, type(uint256).max),
            abi.encode(true)
        );
        // SkyPSM approvals
        _mockExpectCall(
            address(USDS), abi.encodeWithSelector(IERC20.approve.selector, SKY_PSM, type(uint256).max), abi.encode(true)
        );
        _mockExpectCall(
            address(USDC), abi.encodeWithSelector(IERC20.approve.selector, SKY_PSM, type(uint256).max), abi.encode(true)
        );
        // USDD PSM approvals
        _mockExpectCall(
            address(USDD),
            abi.encodeWithSelector(IERC20.approve.selector, USDD_PSM, type(uint256).max),
            abi.encode(true)
        );
        _mockExpectCall(
            address(USDT),
            abi.encodeWithSelector(IERC20.approve.selector, USDD_GEM_JOIN, type(uint256).max),
            abi.encode(true)
        );
        // decimals assertions
        _mockExpectCall(address(USDC), abi.encodeWithSelector(IERC20.decimals.selector), abi.encode(6));
        _mockExpectCall(address(USDT), abi.encodeWithSelector(IERC20.decimals.selector), abi.encode(6));
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

        _mockExpectCall(PSM_GEM, abi.encodeWithSelector(IERC20.balanceOf.selector, address(psm)), abi.encode(amount));
        _mockExpectCall(PSM, abi.encodeWithSelector(IPSM.tin.selector), abi.encode(0));
        _mockExpectCall(PSM, abi.encodeWithSelector(IPSM.sellGem.selector, RECIPIENT, amount), abi.encode(0));

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

contract MakerUsddPSMUnitTest is MakerPSMUnitTest {
    function setUp() public override {
        PSM = USDD_PSM;
        PSM_DAI = USDD;
        PSM_GEM = USDT;
        super.setUp();
    }

    function testSell_DssPsm_ReconstructsOutput() public {
        uint256 amount = 99999;
        uint256 amountOutMin = amount * 1 ether / 1e6;

        _mockExpectCall(USDT, abi.encodeWithSelector(IERC20.balanceOf.selector, address(psm)), abi.encode(amount));
        _mockExpectCall(PSM, abi.encodeWithSelector(IPSM.tin.selector), abi.encode(0));
        _mockExpectCall(PSM, abi.encodeWithSelector(IPSM.sellGem.selector, RECIPIENT, amount), new bytes(0));

        psm.sellToPool(RECIPIENT, 10_000, amountOutMin);
    }

    function testSell_DssPsm_CalculatesFee() public {
        uint256 amount = 1_000_000; // 1 USDT
        uint256 tin = 0.001 ether; // 0.1% fee in wad
        // Expected: wad = 1_000_000 * 1e12 = 1e18, fee = 1e18 * 0.001e18 / 1e18 = 1e15
        // buyAmount = 1e18 - 1e15 = 999_000_000_000_000_000
        uint256 expectedOut = 999_000_000_000_000_000;

        _mockExpectCall(USDT, abi.encodeWithSelector(IERC20.balanceOf.selector, address(psm)), abi.encode(amount));
        _mockExpectCall(PSM, abi.encodeWithSelector(IPSM.tin.selector), abi.encode(tin));
        _mockExpectCall(PSM, abi.encodeWithSelector(IPSM.sellGem.selector, RECIPIENT, amount), new bytes(0));

        psm.sellToPool(RECIPIENT, 10_000, expectedOut);
    }
}
