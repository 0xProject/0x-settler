// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {KatanaSettler} from "src/chains/Katana/TakerSubmitted.sol";
import {ActionDataBuilder} from "../../utils/ActionDataBuilder.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";
import {IAllowanceHolder} from "src/allowanceholder/IAllowanceHolder.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {SettlerBasePairTest, Shim} from "../SettlerBasePairTest.t.sol";
import {sushiswapV3ForkId} from "src/core/univ3forks/SushiswapV3.sol";
import {TooMuchSlippage} from "src/core/SettlerErrors.sol";

IERC20 constant KATANA_VBETH = IERC20(0xEE7D8BCFb72bC1880D0Cf19822eB0A2e6577aB62);
IERC20 constant KATANA_AUSD = IERC20(0x00000000eFE302BEAA2b3e6e1b18d08D69a9012a);
address constant KATANA_SUSHIV3_VBETH_AUSD_POOL = 0xa522683eCE4b864a505cC7D4f65fAeFC93e72f38;
uint256 constant KATANA_BLOCK = 31_863_093;

contract SushiV3KatanaIntegrationTest is SettlerBasePairTest {
    function setUp() public virtual override {
        // Katana proxy token balance slots are not discoverable by `deal()`.
        vm.createSelectFork(_testChainId(), _testBlockNumber());
        vm.setEvmVersion("osaka");
        permit2Domain = keccak256(
            abi.encode(
                keccak256("EIP712Domain(string name,uint256 chainId,address verifyingContract)"),
                keccak256("Permit2"),
                block.chainid,
                address(PERMIT2)
            )
        );
        vm.label(address(this), "FoundryTest");
        vm.label(address(PERMIT2), "Permit2");
        vm.label(FROM, "FROM");
        vm.label(address(fromToken()), "vbETH");
        vm.label(address(toToken()), "AUSD");

        vm.prank(KATANA_SUSHIV3_VBETH_AUSD_POOL);
        fromToken().transfer(FROM, amount());

        allowanceHolder = IAllowanceHolder(0x0000000000001fF3684f28c67538d4D072C22734);
        uint256 forkChainId = (new Shim()).chainId();
        vm.chainId(31337);
        bytes memory initCode = settlerInitCode();
        assembly ("memory-safe") {
            let s := create(0x00, add(0x20, initCode), mload(initCode))
            if iszero(s) { revert(0x00, 0x00) }
            sstore(settler.slot, s)
        }
        vm.label(address(settler), "Settler");
        vm.etch(address(allowanceHolder), vm.getDeployedCode("AllowanceHolder.sol:AllowanceHolder"));
        vm.label(address(allowanceHolder), "AllowanceHolder");
        vm.chainId(forkChainId);
    }

    function settlerInitCode() internal virtual override returns (bytes memory) {
        return bytes.concat(type(KatanaSettler).creationCode, abi.encode(bytes20(0)));
    }

    function _testChainId() internal pure virtual override returns (string memory) {
        return "katana";
    }

    function _testBlockNumber() internal pure virtual override returns (uint256) {
        return KATANA_BLOCK;
    }

    function fromToken() internal pure virtual override returns (IERC20) {
        return KATANA_VBETH;
    }

    function toToken() internal pure virtual override returns (IERC20) {
        return KATANA_AUSD;
    }

    function _testName() internal pure virtual override returns (string memory) {
        return "KATANA-SUSHIV3";
    }

    function amount() internal pure virtual override returns (uint256) {
        return 0.001 ether;
    }

    function _sushiV3Path() internal view returns (bytes memory) {
        return
            abi.encodePacked(fromToken(), uint8(sushiswapV3ForkId), uint24(3000), sqrtPriceLimitX96FromTo(), toToken());
    }

    function _permit() internal view returns (ISignatureTransfer.PermitTransferFrom memory) {
        return defaultERC20PermitTransfer(address(fromToken()), amount(), 0);
    }

    function _exec(bytes[] memory actions) internal {
        bytes memory ahData = abi.encodeCall(
            settler.execute,
            (
                ISettlerBase.AllowedSlippage({recipient: payable(FROM), buyToken: toToken(), minAmountOut: 0}),
                actions,
                bytes32(0)
            )
        );
        allowanceHolder.exec(address(settler), address(fromToken()), amount(), payable(address(settler)), ahData);
    }

    function testKatanaSushiV3() public {
        uint256 buyBalanceBefore = toToken().balanceOf(FROM);

        vm.startPrank(FROM);
        fromToken().approve(address(allowanceHolder), amount());

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.TRANSFER_FROM, (address(settler), _permit(), new bytes(0))),
            abi.encodeCall(ISettlerActions.UNISWAPV3, (FROM, 10_000, _sushiV3Path(), 0))
        );
        _exec(actions);
        vm.stopPrank();

        assertEq(fromToken().balanceOf(FROM), 0, "all vbETH should be spent");
        assertGt(toToken().balanceOf(FROM), buyBalanceBefore, "should have bought AUSD");
    }

    function testKatanaSushiV3_VIP() public {
        uint256 buyBalanceBefore = toToken().balanceOf(FROM);

        vm.startPrank(FROM);
        fromToken().approve(address(allowanceHolder), amount());

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.UNISWAPV3_VIP, (FROM, _permit(), _sushiV3Path(), new bytes(0), 0))
        );
        _exec(actions);
        vm.stopPrank();

        assertEq(fromToken().balanceOf(FROM), 0, "all vbETH should be spent");
        assertGt(toToken().balanceOf(FROM), buyBalanceBefore, "should have bought AUSD");
    }

    function testKatanaSushiV3_slippageRevert() public {
        vm.startPrank(FROM);
        fromToken().approve(address(allowanceHolder), amount());

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.TRANSFER_FROM, (address(settler), _permit(), new bytes(0))),
            abi.encodeCall(ISettlerActions.UNISWAPV3, (FROM, 10_000, _sushiV3Path(), type(uint256).max))
        );

        vm.expectPartialRevert(TooMuchSlippage.selector);
        _exec(actions);
        vm.stopPrank();
    }
}
