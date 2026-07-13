// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Test} from "@forge-std/Test.sol";
import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";

import {ISettlerActions} from "src/ISettlerActions.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";
import {BaseSettler} from "src/chains/Base/TakerSubmitted.sol";
import {IAllowanceHolder} from "src/allowanceholder/IAllowanceHolder.sol";

import {ActionDataBuilder} from "../utils/ActionDataBuilder.sol";
import {Permit2Signature} from "../utils/Permit2Signature.sol";
import {Shim} from "./SettlerBasePairTest.t.sol";

contract SelectBase is Test, Permit2Signature {
    uint256 internal constant BASE_BLOCK = 48_241_765;
    address payable internal RECIPIENT = payable(makeAddr("recipient"));
    uint256 internal constant AMOUNT = 0.01 ether;
    uint48 internal constant PERMIT2_FROM_NONCE = 1;

    IERC20 internal constant WETH = IERC20(0x4200000000000000000000000000000000000006);
    IERC20 internal constant USDC = IERC20(0x833589fCD6eDb6E08f4c7C32D4f71b54bdA02913);
    ISignatureTransfer internal constant PERMIT2 = ISignatureTransfer(0x000000000022D473030F116dDEE9F6B43aC78BA3);
    IAllowanceHolder internal constant ALLOWANCE_HOLDER = IAllowanceHolder(0x0000000000001fF3684f28c67538d4D072C22734);

    uint8 internal constant UNISWAP_V3_FORK_ID = 0;
    uint8 internal constant AERODROME_V3_FORK_ID = 4;
    uint24 internal constant UNISWAP_V3_FEE = 500;
    uint24 internal constant AERODROME_TICK_SPACING = 100;

    bytes32 private constant _PERMIT2_NAME_HASH = keccak256("Permit2");
    bytes32 private constant _PERMIT2_TYPE_HASH =
        keccak256("EIP712Domain(string name,uint256 chainId,address verifyingContract)");

    BaseSettler internal settler;
    bytes32 internal permit2Domain;
    uint256 internal fromPrivateKey;
    address payable internal from;

    function setUp() public {
        vm.createSelectFork("base", BASE_BLOCK);
        vm.setEvmVersion("osaka");
        permit2Domain = keccak256(abi.encode(_PERMIT2_TYPE_HASH, _PERMIT2_NAME_HASH, block.chainid, address(PERMIT2)));
        (address fromAddr, uint256 privateKey) = makeAddrAndKey("FROM");
        from = payable(fromAddr);
        fromPrivateKey = privateKey;

        vm.label(address(PERMIT2), "Permit2");
        vm.label(address(WETH), "WETH");
        vm.label(address(USDC), "USDC");
        vm.label(from, "FROM");
        vm.label(RECIPIENT, "RECIPIENT");

        deal(address(WETH), from, AMOUNT);
        vm.prank(from);
        WETH.approve(address(PERMIT2), type(uint256).max);

        uint256 forkChainId = (new Shim()).chainId();
        vm.chainId(31337);
        settler = new BaseSettler(bytes20(0));
        vm.etch(address(ALLOWANCE_HOLDER), vm.getDeployedCode("AllowanceHolder.sol:AllowanceHolder"));
        vm.chainId(forkChainId);
        vm.label(address(settler), "BaseSettler");
    }

    function testFallbackRescue_primaryRevert_commitsAlternate() public {
        bytes[][] memory candidates = _twoCandidates(type(uint256).max, 0);
        uint256[] memory targets = new uint256[](2);

        uint256 beforeBalance = USDC.balanceOf(RECIPIENT);
        _runSelect(address(0), targets, candidates, 1);
        uint256 received = USDC.balanceOf(RECIPIENT) - beforeBalance;

        assertGt(received, 1, "alternate route paid recipient");
        assertEq(WETH.balanceOf(address(settler)), 0, "settler WETH consumed");
        assertEq(USDC.balanceOf(address(settler)), 0, "top-level slippage transferred USDC");
    }

    function testMeasuredBestOf_measuresBothAndCommitsLargerStandaloneOutput() public {
        bytes[][] memory candidates = _twoCandidates(0, 0);

        uint256 uniswapOutput = _standaloneOutput(candidates[0]);
        uint256 aerodromeOutput = _standaloneOutput(candidates[1]);
        uint256 expected = uniswapOutput > aerodromeOutput ? uniswapOutput : aerodromeOutput;

        uint256[] memory targets = new uint256[](2);
        targets[0] = type(uint256).max;
        targets[1] = type(uint256).max;

        uint256 beforeBalance = USDC.balanceOf(RECIPIENT);
        _runSelect(address(USDC), targets, candidates, expected);
        uint256 received = USDC.balanceOf(RECIPIENT) - beforeBalance;

        assertEq(received, expected, "SELECT committed measured argmax");
    }

    function testLadderCommit_unreachableFirstTarget_commitsReachableSecondTarget() public {
        bytes[][] memory candidates = _twoCandidates(0, 0);
        uint256 aerodromeOutput = _standaloneOutput(candidates[1]);

        uint256[] memory targets = new uint256[](2);
        targets[0] = type(uint256).max;
        targets[1] = aerodromeOutput;

        uint256 beforeBalance = USDC.balanceOf(RECIPIENT);
        _runSelect(address(USDC), targets, candidates, aerodromeOutput);
        uint256 received = USDC.balanceOf(RECIPIENT) - beforeBalance;

        assertEq(received, aerodromeOutput, "first reachable rung committed");
    }

    function _runSelect(address token, uint256[] memory targets, bytes[][] memory candidates, uint256 minOut) internal {
        bytes[] memory actions = ActionDataBuilder.build(
            _permit2FundingAction(),
            abi.encodeWithSelector(
                ISettlerActions.SELECT.selector,
                uint256(0),
                token,
                targets,
                candidates
            )
        );

        _execute(actions, minOut);
    }

    function _standaloneOutput(bytes[] memory candidate) internal returns (uint256 output) {
        uint256 snapshot = vm.snapshot();
        uint256 beforeBalance = USDC.balanceOf(RECIPIENT);
        _execute(ActionDataBuilder.build(_permit2FundingAction(), candidate[0]), 1);
        output = USDC.balanceOf(RECIPIENT) - beforeBalance;
        vm.revertTo(snapshot);
    }

    function _execute(bytes[] memory actions, uint256 minOut) internal {
        vm.prank(from, from);
        settler.execute(
            ISettlerBase.AllowedSlippage({recipient: RECIPIENT, buyToken: USDC, minAmountOut: minOut}),
            actions,
            bytes32(0)
        );
    }

    function _permit2FundingAction() internal view returns (bytes memory) {
        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(WETH), AMOUNT, PERMIT2_FROM_NONCE);
        bytes memory sig = getPermitTransferSignature(permit, address(settler), fromPrivateKey, permit2Domain);
        return abi.encodeCall(ISettlerActions.TRANSFER_FROM, (address(settler), permit, sig));
    }

    function _twoCandidates(uint256 uniswapMinOut, uint256 aerodromeMinOut)
        internal
        view
        returns (bytes[][] memory candidates)
    {
        candidates = new bytes[][](2);
        candidates[0] = _candidate(_uniswapPath(), uniswapMinOut);
        candidates[1] = _candidate(_aerodromePath(), aerodromeMinOut);
    }

    function _candidate(bytes memory path, uint256 minOut) internal view returns (bytes[] memory candidate) {
        candidate = new bytes[](1);
        candidate[0] = abi.encodeCall(ISettlerActions.UNISWAPV3, (address(settler), 10_000, path, minOut));
    }

    function _uniswapPath() internal pure returns (bytes memory) {
        return _path(UNISWAP_V3_FORK_ID, UNISWAP_V3_FEE);
    }

    function _aerodromePath() internal pure returns (bytes memory) {
        return _path(AERODROME_V3_FORK_ID, AERODROME_TICK_SPACING);
    }

    function _path(uint8 forkId, uint24 poolId) internal pure returns (bytes memory) {
        return abi.encodePacked(address(WETH), forkId, poolId, _sqrtPriceLimitX96(), address(USDC));
    }

    function _sqrtPriceLimitX96() internal pure returns (uint160) {
        return 4295128740;
    }
}
