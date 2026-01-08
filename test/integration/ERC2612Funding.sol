// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {ActionDataBuilder} from "../utils/ActionDataBuilder.sol";
import {SettlerBasePairTest} from "./SettlerBasePairTest.t.sol";

interface IUSDC {
    function permit(address owner, address spender, uint256 value, uint256 deadline, uint8 v, bytes32 r, bytes32 s)
        external;
    function nonces(address owner) external view returns (uint256);
    function DOMAIN_SEPARATOR() external view returns (bytes32);
}

contract ERC2612FundingTest is SettlerBasePairTest {
    IERC20 internal constant _USDC = IERC20(0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48);
    IERC20 internal constant _WETH = IERC20(0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2);

    bytes32 private constant _PERMIT_TYPEHASH =
        keccak256("Permit(address owner,address spender,uint256 value,uint256 nonce,uint256 deadline)");

    function _testName() internal pure override returns (string memory) {
        return "ERC2612Funding";
    }

    function fromToken() internal pure override returns (IERC20) {}

    function toToken() internal pure override returns (IERC20) {}

    function amount() internal pure override returns (uint256) {
        return 1000e6;
    }

    function _signERC2612Permit(address owner, address spender, uint256 value, uint256 deadline, uint256 privateKey)
        internal
        view
        returns (uint8 v, bytes32 r, bytes32 s)
    {
        uint256 nonce = IUSDC(address(_USDC)).nonces(owner);
        bytes32 domainSeparator = IUSDC(address(_USDC)).DOMAIN_SEPARATOR();

        bytes32 structHash = keccak256(abi.encode(_PERMIT_TYPEHASH, owner, spender, value, nonce, deadline));

        bytes32 digest = keccak256(abi.encodePacked("\x19\x01", domainSeparator, structHash));

        (v, r, s) = vm.sign(privateKey, digest);
    }

    function testPermitFlow() public {
        (address sender, uint256 pk) = makeAddrAndKey("sender");

        deal(address(_USDC), sender, amount());

        uint256 deadline = block.timestamp + 1 hours;
        (uint8 v, bytes32 r, bytes32 s) = _signERC2612Permit(sender, address(allowanceHolder), amount(), deadline, pk);

        bytes memory permit =
            abi.encodeCall(IUSDC.permit, (sender, address(allowanceHolder), amount(), deadline, v, r, s));

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(
                ISettlerActions.TRANSFER_FROM,
                (address(this), defaultERC20PermitTransfer(address(_USDC), amount(), 0), permit)
            )
        );

        vm.prank(sender);
        allowanceHolder.exec(
            address(settler),
            address(_USDC),
            amount(),
            payable(address(settler)),
            abi.encodeCall(
                settler.execute,
                (
                    ISettlerBase.AllowedSlippage({
                        recipient: payable(address(0)), buyToken: IERC20(address(0)), minAmountOut: 0
                    }),
                    actions,
                    bytes32(0)
                )
            )
        );

        assertEq(_USDC.balanceOf(address(this)), amount(), "Transfer failed");
        assertEq(_USDC.balanceOf(sender), 0, "Sender should have 0 balance");
    }
}
