// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Test} from "@forge-std/Test.sol";
import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {AllowanceHolder} from "src/allowanceholder/AllowanceHolder.sol";
import {ALLOWANCE_HOLDER} from "src/allowanceholder/IAllowanceHolder.sol";
import {BridgeSettler, BridgeSettlerBase} from "src/bridge/BridgeSettler.sol";
import {ISettlerTakerSubmitted} from "src/interfaces/ISettlerTakerSubmitted.sol";
import {MainnetSettler} from "src/chains/Mainnet/TakerSubmitted.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";
import {IBridgeSettlerActions} from "src/bridge/IBridgeSettlerActions.sol";
import {DAI, USDC} from "src/core/MakerPSM.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";

contract BridgeSettlerDummy is BridgeSettler {
    constructor(bytes20 gitCommit) BridgeSettlerBase(gitCommit) {}
}

contract BridgeDummy {
    function take(address token, uint256 amount) external {
        IERC20(token).transferFrom(msg.sender, address(this), amount);
    }
}

contract BridgeSettlerTest is Test {
    BridgeSettler bridgeSettler;
    ISettlerTakerSubmitted settler;
    IERC20 token;
    BridgeDummy bridgeDummy;

    function setUp() public {
        bridgeSettler = new BridgeSettlerDummy(bytes20(0));
        AllowanceHolder ah = new AllowanceHolder();
        vm.etch(address(ALLOWANCE_HOLDER), address(ah).code);
        token = deployMockERC20("Test Token", "TT", 18);
        bridgeDummy = new BridgeDummy();
        // Mock DAI and USDC for MainnetSettler to be usable
        vm.etch(address(DAI), address(token).code);
        vm.etch(address(USDC), address(token).code);
        settler = new MainnetSettler(bytes20(0));
    }

    function testUserFlow() public {
        address user = makeAddr("user");

        bytes[] memory settlerActions = new bytes[](2);
        // Take the assets from BridgeSettler
        settlerActions[0] = abi.encodeWithSelector(
            ISettlerActions.TRANSFER_FROM.selector,
            address(settler),
            ISignatureTransfer.PermitTransferFrom({
                permitted: ISignatureTransfer.TokenPermissions({
                    token: address(token),
                    amount: 1000
                }),
                nonce: 0,
                deadline: block.timestamp
            }),
            bytes(""),
            abi.encodeWithSelector(
                ALLOWANCE_HOLDER.transferFrom.selector,
                address(token),
                address(bridgeSettler),
                address(settler),
                1000
            )
        );
        // Just send them back to BridgeSettler
        settlerActions[1] = abi.encodeWithSelector(
            ISettlerActions.BASIC.selector,
            address(0),
            0,
            address(token),
            0,
            abi.encodeWithSelector(
                IERC20.transfer.selector,
                address(bridgeSettler),
                1000
            )
        );
        
        bytes[] memory bridgeActions = new bytes[](3);
        // Take the assets from the BridgeSettler
        bridgeActions[0] = abi.encodeWithSelector(
            IBridgeSettlerActions.TAKE.selector,
            address(token),
            1000
        );
        // Do a swap (that just takes and returns the assets)
        bridgeActions[1] = abi.encodeWithSelector(
            IBridgeSettlerActions.SETTLER_SWAP.selector,
            address(token),
            1000,
            address(settler),
            abi.encodeWithSelector(
                ISettlerTakerSubmitted.execute.selector,
                ISettlerBase.AllowedSlippage({
                    recipient: payable(address(0)),
                    buyToken: IERC20(address(0)),
                    minAmountOut: 0
                }),
                settlerActions,
                bytes32(0)
            )
        );
        // Bridge the assets to the dummy bridge
        bridgeActions[2] = abi.encodeWithSelector(
            IBridgeSettlerActions.BRIDGE.selector,
            address(token),
            address(bridgeDummy),
            abi.encodeWithSelector(
                BridgeDummy.take.selector,
                address(token),
                1000
            )
        );

        vm.prank(user);
        token.approve(address(ALLOWANCE_HOLDER), type(uint256).max);
        deal(address(token), user, 1000);

        vm.prank(user);
        ALLOWANCE_HOLDER.exec(
            address(bridgeSettler), 
            address(token), 
            1000, 
            payable(address(bridgeSettler)), 
            abi.encodeWithSelector(
                BridgeSettler.execute.selector, 
                bridgeActions,
                bytes32(0)
            )
        );

        assertEq(token.balanceOf(address(bridgeDummy)), 1000, "Bridge did not receive the assets");
    }
}