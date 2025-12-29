// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Test} from "@forge-std/Test.sol";
import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {ALLOWANCE_HOLDER} from "src/allowanceholder/IAllowanceHolder.sol";
import {BridgeSettler, BridgeSettlerBase} from "src/bridge/BridgeSettler.sol";
import {ISettlerTakerSubmitted} from "src/interfaces/ISettlerTakerSubmitted.sol";
import {MainnetSettler} from "src/chains/Mainnet/TakerSubmitted.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";
import {IBridgeSettlerActions} from "src/bridge/IBridgeSettlerActions.sol";
import {DAI, USDC} from "src/core/MakerPSM.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {Utils} from "./Utils.sol";
import {DEPLOYER} from "src/deployer/DeployerAddress.sol";
import {IERC721View} from "src/deployer/IDeployer.sol";
import {MockERC20} from "@solmate/test/utils/mocks/MockERC20.sol";

contract BridgeSettlerDummy is BridgeSettler {
    constructor(bytes20 gitCommit) BridgeSettlerBase(gitCommit) {}
}

contract BridgeDummy {
    function take(address token, uint256 amount) external {
        IERC20(token).transferFrom(msg.sender, address(this), amount);
    }

    receive() external payable {}
}

contract BridgeSettlerTestBase is Test {
    BridgeSettler bridgeSettler;
    ISettlerTakerSubmitted settler;
    IERC20 token;
    BridgeDummy bridgeDummy;

    function _testBridgeSettler() internal virtual {
        bridgeSettler = new BridgeSettlerDummy(bytes20(0));
    }

    function setUp() public virtual {
        _testBridgeSettler();
        vm.label(address(bridgeSettler), "BridgeSettler");
        bridgeDummy = new BridgeDummy();
        token = IERC20(address(new MockERC20("Test Token", "TT", 18)));
    }
}

contract BridgeSettlerUnitTest is BridgeSettlerTestBase {
    function setUp() public override {
        super.setUp();

        vm.etch(address(ALLOWANCE_HOLDER), vm.getDeployedCode("AllowanceHolder.sol:AllowanceHolder"));
        // Mock DAI and USDC for MainnetSettler to be usable
        deployCodeTo("MockERC20", abi.encode("DAI", "DAI", 18), address(DAI));
        deployCodeTo("MockERC20", abi.encode("USDC", "USDC", 6), address(USDC));
        settler = new MainnetSettler(bytes20(0));
    }
}

contract BridgeSettlerTest is BridgeSettlerUnitTest, Utils {
    function testUserFlow() public {
        address user = makeAddr("user");
        uint256 amount = 2000;

        bytes[] memory settlerActions = new bytes[](2);
        // Take the assets from BridgeSettler
        settlerActions[0] = abi.encodeCall(
            ISettlerActions.TRANSFER_FROM,
            (
                address(settler),
                ISignatureTransfer.PermitTransferFrom({
                    permitted: ISignatureTransfer.TokenPermissions({token: address(token), amount: amount}),
                    nonce: 0,
                    deadline: block.timestamp
                }),
                bytes("")
            )
        );
        // Just send them back to BridgeSettler
        settlerActions[1] = abi.encodeCall(
            ISettlerActions.BASIC,
            (address(token), 10_000, address(token), 0x24, abi.encodeCall(IERC20.transfer, (address(bridgeSettler), 0)))
        );

        bytes[] memory bridgeActions = new bytes[](3);
        // Take the assets from the BridgeSettler
        bridgeActions[0] = abi.encodeCall(
            IBridgeSettlerActions.TRANSFER_FROM,
            (
                address(bridgeSettler),
                ISignatureTransfer.PermitTransferFrom({
                    permitted: ISignatureTransfer.TokenPermissions({token: address(token), amount: amount}),
                    nonce: 0,
                    deadline: block.timestamp
                }),
                bytes("")
            )
        );
        // Do a swap (that just takes and returns the assets)
        bridgeActions[1] = abi.encodeCall(
            IBridgeSettlerActions.SETTLER_SWAP,
            (
                address(token),
                amount,
                address(settler),
                abi.encodeCall(
                    ISettlerTakerSubmitted.execute,
                    (
                        ISettlerBase.AllowedSlippage({
                            recipient: payable(address(0)),
                            buyToken: IERC20(address(0)),
                            minAmountOut: 0
                        }),
                        settlerActions,
                        bytes32(0)
                    )
                )
            )
        );
        // Bridge the assets to the dummy bridge
        bridgeActions[2] = abi.encodeCall(
            IBridgeSettlerActions.BASIC,
            (address(token), 10_000, address(bridgeDummy), 0x24, abi.encodeCall(BridgeDummy.take, (address(token), 0)))
        );

        vm.prank(user);
        token.approve(address(ALLOWANCE_HOLDER), type(uint256).max);
        deal(address(token), user, amount);

        _mockExpectCall(address(DEPLOYER), abi.encodeCall(IERC721View.ownerOf, (2)), abi.encode(address(settler)));
        vm.prank(user);
        ALLOWANCE_HOLDER.exec(
            address(bridgeSettler),
            address(token),
            amount,
            payable(address(bridgeSettler)),
            abi.encodeCall(BridgeSettler.execute, (bridgeActions, bytes32(0)))
        );

        assertEq(token.balanceOf(address(bridgeDummy)), amount, "Bridge did not receive the assets");
    }

    function testUserFlowWithNative() public {
        address user = makeAddr("user");
        address ETH_ADDRESS = address(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE);
        uint256 amount = 1000;

        bytes[] memory settlerActions = new bytes[](1);
        // Just send Native back to BridgeSettler
        settlerActions[0] =
            abi.encodeCall(ISettlerActions.BASIC, (ETH_ADDRESS, 10_000, address(bridgeSettler), 0x00, bytes("")));

        bytes[] memory bridgeActions = new bytes[](2);
        // Do a swap (that just sends and return the assets)
        bridgeActions[0] = abi.encodeCall(
            IBridgeSettlerActions.SETTLER_SWAP,
            (
                ETH_ADDRESS,
                amount,
                address(settler),
                abi.encodeCall(
                    ISettlerTakerSubmitted.execute,
                    (
                        ISettlerBase.AllowedSlippage({
                            recipient: payable(address(0)),
                            buyToken: IERC20(address(0)),
                            minAmountOut: 0
                        }),
                        settlerActions,
                        bytes32(0)
                    )
                )
            )
        );
        // Bridge the assets to the dummy bridge
        bridgeActions[1] =
            abi.encodeCall(IBridgeSettlerActions.BASIC, (ETH_ADDRESS, 10_000, address(bridgeDummy), 0, bytes("")));

        deal(user, amount);

        _mockExpectCall(address(DEPLOYER), abi.encodeCall(IERC721View.ownerOf, (2)), abi.encode(address(settler)));
        vm.prank(user);
        bridgeSettler.execute{value: amount}(bridgeActions, bytes32(0));

        assertEq(address(bridgeDummy).balance, amount, "Bridge did not receive the assets");
    }
}
