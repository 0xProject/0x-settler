// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Test} from "@forge-std/Test.sol";
import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ReceivePolicyBlocked} from "src/core/SettlerErrors.sol";

interface IRecipientCheck {
    function checkRecipient(address sender, address recipient, IERC20 token) external view;
}

interface IReceivePolicyRegistry {
    function createPolicyWithAccounts(address admin, uint8 policyType, address[] calldata accounts)
        external
        returns (uint64);

    function setReceivePolicy(uint64 senderPolicyId, uint64 tokenFilterId, address recoveryAuthority) external;
}

contract ReceivePolicyReceiver {
    function verify(IRecipientCheck settler, address sender) external {
        IReceivePolicyRegistry registry = IReceivePolicyRegistry(0x403c000000000000000000000000000000000000);
        IERC20 token = IERC20(0x20C0000000000000000000000000000000000001);
        address[] memory allowed = new address[](1);
        allowed[0] = sender;
        uint64 senderPolicy = registry.createPolicyWithAccounts(address(this), 0, allowed);
        registry.setReceivePolicy(senderPolicy, 1, address(0));

        settler.checkRecipient(sender, address(this), token);
        _expectBlocked(settler, address(settler), token);

        allowed[0] = address(settler);
        senderPolicy = registry.createPolicyWithAccounts(address(this), 0, allowed);
        registry.setReceivePolicy(senderPolicy, 1, address(0));
        settler.checkRecipient(address(settler), address(this), token);
        _expectBlocked(settler, sender, token);

        registry.setReceivePolicy(1, 0, address(0));
        _expectBlocked(settler, sender, token);
        settler.checkRecipient(sender, address(this), IERC20(address(1)));
        settler.checkRecipient(sender, address(settler), token);
    }

    function _expectBlocked(IRecipientCheck settler, address sender, IERC20 token) private view {
        try settler.checkRecipient(sender, address(this), token) {
            revert("blocked transfer accepted");
        } catch (bytes memory reason) {
            require(
                keccak256(reason) == keccak256(abi.encodeWithSelector(ReceivePolicyBlocked.selector, address(this))),
                "incorrect rejection"
            );
        }
    }
}

contract TempoReceivePolicyTest is Test {
    function test_RecipientCheck_Taker_UsesActualSender() public {
        _verify("SettlerRecipientCheck.t.sol:TempoRecipientCheckHarness");
    }

    function test_RecipientCheck_MetaTxn_UsesActualSender() public {
        _verify("SettlerRecipientCheck.t.sol:TempoMetaTxnRecipientCheckHarness");
    }

    function test_RecipientCheck_Intent_UsesActualSender() public {
        _verify("SettlerRecipientCheck.t.sol:TempoIntentRecipientCheckHarness");
    }

    function test_RecipientCheck_Bridge_UsesActualSender() public {
        _verify("BridgeRecipientCheck.t.sol:TempoBridgeRecipientCheckHarness");
    }

    function _verify(string memory artifact) private {
        address settler = deployCode(artifact);
        address receiver = makeAddr("receive policy receiver");
        bytes memory data = abi.encodeCall(ReceivePolicyReceiver.verify, (IRecipientCheck(settler), makeAddr("sender")));
        // A standard Foundry fork does not execute Tempo's native precompiles.
        // The node applies these overrides only within the simulated call.
        string memory params = string.concat(
            '[{"to":"',
            vm.toString(receiver),
            '","data":"',
            vm.toString(data),
            '"},"latest",{',
            '"',
            vm.toString(receiver),
            '":{"code":"',
            vm.toString(type(ReceivePolicyReceiver).runtimeCode),
            '"},',
            '"',
            vm.toString(settler),
            '":{"code":"',
            vm.toString(settler.code),
            '"}}]'
        );
        vm.rpc(vm.envOr("TEMPO_RPC_URL", string("https://rpc.tempo.xyz/")), "eth_call", params);
    }
}
