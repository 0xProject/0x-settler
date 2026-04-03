// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";

interface IDlnSource {
    /// @dev Struct representing the creation parameters for creating an order on the (EVM) chain.
    struct OrderCreation {
        /// Address of the ERC-20 token that the maker is offering as part of this order.
        /// Use the zero address to indicate that the maker is offering a native blockchain token (such as Ether, Matic, etc.).
        address giveTokenAddress;
        /// Amount of tokens the maker is offering.
        uint256 giveAmount;
        /// Address of the ERC-20 token that the maker is willing to accept on the destination chain.
        bytes takeTokenAddress;
        /// Amount of tokens the maker is willing to accept on the destination chain.
        uint256 takeAmount;
        // the ID of the chain where an order should be fulfilled.
        uint256 takeChainId;
        /// Address on the destination chain where funds should be sent upon order fulfillment.
        bytes receiverDst;
        /// Address on the source (current) chain authorized to patch the order by adding more input tokens, making it more attractive to takers.
        address givePatchAuthoritySrc;
        /// Address on the destination chain authorized to patch the order by reducing the take amount, making it more attractive to takers,
        /// and can also cancel the order in the take chain.
        bytes orderAuthorityAddressDst;
        // An optional address restricting anyone in the open market from fulfilling
        // this order but the given address. This can be useful if you are creating a order
        // for a specific taker. By default, set to empty bytes array (0x)
        bytes allowedTakerDst;
        /// An optional external call data payload.
        bytes externalCall;
        // An optional address on the source (current) chain where the given input tokens
        // would be transferred to in case order cancellation is initiated by the orderAuthorityAddressDst
        // on the destination chain. This property can be safely set to an empty bytes array (0x):
        // in this case, tokens would be transferred to the arbitrary address specified
        // by the orderAuthorityAddressDst upon order cancellation
        bytes allowedCancelBeneficiarySrc;
    }

    function createSaltedOrder(
        OrderCreation calldata _orderCreation,
        uint64 _salt,
        bytes calldata _affiliateFee,
        uint32 _referralCode,
        bytes calldata _permitEnvelope,
        bytes memory _metadata
    ) external payable returns (bytes32);

    function globalFixedNativeFee() external view returns (uint256);
}

IDlnSource constant DLN_SOURCE = IDlnSource(0xeF4fB24aD0916217251F553c0596F8Edc630EB66);

contract DeBridge {
    using SafeTransferLib for IERC20;

    /// @notice Bridge ERC20 tokens via DeBridge
    /// @param globalFee The global fixed native fee
    /// @param createOrderData Encoded call to `IDlnSource.createSaltedOrder` without selector
    function bridgeToDeBridge(uint256 globalFee, bytes memory createOrderData) internal {
        IERC20 inputToken;
        uint256 amount;
        uint256 orderCreationPtr;
        assembly ("memory-safe") {
            // `createOrderData` layout:
            // +0x00: createOrderData length
            // ... all other `IDlnSource.createSaltedOrder` parameters
            let createOrderPtr := add(0x20, createOrderData)
            orderCreationPtr := add(mload(createOrderPtr), createOrderPtr)
            // `IDlnSource.OrderCreation` layout at `orderCreationPtr`:
            // +0x00: giveTokenAddress
            // +0x20: giveAmount
            // ... all other `IDlnSource.OrderCreation` fields
            inputToken := mload(orderCreationPtr)
        }
        // Store the constant into source to read it only once
        IDlnSource source = DLN_SOURCE;
        if (address(inputToken) == address(0)) {
            uint256 balance = address(this).balance;
            amount = balance - globalFee;
            globalFee = balance;
        } else {
            amount = inputToken.fastBalanceOf(address(this));
            inputToken.safeApproveIfBelow(address(source), amount);
        }

        assembly ("memory-safe") {
            // override giveAmount
            mstore(add(0x20, orderCreationPtr), amount)

            let len := mload(createOrderData)
            // temporarily clobber `createOrderData` size memory area
            mstore(createOrderData, 0xb9303701) // selector for `IDlnSource.createSaltedOrder`
            // `IDlnSource.createSaltedOrder` doesn't clash with restricted targets (AllowanceHolder & Permit2).
            // `source` is also hardcoded to `DLN_SOURCE`.
            if iszero(call(gas(), source, globalFee, add(0x1c, createOrderData), add(0x04, len), 0x00, 0x00)) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
            // restore clobbered memory
            mstore(createOrderData, len)
        }
    }
}
