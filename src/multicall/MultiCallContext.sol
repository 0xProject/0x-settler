// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Context} from "../Context.sol";

interface IMultiCall {
    enum RevertPolicy {
        REVERT,
        STOP,
        CONTINUE
    }

    struct Call {
        address target;
        RevertPolicy revertPolicy;
        bytes data;
    }

    struct Result {
        bool success;
        bytes data;
    }

    function multicall(Call[] calldata, uint256 contextdepth) external returns (Result[] memory);
}

abstract contract MultiCallContext is Context {
    IMultiCall internal constant _MULTICALL = IMultiCall(0x000000000000deaDdeAddEADdEaddeaDDEADDeAd); // TODO:

    function _isForwarded() internal view virtual override returns (bool) {
        return super._isForwarded() || super._msgSender() == address(_MULTICALL);
    }

    function _msgSender() internal view virtual override returns (address sender) {
        sender = super._msgSender();
        assembly ("memory-safe") {
            sender := and(0xffffffffffffffffffffffffffffffffffffffff, sender)
            // ERC-2771. The trusted forwarder (`_MULTICALL`) has appended the appropriate
            // msg.sender to the msg data
            sender := xor(sender, mul(xor(sender, shr(0x60, calldataload(sub(calldatasize(), 0x14)))), eq(_MULTICALL, sender)))
        }
    }
}
