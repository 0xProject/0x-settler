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
        uint256 value;
        bytes data;
    }

    struct Result {
        bool success;
        bytes data;
    }

    function multicall(Call[] calldata calls, uint256 contextdepth) external payable returns (Result[] memory);
}

abstract contract MultiCallContext is Context {
    address private constant _MULTICALL_ADDRESS = 0x000000000000deaDdeAddEADdEaddeaDDEADDeAd; // TODO:

    IMultiCall internal constant _MULTICALL = IMultiCall(_MULTICALL_ADDRESS);

    function _isForwarded() internal view virtual override returns (bool) {
        return super._isForwarded() || super._msgSender() == address(_MULTICALL);
    }

    function _msgData() internal view virtual override returns (bytes calldata r) {
        address sender = super._msgSender();
        r = super._msgData();
        assembly ("memory-safe") {
            r.length :=
                sub(r.length, mul(0x14, eq(_MULTICALL_ADDRESS, and(0xffffffffffffffffffffffffffffffffffffffff, sender))))
        }
    }

    function _msgSender() internal view virtual override returns (address sender) {
        sender = super._msgSender();
        bytes calldata data = super._msgData();
        assembly ("memory-safe") {
            sender := and(0xffffffffffffffffffffffffffffffffffffffff, sender)
            // ERC-2771. The trusted forwarder (`_MULTICALL`) has appended the appropriate
            // msg.sender to the msg data
            sender :=
                xor(
                    sender,
                    mul(
                        xor(sender, shr(0x60, calldataload(add(data.offset, sub(data.length, 0x14))))),
                        eq(_MULTICALL_ADDRESS, sender)
                    )
                )
        }
    }
}
