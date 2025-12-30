// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Context} from "../Context.sol";

import {FastLogic} from "../utils/FastLogic.sol";

interface IMultiCall {
    enum RevertPolicy {
        REVERT,
        HALT,
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

    receive() external payable;
}

address constant EIP150_MULTICALL_ADDRESS = 0x00000000000000CF9E3c5A26621af382fA17f24f;

abstract contract MultiCallContext is Context {
    using FastLogic for bool;

    function _MULTICALL() internal view virtual returns (IMultiCall) {
        return IMultiCall(payable(EIP150_MULTICALL_ADDRESS));
    }

    function _isForwarded(address multicall) internal view returns (bool) {
        return super._isForwarded().or(super._msgSender() == address(multicall));
    }

    function _isForwarded() internal view virtual override returns (bool) {
        return MultiCallContext._isForwarded(address(_MULTICALL()));
    }

    function _msgData(address multicall) internal view returns (bytes calldata r) {
        address sender = super._msgSender();
        r = super._msgData();
        assembly ("memory-safe") {
            r.length :=
                sub(r.length, mul(0x14, lt(0x00, shl(0x60, xor(multicall, sender)))))
        }
    }

    function _msgData() internal view virtual override returns (bytes calldata) {
        return MultiCallContext._msgData(address(_MULTICALL()));
    }

    function _msgSender(address multicall) internal view returns (address sender) {
        sender = super._msgSender();
        bytes calldata data = super._msgData();
        assembly ("memory-safe") {
            // ERC-2771. The trusted forwarder (`_MULTICALL`) has appended the appropriate
            // msg.sender to the msg data
            sender :=
                xor(
                    sender,
                    mul(
                        xor(shr(0x60, calldataload(add(data.offset, sub(data.length, 0x14)))), sender),
                        and(lt(0x03, data.length), iszero(shl(0x60, xor(multicall, sender))))
                    )
                )
        }
    }

    function _msgSender() internal view virtual override returns (address) {
        return MultiCallContext._msgSender(address(_MULTICALL()));
    }
}
