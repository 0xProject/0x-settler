// SPDX-License-Identifier: MIT
pragma solidity =0.8.25;

import {AllowanceHolderContext} from "../../src/allowanceholder/AllowanceHolderContext.sol";

contract MockContextContract is AllowanceHolderContext {

    address public savedMsgSender;
    bool public savedIsForwarded;

    function isForwardedHarness() public view returns (bool) {
        return _isForwarded();
    }

    function msgSenderHarness(bytes calldata /*data*/) public view returns (address) {
        return _msgSender();
    }

    // Length property — returns (msgDataLen, rawMsgDataLen)
    function msgDataLengthHarness(bytes calldata) external view returns (uint256, uint256) {
        return (_msgData().length, msg.data.length);
    }

    // Byte-at-index — _msgData()[i] == msg.data[i]
    // The bytes calldata parameter ensures msg.data is longer than just the 4-byte selector
    function msgDataByteAtHarness(uint256 i, bytes calldata) external view returns (bytes1, bytes1) {
        bytes calldata d = _msgData();
        require(i < d.length, "out of bounds");
        return (d[i], msg.data[i]);
    }

    // Consistency — the stripped tail equals _msgSender()
    // Only meaningful when forwarded
    function msgDataTailIsSenderHarness(bytes calldata) external view returns (address tail, address sender) {
        sender = _msgSender();
        assembly ("memory-safe") {
            tail := shr(0x60, calldataload(sub(calldatasize(), 0x14)))
        }
    }

    function endToEndTest() external {
        savedMsgSender = _msgSender();
        savedIsForwarded = _isForwarded();
    }
}