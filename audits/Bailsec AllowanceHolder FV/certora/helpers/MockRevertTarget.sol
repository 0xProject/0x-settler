// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

// A target used to prove exec propagates the target call's revert
// (AllowanceHolderBase._exec line 125: `case 0 { revert(ptr, returndatasize()) }`).

interface IRevertTarget {
    function triggerRevert() external payable;
}

contract MockRevertTarget {
    function triggerRevert() external payable {
        revert();
    }
}
