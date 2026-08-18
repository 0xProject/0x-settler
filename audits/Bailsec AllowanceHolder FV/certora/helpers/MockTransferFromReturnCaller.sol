// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

interface IAHTransferFrom {
    function transferFrom(address token, address owner, address recipient, uint256 amount) external returns (bool);
}

// Captures the RETURN VALUE of the AllowanceHolder fallback's transferFrom selector
// path (AllowanceHolderBase.sol:173-177: `mstore(0x00, 0x01); return(0x00, 0x20)`).

contract MockTransferFromReturnCaller {
    IAHTransferFrom allowanceHolder; // linked to AllowanceHolderHarness (internal: no getter)

    // Typed call: decodes the fallback's 32-byte return as bool.
    function callTransferFromReturnBool(address token, address owner, address recipient, uint256 amount)
        external
        returns (bool)
    {
        return allowanceHolder.transferFrom(token, owner, recipient, amount);
    }

    // Low-level call: surfaces the raw returndata length and its first 32-byte word.
    function callTransferFromReturnWord(address token, address owner, address recipient, uint256 amount)
        external
        returns (uint256 word, uint256 retLen)
    {
        (bool ok, bytes memory ret) = address(allowanceHolder).call(
            abi.encodeWithSelector(IAHTransferFrom.transferFrom.selector, token, owner, recipient, amount)
        );
        require(ok, "fallback call failed");
        retLen = ret.length;
        word = abi.decode(ret, (uint256));
    }
}
