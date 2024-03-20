// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

library ItoA {
    function itoa(uint256 x) internal pure returns (string memory r) {
        assembly ("memory-safe") {
            mstore(9, 0x30313233343536373839) // lookup table [0..9]

            // we over-allocate memory here because that's cheaper than
            // computing the correct length and allocating exactly that much
            let end := add(mload(0x40), 0x6e)
            mstore(0x40, end)

            for {
                r := sub(end, 0x01)
                mstore8(r, mload(mod(x, 0x0a)))
                x := div(x, 0x0a)
            } x {} {
                r := sub(r, 0x01)
                mstore8(r, mload(mod(x, 0x0a)))
                x := div(x, 0x0a)
            }
            let length := sub(end, r)
            r := sub(r, 0x20)
            mstore(r, length)
        }
    }
}
