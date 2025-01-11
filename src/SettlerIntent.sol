// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {SettlerMetaTxnBase} from "./SettlerMetaTxn.sol";

import {Panic} from "./utils/Panic.sol";

library ArraySliceBecauseSolidityIsDumb {
    function slice(bytes[] calldata data, uint256 stop_) internal pure returns (bytes[] calldata rData) {
        if (stop_ > data.length) {
            Panic.panic(Panic.ARRAY_OUT_OF_BOUNDS);
        }
        assembly ("memory-safe") {
            rData.offset := data.offset
            rData.length := stop_
        }
    }
}

abstract contract SettlerIntent is SettlerMetaTxnBase {
    using ArraySliceBecauseSolidityIsDumb for bytes[];

    function _tokenId() internal pure override returns (uint256) {
        return 4;
    }

    function executeIntent(
        AllowedSlippage calldata slippage,
        bytes[] calldata actions,
        bytes32, /* zid & affiliate */
        address msgSender,
        bytes calldata sig,
        uint256 prefixLen
    )
        external
        metaTx(msgSender, _hashSlippageAnd(SLIPPAGE_AND_CONDITION_TYPEHASH, actions.slice(prefixLen), slippage))
        returns (bool)
    {
        return _executeMetaTxn(slippage, actions, sig, prefixLen);
    }

    function _witnessTypeSuffix() internal pure override returns (string memory) {
        return string(
            abi.encodePacked(
                "SlippageAndCondition slippageAndCondition)", SLIPPAGE_AND_CONDITION_TYPE, TOKEN_PERMISSIONS_TYPE
            )
        );
    }
}
