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

    string internal constant SLIPPAGE_AND_CONDITION_TYPE =
        "SlippageAndCondition(address recipient,address buyToken,uint256 minAmountOut,bytes[] condition)";
    bytes32 internal constant SLIPPAGE_AND_CONDITION_TYPEHASH =
        0x24a8d1e812d61f4d1c5a389ec4379906a57587add93708e221ed7965b9ec1c2c;
    string internal constant INTENT_WITNESS_TYPE_SUFFIX =
        "SlippageAndCondition slippageAndCondition)SlippageAndCondition(address recipient,address buyToken,uint256 minAmountOut,bytes[] condition)TokenPermissions(address token,uint256 amount)";

    constructor() {
        assert(SLIPPAGE_AND_CONDITION_TYPEHASH == keccak256(bytes(SLIPPAGE_AND_CONDITION_TYPE)));
        assert(
            keccak256(bytes(INTENT_WITNESS_TYPE_SUFFIX))
                == keccak256(
                    abi.encodePacked(
                        "SlippageAndCondition slippageAndCondition)", SLIPPAGE_AND_CONDITION_TYPE, TOKEN_PERMISSIONS_TYPE
                    )
                )
        );
    }

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
        return INTENT_WITNESS_TYPE_SUFFIX;
    }
}
