// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {SettlerMetaTxnBase} from "./SettlerMetaTxnBase.sol";

abstract contract SettlerMetaTxn is SettlerMetaTxnBase {
    string internal constant SLIPPAGE_AND_ACTIONS_TYPE =
        "SlippageAndActions(address recipient,address buyToken,uint256 minAmountOut,bytes[] actions)";
    bytes32 internal constant SLIPPAGE_AND_ACTIONS_TYPEHASH =
        0x615e8d716cef7295e75dd3f1f10d679914ad6d7759e8e9459f0109ef75241701;
    string internal constant METATX_WITNESS_TYPE_SUFFIX =
        "SlippageAndActions slippageAndActions)SlippageAndActions(address recipient,address buyToken,uint256 minAmountOut,bytes[] actions)TokenPermissions(address token,uint256 amount)";

    constructor() {
        assert(SLIPPAGE_AND_ACTIONS_TYPEHASH == keccak256(bytes(SLIPPAGE_AND_ACTIONS_TYPE)));
        assert(
            keccak256(bytes(METATX_WITNESS_TYPE_SUFFIX))
                == keccak256(
                    abi.encodePacked(
                        "SlippageAndActions slippageAndActions)", SLIPPAGE_AND_ACTIONS_TYPE, TOKEN_PERMISSIONS_TYPE
                    )
                )
        );
    }

    function _tokenId() internal pure override returns (uint256) {
        return 3;
    }

    function executeMetaTxn(
        AllowedSlippage calldata slippage,
        bytes[] calldata actions,
        bytes32, /* zid & affiliate */
        address msgSender,
        bytes calldata sig
    ) external metaTx(msgSender, _hashSlippageAnd(SLIPPAGE_AND_ACTIONS_TYPEHASH, actions, slippage)) returns (bool) {
        return _executeMetaTxn(slippage, actions, sig, 0);
    }

    function _witnessTypeSuffix() internal pure override returns (string memory) {
        return METATX_WITNESS_TYPE_SUFFIX;
    }
}
