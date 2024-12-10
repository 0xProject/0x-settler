// SPDX-License-Identifier: MIT
pragma solidity =0.8.25;

import {SettlerBase} from "../SettlerBase.sol";
import {Settler} from "../Settler.sol";
import {SettlerMetaTxn} from "../SettlerMetaTxn.sol";
import {SettlerIntent} from "../SettlerIntent.sol";

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {DodoV1, IDodoV1} from "../core/DodoV1.sol";
import {DodoV2, IDodoV2} from "../core/DodoV2.sol";
import {FreeMemory} from "../utils/FreeMemory.sol";

import {ISettlerActions} from "../ISettlerActions.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {UnknownForkId} from "../core/SettlerErrors.sol";

import {
    uniswapV3MainnetFactory,
    uniswapV3InitHash,
    uniswapV3ForkId,
    IUniswapV3Callback
} from "../core/univ3forks/UniswapV3.sol";
import {IAlgebraCallback} from "../core/univ3forks/Algebra.sol";
import {sushiswapV3PolygonFactory, sushiswapV3ForkId} from "../core/univ3forks/SushiswapV3.sol";
import {quickSwapV3Factory, quickSwapV3InitHash, quickSwapV3ForkId} from "../core/univ3forks/QuickSwapV3.sol";

// Solidity inheritance is stupid
import {SettlerAbstract} from "../SettlerAbstract.sol";
import {AbstractContext} from "../Context.sol";
import {Permit2PaymentAbstract} from "../core/Permit2PaymentAbstract.sol";
import {Permit2PaymentMetaTxn, Permit2Payment} from "../core/Permit2Payment.sol";

abstract contract PolygonMixin is FreeMemory, SettlerBase, DodoV1, DodoV2 {
    constructor() {
        assert(block.chainid == 137 || block.chainid == 31337);
    }

    function _dispatch(uint256 i, uint256 action, bytes calldata data)
        internal
        virtual
        override(SettlerAbstract, SettlerBase)
        DANGEROUS_freeMemory
        returns (bool)
    {
        if (super._dispatch(i, action, data)) {
            return true;
        } else if (action == uint32(ISettlerActions.DODOV2.selector)) {
            (address recipient, IERC20 sellToken, uint256 bps, IDodoV2 dodo, bool quoteForBase, uint256 minBuyAmount) =
                abi.decode(data, (address, IERC20, uint256, IDodoV2, bool, uint256));

            sellToDodoV2(recipient, sellToken, bps, dodo, quoteForBase, minBuyAmount);
        } else if (action == uint32(ISettlerActions.DODOV1.selector)) {
            (IERC20 sellToken, uint256 bps, IDodoV1 dodo, bool quoteForBase, uint256 minBuyAmount) =
                abi.decode(data, (IERC20, uint256, IDodoV1, bool, uint256));

            sellToDodoV1(sellToken, bps, dodo, quoteForBase, minBuyAmount);
        } else {
            return false;
        }
        return true;
    }

    function _uniV3ForkInfo(uint8 forkId)
        internal
        pure
        override
        returns (address factory, bytes32 initHash, uint32 callbackSelector)
    {
        if (forkId == uniswapV3ForkId) {
            factory = uniswapV3MainnetFactory;
            initHash = uniswapV3InitHash;
            callbackSelector = uint32(IUniswapV3Callback.uniswapV3SwapCallback.selector);
        } else if (forkId == sushiswapV3ForkId) {
            factory = sushiswapV3PolygonFactory;
            initHash = uniswapV3InitHash;
            callbackSelector = uint32(IUniswapV3Callback.uniswapV3SwapCallback.selector);
        } else if (forkId == quickSwapV3ForkId) {
            factory = quickSwapV3Factory;
            initHash = quickSwapV3InitHash;
            callbackSelector = uint32(IAlgebraCallback.algebraSwapCallback.selector);
        } else {
            revert UnknownForkId(forkId);
        }
    }
}

/// @custom:security-contact security@0x.org
contract PolygonSettler is Settler, PolygonMixin {
    constructor(bytes20 gitCommit) SettlerBase(gitCommit) {}

    function _dispatchVIP(uint256 action, bytes calldata data) internal override DANGEROUS_freeMemory returns (bool) {
        return super._dispatchVIP(action, data);
    }

    // Solidity inheritance is stupid
    function _isRestrictedTarget(address target)
        internal
        pure
        override(Settler, Permit2PaymentAbstract)
        returns (bool)
    {
        return super._isRestrictedTarget(target);
    }

    function _dispatch(uint256 i, uint256 action, bytes calldata data)
        internal
        override(SettlerAbstract, SettlerBase, PolygonMixin)
        returns (bool)
    {
        return super._dispatch(i, action, data);
    }

    function _msgSender() internal view override(Settler, AbstractContext) returns (address) {
        return super._msgSender();
    }
}

/// @custom:security-contact security@0x.org
contract PolygonSettlerMetaTxn is SettlerMetaTxn, PolygonMixin {
    constructor(bytes20 gitCommit) SettlerBase(gitCommit) {}

    function _dispatchVIP(uint256 action, bytes calldata data, bytes calldata sig)
        internal
        virtual
        override
        DANGEROUS_freeMemory
        returns (bool)
    {
        return super._dispatchVIP(action, data, sig);
    }

    // Solidity inheritance is stupid
    function _dispatch(uint256 i, uint256 action, bytes calldata data)
        internal
        virtual
        override(SettlerAbstract, SettlerBase, PolygonMixin)
        returns (bool)
    {
        return super._dispatch(i, action, data);
    }

    function _msgSender() internal view virtual override(SettlerMetaTxn, AbstractContext) returns (address) {
        return super._msgSender();
    }
}

/// @custom:security-contact security@0x.org
contract PolygonSettlerIntent is SettlerIntent, PolygonSettlerMetaTxn {
    constructor(bytes20 gitCommit) PolygonSettlerMetaTxn(gitCommit) {}

    // Solidity inheritance is stupid
    function _dispatch(uint256 i, uint256 action, bytes calldata data)
        internal
        override(PolygonSettlerMetaTxn, SettlerBase, SettlerAbstract)
        returns (bool)
    {
        return super._dispatch(i, action, data);
    }

    function _msgSender() internal view override(SettlerIntent, PolygonSettlerMetaTxn) returns (address) {
        return super._msgSender();
    }

    function _witnessTypeSuffix()
        internal
        pure
        override(SettlerIntent, Permit2PaymentMetaTxn)
        returns (string memory)
    {
        return super._witnessTypeSuffix();
    }

    function _tokenId() internal pure override(SettlerIntent, SettlerMetaTxn, SettlerAbstract) returns (uint256) {
        return super._tokenId();
    }

    function _dispatchVIP(uint256 action, bytes calldata data, bytes calldata sig)
        internal
        override(PolygonSettlerMetaTxn, SettlerMetaTxn)
        returns (bool)
    {
        return super._dispatchVIP(action, data, sig);
    }

    function _permitToSellAmount(ISignatureTransfer.PermitTransferFrom memory permit)
        internal
        view
        override(SettlerIntent, Permit2PaymentAbstract, Permit2PaymentMetaTxn)
        returns (uint256)
    {
        return super._permitToSellAmount(permit);
    }
}
