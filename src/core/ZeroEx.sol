// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {ERC20} from "solmate/src/tokens/ERC20.sol";

import {SafeTransferLib} from "../utils/SafeTransferLib.sol";

interface IZeroEx {
    /// @dev Allowed signature types.
    enum SignatureType {
        ILLEGAL,
        INVALID,
        EIP712,
        ETHSIGN,
        PRESIGNED
    }

    /// @dev Encoded EC signature.
    struct Signature {
        // How to validate the signature.
        SignatureType signatureType;
        // EC Signature data.
        uint8 v;
        // EC Signature data.
        bytes32 r;
        // EC Signature data.
        bytes32 s;
    }

    /// @dev An OTC limit order.
    struct OtcOrder {
        ERC20 makerToken;
        ERC20 takerToken;
        uint128 makerAmount;
        uint128 takerAmount;
        address maker;
        address taker;
        address txOrigin;
        uint256 expiryAndNonce; // [uint64 expiry, uint64 nonceBucket, uint128 nonce]
    }

    function fillOtcOrder(OtcOrder calldata order, Signature calldata makerSignature, uint128 takerTokenFillAmount)
        external
        returns (uint128 takerTokenFilledAmount, uint128 makerTokenFilledAmount);
}

abstract contract ZeroEx {
    using SafeTransferLib for ERC20;

    IZeroEx private immutable ZERO_EX;

    constructor(address zeroEx) {
        ZERO_EX = IZeroEx(zeroEx);
    }

    function sellTokenForTokenToZeroExOTC(
        IZeroEx.OtcOrder memory order,
        IZeroEx.Signature memory signature,
        uint256 sellAmount
    ) internal {
        order.takerToken.safeApproveIfBelow(address(ZERO_EX), type(uint256).max);
        ZERO_EX.fillOtcOrder(order, signature, uint128(sellAmount));
    }
}
