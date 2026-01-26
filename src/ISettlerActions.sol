// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";

interface ISettlerActions {
    /// VIP actions should always start with `recipient` address and the permit` from the taker
    /// followed by all the other parameters to ensure compatibility with `executeWithPermit` entrypoint.

    /// @dev Transfer funds from msg.sender Permit2.
    function TRANSFER_FROM(address recipient, ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig)
        external;

    // @dev msgValue is interpreted as an upper bound on the expected msg.value, not as an exact specification
    function NATIVE_CHECK(uint256 deadline, uint256 msgValue) external;

    /// @dev Transfer funds from metatransaction requestor into the Settler contract using Permit2. Only for use in `Settler.executeMetaTxn` where the signature is provided as calldata
    function METATXN_TRANSFER_FROM(address recipient, ISignatureTransfer.PermitTransferFrom memory permit) external;

    /// @dev Settle an RfqOrder between maker and taker transfering funds directly between the parties
    // Post-req: Payout if recipient != taker
    function RFQ_VIP(
        address recipient,
        ISignatureTransfer.PermitTransferFrom memory takerPermit,
        ISignatureTransfer.PermitTransferFrom memory makerPermit,
        address maker,
        bytes memory makerSig,
        bytes memory takerSig
    ) external;

    /// @dev Settle an RfqOrder between maker and taker transfering funds directly between the parties for the entire amount
    function METATXN_RFQ_VIP(
        address recipient,
        ISignatureTransfer.PermitTransferFrom memory takerPermit,
        ISignatureTransfer.PermitTransferFrom memory makerPermit,
        address maker,
        bytes memory makerSig
    ) external;

    /// @dev Settle an RfqOrder between Maker and Settler. Transfering funds from the Settler contract to maker.
    /// Retaining funds in the settler contract.
    // Pre-req: Funded
    // Post-req: Payout
    function RFQ(
        address recipient,
        ISignatureTransfer.PermitTransferFrom memory permit,
        address maker,
        bytes memory makerSig,
        address takerToken,
        uint256 maxTakerAmount
    ) external;

    function UNISWAPV4(
        address recipient,
        address sellToken,
        uint256 bps,
        bool feeOnTransfer,
        uint256 hashMul,
        uint256 hashMod,
        bytes memory fills,
        uint256 amountOutMin
    ) external;
    function UNISWAPV4_VIP(
        address recipient,
        ISignatureTransfer.PermitTransferFrom memory permit,
        bool feeOnTransfer,
        uint256 hashMul,
        uint256 hashMod,
        bytes memory fills,
        bytes memory sig,
        uint256 amountOutMin
    ) external;
    function METATXN_UNISWAPV4_VIP(
        address recipient,
        ISignatureTransfer.PermitTransferFrom memory permit,
        bool feeOnTransfer,
        uint256 hashMul,
        uint256 hashMod,
        bytes memory fills,
        uint256 amountOutMin
    ) external;

    function BALANCERV3(
        address recipient,
        address sellToken,
        uint256 bps,
        bool feeOnTransfer,
        uint256 hashMul,
        uint256 hashMod,
        bytes memory fills,
        uint256 amountOutMin
    ) external;
    function BALANCERV3_VIP(
        address recipient,
        ISignatureTransfer.PermitTransferFrom memory permit,
        bool feeOnTransfer,
        uint256 hashMul,
        uint256 hashMod,
        bytes memory fills,
        bytes memory sig,
        uint256 amountOutMin
    ) external;
    function METATXN_BALANCERV3_VIP(
        address recipient,
        ISignatureTransfer.PermitTransferFrom memory permit,
        bool feeOnTransfer,
        uint256 hashMul,
        uint256 hashMod,
        bytes memory fills,
        uint256 amountOutMin
    ) external;

    function PANCAKE_INFINITY(
        address recipient,
        address sellToken,
        uint256 bps,
        bool feeOnTransfer,
        uint256 hashMul,
        uint256 hashMod,
        bytes memory fills,
        uint256 amountOutMin
    ) external;
    function PANCAKE_INFINITY_VIP(
        address recipient,
        ISignatureTransfer.PermitTransferFrom memory permit,
        bool feeOnTransfer,
        uint256 hashMul,
        uint256 hashMod,
        bytes memory fills,
        bytes memory sig,
        uint256 amountOutMin
    ) external;
    function METATXN_PANCAKE_INFINITY_VIP(
        address recipient,
        ISignatureTransfer.PermitTransferFrom memory permit,
        bool feeOnTransfer,
        uint256 hashMul,
        uint256 hashMod,
        bytes memory fills,
        uint256 amountOutMin
    ) external;

    /// @dev Trades against UniswapV3 using the contracts balance for funding
    // Pre-req: Funded
    // Post-req: Payout
    function UNISWAPV3(address recipient, uint256 bps, bytes memory path, uint256 amountOutMin) external;
    /// @dev Trades against UniswapV3 using user funds via Permit2 for funding
    function UNISWAPV3_VIP(
        address recipient,
        ISignatureTransfer.PermitTransferFrom memory permit,
        bytes memory path,
        bytes memory sig,
        uint256 amountOutMin
    ) external;
    /// @dev Trades against UniswapV3 using user funds via Permit2 for funding. Metatransaction variant. Signature is over all actions.
    function METATXN_UNISWAPV3_VIP(
        address recipient,
        ISignatureTransfer.PermitTransferFrom memory permit,
        bytes memory path,
        uint256 amountOutMin
    ) external;

    function MAKERPSM(address recipient, uint256 bps, bool buyGem, uint256 amountOutMin, address psm, address dai)
        external;

    function CURVE_TRICRYPTO_VIP(
        address recipient,
        ISignatureTransfer.PermitTransferFrom memory permit,
        uint80 poolInfo,
        bytes memory sig,
        uint256 minBuyAmount
    ) external;
    function METATXN_CURVE_TRICRYPTO_VIP(
        address recipient,
        ISignatureTransfer.PermitTransferFrom memory permit,
        uint80 poolInfo,
        uint256 minBuyAmount
    ) external;

    function DODOV1(address sellToken, uint256 bps, address pool, bool quoteForBase, uint256 minBuyAmount) external;
    function DODOV2(
        address recipient,
        address sellToken,
        uint256 bps,
        address pool,
        bool quoteForBase,
        uint256 minBuyAmount
    ) external;

    function VELODROME(address recipient, uint256 bps, address pool, uint24 swapInfo, uint256 minBuyAmount) external;

    /// @dev Trades against MaverickV2 using the contracts balance for funding
    /// This action does not use the MaverickV2 callback, so it takes an arbitrary pool address to make calls against.
    /// Passing `tokenAIn` as a parameter actually saves gas relative to introspecting the pool's `tokenA()` accessor.
    function MAVERICKV2(
        address recipient,
        address sellToken,
        uint256 bps,
        address pool,
        bool tokenAIn,
        int32 tickLimit,
        uint256 minBuyAmount
    ) external;
    /// @dev Trades against MaverickV2, spending the taker's coupon inside the callback
    /// This action requires the use of the MaverickV2 callback, so we take the MaverickV2 CREATE2 salt as an argument to derive the pool address from the trusted factory and inithash.
    /// @param salt is formed as `keccak256(abi.encode(feeAIn, feeBIn, tickSpacing, lookback, tokenA, tokenB, kinds, address(0)))`
    function MAVERICKV2_VIP(
        address recipient,
        ISignatureTransfer.PermitTransferFrom memory permit,
        bytes32 salt,
        bool tokenAIn,
        bytes memory sig,
        int32 tickLimit,
        uint256 minBuyAmount
    ) external;
    /// @dev Trades against MaverickV2, spending the taker's coupon inside the callback; metatransaction variant
    function METATXN_MAVERICKV2_VIP(
        address recipient,
        ISignatureTransfer.PermitTransferFrom memory permit,
        bytes32 salt,
        bool tokenAIn,
        int32 tickLimit,
        uint256 minBuyAmount
    ) external;

    /// @dev Trades against UniswapV2 using the contracts balance for funding
    /// @param swapInfo is encoded as the upper 16 bits as the fee of the pool in bps, the second
    ///                 lowest bit as "sell token has transfer fee", and the lowest bit as the
    ///                 "token0 for token1" flag.
    function UNISWAPV2(
        address recipient,
        address sellToken,
        uint256 bps,
        address pool,
        uint24 swapInfo,
        uint256 amountOutMin
    ) external;

    function POSITIVE_SLIPPAGE(address payable recipient, address token, uint256 expectedAmount, uint256 maxBps)
        external;

    /// @dev Trades against a basic AMM which follows the approval, transferFrom(msg.sender) interaction
    // Pre-req: Funded
    // Post-req: Payout
    function BASIC(address sellToken, uint256 bps, address pool, uint256 offset, bytes calldata data) external;

    function EKUBO(
        address recipient,
        address sellToken,
        uint256 bps,
        bool feeOnTransfer,
        uint256 hashMul,
        uint256 hashMod,
        bytes memory fills,
        uint256 amountOutMin
    ) external;

    function EKUBO_VIP(
        address recipient,
        ISignatureTransfer.PermitTransferFrom memory permit,
        bool feeOnTransfer,
        uint256 hashMul,
        uint256 hashMod,
        bytes memory fills,
        bytes memory sig,
        uint256 amountOutMin
    ) external;

    function METATXN_EKUBO_VIP(
        address recipient,
        ISignatureTransfer.PermitTransferFrom memory permit,
        bool feeOnTransfer,
        uint256 hashMul,
        uint256 hashMod,
        bytes memory fills,
        uint256 amountOutMin
    ) external;

    function EULERSWAP(
        address recipient,
        address sellToken,
        uint256 bps,
        address pool,
        bool zeroForOne,
        uint256 amountOutMin
    ) external;

    function RENEGADE(address target, address baseToken, bytes memory data) external;

    function LFJTM(
        address recipient,
        address sellToken,
        uint256 bps,
        address pool,
        bool zeroForOne,
        uint256 amountOutMin
    ) external;

    struct BebopMakerSignature {
        bytes signatureBytes;
        uint256 flags;
    }

    struct BebopOrder {
        uint256 expiry;
        address maker_address;
        uint256 maker_nonce;
        address maker_token;
        uint256 taker_amount;
        uint256 maker_amount;

        // the high 5 bits are unused
        // the next 3 bits are the `takerHasNative`, `makerHasNative`, and
        //   `takerUsingPermit2` flags (in that order from high to low) from the
        //   original `packed_commands` field
        // the next 120 bits are unused
        // the low 128 bits are the `event_id` from the original `flags` field
        uint256 event_id_and_flags;
    }

    function BEBOP(
        address recipient,
        address sellToken,
        BebopOrder memory order,
        BebopMakerSignature memory makerSignature,
        uint256 amountOutMin
    ) external;

    function HANJI(
        address sellToken,
        uint256 bps,
        address pool,
        uint256 sellScalingFactor,
        uint256 buyScalingFactor,
        bool isAsk,
        uint256 priceLimit,
        uint256 minBuyAmount
    ) external;
}
