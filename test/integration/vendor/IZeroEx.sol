// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";

/// @dev Feature to composably transform between ERC20 tokens.
interface ITransformERC20Feature {
    /// @dev Defines a transformation to run in `transformERC20()`.
    struct Transformation {
        // The deployment nonce for the transformer.
        // The address of the transformer contract will be derived from this
        // value.
        uint32 deploymentNonce;
        // Arbitrary data to pass to the transformer.
        bytes data;
    }

    /// @dev Arguments for `_transformERC20()`.
    struct TransformERC20Args {
        // The taker address.
        address payable taker;
        // The token being provided by the taker.
        // If `0xeee...`, ETH is implied and should be provided with the call.`
        IERC20 inputToken;
        // The token to be acquired by the taker.
        // `0xeee...` implies ETH.
        IERC20 outputToken;
        // The amount of `inputToken` to take from the taker.
        // If set to `uint256(-1)`, the entire spendable balance of the taker
        // will be solt.
        uint256 inputTokenAmount;
        // The minimum amount of `outputToken` the taker
        // must receive for the entire transformation to succeed. If set to zero,
        // the minimum output token transfer will not be asserted.
        uint256 minOutputTokenAmount;
        // The transformations to execute on the token balance(s)
        // in sequence.
        Transformation[] transformations;
        // Whether to use the Exchange Proxy's balance of `inputToken`.
        bool useSelfBalance;
        // The recipient of the bought `outputToken`.
        address payable recipient;
    }
}

interface IMetaTransactionsFeatureV2 {
    /// @dev Describes an exchange proxy meta transaction.
    struct MetaTransactionFeeData {
        // ERC20 fee recipient
        address recipient;
        // ERC20 fee amount
        uint256 amount;
    }

    struct MetaTransactionDataV2 {
        // Signer of meta-transaction. On whose behalf to execute the MTX.
        address payable signer;
        // Required sender, or NULL for anyone.
        address sender;
        // MTX is invalid after this time.
        uint256 expirationTimeSeconds;
        // Nonce to make this MTX unique.
        uint256 salt;
        // Encoded call data to a function on the exchange proxy.
        bytes callData;
        // ERC20 fee `signer` pays `sender`.
        IERC20 feeToken;
        // ERC20 fees.
        MetaTransactionFeeData[] fees;
    }
}

interface IZeroEx {
    function sellTokenForTokenToUniswapV3(
        bytes memory encodedPath,
        uint256 sellAmount,
        uint256 minBuyAmount,
        address recipient
    ) external returns (uint256 buyAmount);

    // Identifies the type of subcall.
    enum MultiplexSubcall {
        Invalid,
        RFQ,
        OTC,
        UniswapV2,
        UniswapV3,
        LiquidityProvider,
        TransformERC20,
        BatchSell,
        MultiHopSell
    }

    // Represents a constituent call of a batch sell.
    struct BatchSellSubcall {
        // The function to call.
        MultiplexSubcall id;
        // Amount of input token to sell. If the highest bit is 1,
        // this value represents a proportion of the total
        // `sellAmount` of the batch sell. See `_normalizeSellAmount`
        // for details.
        uint256 sellAmount;
        // ABI-encoded parameters needed to perform the call.
        bytes data;
    }

    function multiplexBatchSellTokenForToken(
        IERC20 inputToken,
        IERC20 outputToken,
        BatchSellSubcall[] calldata calls,
        uint256 sellAmount,
        uint256 minBuyAmount
    ) external returns (uint256 boughtAmount);

    function sellToLiquidityProvider(
        IERC20 inputToken,
        IERC20 outputToken,
        address provider,
        address recipient,
        uint256 sellAmount,
        uint256 minBuyAmount,
        bytes calldata auxiliaryData
    ) external payable returns (uint256 boughtAmount);

    function transformERC20(
        IERC20 inputToken,
        IERC20 outputToken,
        uint256 inputTokenAmount,
        uint256 minOutputTokenAmount,
        ITransformERC20Feature.Transformation[] calldata transformations
    ) external payable returns (uint256 outputTokenAmount);

    struct LimitOrder {
        IERC20 makerToken;
        IERC20 takerToken;
        uint128 makerAmount;
        uint128 takerAmount;
        uint128 takerTokenFeeAmount;
        address maker;
        address taker;
        address sender;
        address feeRecipient;
        bytes32 pool;
        uint64 expiry;
        uint256 salt;
    }

    /// @dev An RFQ limit order.
    struct RfqOrder {
        IERC20 makerToken;
        IERC20 takerToken;
        uint128 makerAmount;
        uint128 takerAmount;
        address maker;
        address taker;
        address txOrigin;
        bytes32 pool;
        uint64 expiry;
        uint256 salt;
    }

    /// @dev An OTC limit order.
    struct OtcOrder {
        IERC20 makerToken;
        IERC20 takerToken;
        uint128 makerAmount;
        uint128 takerAmount;
        address maker;
        address taker;
        address txOrigin;
        uint256 expiryAndNonce; // [uint64 expiry, uint64 nonceBucket, uint128 nonce]
    }

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

    function fillOtcOrder(OtcOrder calldata order, Signature calldata makerSignature, uint128 takerTokenFillAmount)
        external
        returns (uint128 takerTokenFilledAmount, uint128 makerTokenFilledAmount);

    function getOtcOrderHash(IZeroEx.OtcOrder memory order) external view returns (bytes32 orderHash);
    function lastOtcTxOriginNonce(address txOrigin, uint64 nonceBucket) external view returns (uint128 lastNonce);

    function getMetaTransactionV2Hash(IMetaTransactionsFeatureV2.MetaTransactionDataV2 calldata mtx)
        external
        view
        returns (bytes32 mtxHash);
    function executeMetaTransactionV2(
        IMetaTransactionsFeatureV2.MetaTransactionDataV2 calldata mtx,
        Signature calldata signature
    ) external returns (bytes memory returnResult);
}

interface IFillQuoteTransformer {
    /// @dev Whether we are performing a market sell or buy.
    enum Side {
        Sell,
        Buy
    }

    enum OrderType {
        Bridge,
        Limit,
        Rfq,
        Otc
    }

    struct LimitOrderInfo {
        IZeroEx.LimitOrder order;
        IZeroEx.Signature signature;
        // Maximum taker token amount of this limit order to fill.
        uint256 maxTakerTokenFillAmount;
    }

    struct RfqOrderInfo {
        IZeroEx.RfqOrder order;
        IZeroEx.Signature signature;
        // Maximum taker token amount of this limit order to fill.
        uint256 maxTakerTokenFillAmount;
    }

    struct OtcOrderInfo {
        IZeroEx.OtcOrder order;
        IZeroEx.Signature signature;
        // Maximum taker token amount of this limit order to fill.
        uint256 maxTakerTokenFillAmount;
    }

    /// @dev Transform data to ABI-encode and pass into `transform()`.
    struct TransformData {
        // Whether we are performing a market sell or buy.
        Side side;
        // The token being sold.
        // This should be an actual token, not the ETH pseudo-token.
        IERC20 sellToken;
        // The token being bought.
        // This should be an actual token, not the ETH pseudo-token.
        IERC20 buyToken;
        // External liquidity bridge orders. Sorted by fill sequence.
        IBridgeAdapter.BridgeOrder[] bridgeOrders;
        // Native limit orders. Sorted by fill sequence.
        LimitOrderInfo[] limitOrders;
        // Native RFQ orders. Sorted by fill sequence.
        RfqOrderInfo[] rfqOrders;
        // The sequence to fill the orders in. Each item will fill the next
        // order of that type in either `bridgeOrders`, `limitOrders`,
        // or `rfqOrders.`
        OrderType[] fillSequence;
        // Amount of `sellToken` to sell or `buyToken` to buy.
        // For sells, setting the high-bit indicates that
        // `sellAmount & LOW_BITS` should be treated as a `1e18` fraction of
        // the current balance of `sellToken`, where
        // `1e18+ == 100%` and `0.5e18 == 50%`, etc.
        uint256 fillAmount;
        // Who to transfer unused protocol fees to.
        // May be a valid address or one of:
        // `address(0)`: Stay in flash wallet.
        // `address(1)`: Send to the taker.
        // `address(2)`: Send to the sender (caller of `transformERC20()`).
        address payable refundReceiver;
        // Otc orders. Sorted by fill sequence.
        OtcOrderInfo[] otcOrders;
    }
}

interface IBridgeAdapter {
    struct BridgeOrder {
        // Upper 16 bytes: uint128 protocol ID (right-aligned)
        // Lower 16 bytes: ASCII source name (left-aligned)
        bytes32 source;
        uint256 takerTokenAmount;
        uint256 makerTokenAmount;
        bytes bridgeData;
    }
}

library BridgeProtocols {
    // A incrementally increasing, append-only list of protocol IDs.
    // We don't use an enum so solidity doesn't throw when we pass in a
    // new protocol ID that hasn't been rolled up yet.
    uint128 internal constant UNKNOWN = 0;
    uint128 internal constant CURVE = 1;
    uint128 internal constant UNISWAPV2 = 2;
    uint128 internal constant UNISWAP = 3;
    uint128 internal constant BALANCER = 4;
    uint128 internal constant KYBER = 5; // Not used: deprecated.
    uint128 internal constant MOONISWAP = 6;
    uint128 internal constant MSTABLE = 7;
    uint128 internal constant OASIS = 8; // Not used: deprecated.
    uint128 internal constant SHELL = 9;
    uint128 internal constant DODO = 10;
    uint128 internal constant DODOV2 = 11;
    uint128 internal constant CRYPTOCOM = 12;
    uint128 internal constant BANCOR = 13;
    uint128 internal constant COFIX = 14; // Not used: deprecated.
    uint128 internal constant NERVE = 15;
    uint128 internal constant MAKERPSM = 16;
    uint128 internal constant BALANCERV2 = 17;
    uint128 internal constant UNISWAPV3 = 18;
    uint128 internal constant KYBERDMM = 19;
    uint128 internal constant CURVEV2 = 20;
    uint128 internal constant LIDO = 21;
    uint128 internal constant CLIPPER = 22; // Not used: Clipper is now using PLP interface
    uint128 internal constant AAVEV2 = 23;
    uint128 internal constant COMPOUND = 24;
    uint128 internal constant BALANCERV2BATCH = 25;
    uint128 internal constant GMX = 26;
    uint128 internal constant PLATYPUS = 27;
    uint128 internal constant BANCORV3 = 28;
    uint128 internal constant SOLIDLY = 29;
    uint128 internal constant SYNTHETIX = 30;
    uint128 internal constant WOOFI = 31;
    uint128 internal constant AAVEV3 = 32;
    uint128 internal constant KYBERELASTIC = 33;
}
