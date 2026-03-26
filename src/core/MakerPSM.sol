// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";

import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {UnsafeMath} from "../utils/UnsafeMath.sol";
import {revertTooMuchSlippage} from "./SettlerErrors.sol";
import {Ternary} from "../utils/Ternary.sol";

import {SettlerSwapAbstract} from "../SettlerAbstract.sol";

interface IPSM {
    /// @dev Fee for selling gem (USDC/USDT) into the PSM
    /// @return tin toll in [wad]
    function tin() external view returns (uint256);

    /// @dev Fee for buying gem (USDC/USDT) from the PSM
    /// @return tout toll out [wad]
    function tout() external view returns (uint256);

    /// @dev Get the address of the underlying vault powering PSM
    /// @return address of gemJoin contract
    function gemJoin() external view returns (address);

    /// @dev Sell gem (USDC/USDT) for dai (DAI/USDS/USDD)
    /// @param usr The address of the account trading gem for dai.
    /// @param gemAmt The amount of gem to sell in gem base units
    /// @return daiOutWad The amount of dai bought.
    function sellGem(address usr, uint256 gemAmt) external returns (uint256 daiOutWad);

    /// @dev Buy gem (USDC/USDT) with dai (DAI/USDS/USDD)
    /// @param usr The address of the account trading dai for gem
    /// @param gemAmt The amount of gem to buy in gem base units
    /// @return daiInWad The amount of dai required to sell.
    function buyGem(address usr, uint256 gemAmt) external returns (uint256 daiInWad);
}

library FastPSM {
    function fastSellGem(IPSM psm, address usr, uint256 gemAmt) internal {
        assembly ("memory-safe") {
            mstore(0x34, gemAmt)
            mstore(0x14, usr)
            mstore(0x00, 0x95991276000000000000000000000000) // selector for `sellGem(address,uint256)` with `usr`'s padding

            if iszero(call(gas(), psm, 0x00, 0x10, 0x44, 0x00, 0x20)) {
                let ptr := and(0xffffffffffffffffffffffff, mload(0x40))
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
            mstore(0x34, 0x00)
        }
    }

    function fastBuyGem(IPSM psm, address usr, uint256 gemAmt) internal {
        assembly ("memory-safe") {
            mstore(0x34, gemAmt)
            mstore(0x14, usr)
            mstore(0x00, 0x8d7ef9bb000000000000000000000000) // selector for `buyGem(address,uint256)` with `usr`'s padding

            if iszero(call(gas(), psm, 0x00, 0x10, 0x44, 0x00, 0x20)) {
                let ptr := and(0xffffffffffffffffffffffff, mload(0x40))
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
            mstore(0x34, 0x00)
        }
    }

    // Unlike fastSellGem/fastBuyGem, `tin()`/`tout()` are present on both LitePSM and classic DssPsm,
    // so we require return data here.
    function fastTin(IPSM psm) internal view returns (uint256 tin) {
        assembly ("memory-safe") {
            mstore(0x00, 0x568d4b6f) // selector for `tin()`

            if iszero(staticcall(gas(), psm, 0x1c, 0x04, 0x00, 0x20)) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
            if iszero(gt(returndatasize(), 0x1f)) { revert(0x00, 0x00) }
            tin := mload(0x00)
        }
    }

    function fastTout(IPSM psm) internal view returns (uint256 tout) {
        assembly ("memory-safe") {
            mstore(0x00, 0xfae036d5) // selector for `tout()`

            if iszero(staticcall(gas(), psm, 0x1c, 0x04, 0x00, 0x20)) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
            if iszero(gt(returndatasize(), 0x1f)) { revert(0x00, 0x00) }
            tout := mload(0x00)
        }
    }
}

// Maker units https://github.com/makerdao/dss/blob/master/DEVELOPING.md
// wad: fixed point decimal with 18 decimals (for basic quantities, e.g. balances)
uint256 constant WAD = 10 ** 18;

IERC20 constant DAI = IERC20(0x6B175474E89094C44Da98b954EedeAC495271d0F);
IERC20 constant USDS = IERC20(0xdC035D45d973E3EC169d2276DDab16f1e407384F);
IERC20 constant USDC = IERC20(0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48);
IERC20 constant USDT = IERC20(0xdAC17F958D2ee523a2206206994597C13D831ec7);
IERC20 constant USDD = IERC20(0x4f8e5DE400DE08B164E7421B3EE387f461beCD1A);
IPSM constant LitePSM = IPSM(0xf6e72Db5454dd049d0788e411b06CfAF16853042);
IPSM constant SkyPSM = IPSM(0xA188EEC8F81263234dA3622A406892F3D630f98c);
IPSM constant UsddPSM = IPSM(0xcE355440c00014A229bbEc030A2B8f8EB45a2897);
address constant UsddGemJoin = 0x217e42CEB2eAE9ECB788fDF0e31c806c531760A3;

abstract contract MakerPSM is SettlerSwapAbstract {
    using UnsafeMath for uint256;
    using SafeTransferLib for IERC20;
    using FastPSM for IPSM;
    using Ternary for bool;

    // USDC and USDT both have 6 decimals, so GEM_basis (1e6) is safe to use for all supported gems.
    uint256 private constant GEM_basis = 1_000_000;

    constructor() {
        assert(block.chainid == 1 || block.chainid == 31337);
        assert(GEM_basis == 10 ** USDC.decimals());
        assert(GEM_basis == 10 ** USDT.decimals());
        // LitePSM is its own join
        DAI.safeApprove(address(LitePSM), type(uint256).max);
        USDC.safeApprove(address(LitePSM), type(uint256).max);
        // SkyPSM is its own join
        USDS.safeApprove(address(SkyPSM), type(uint256).max);
        USDC.safeApprove(address(SkyPSM), type(uint256).max);
        // USDD PSM (classic DssPsm — separate GemJoin)
        USDD.safeApprove(address(UsddPSM), type(uint256).max);
        USDT.safeApprove(UsddGemJoin, type(uint256).max);
    }

    function sellToMakerPsm(address recipient, uint256 bps, bool buyGem, uint256 amountOutMin, IPSM psm, IERC20 dai)
        internal
        returns (uint256 buyAmount)
    {
        // Configured approval pairs: LitePSM/DAI/USDC, SkyPSM/USDS/USDC, UsddPSM/USDD/USDT.
        IERC20 gem = IERC20((psm == UsddPSM).ternary(address(USDT), address(USDC)));
        (IERC20 sellToken, IERC20 buyToken) = buyGem.maybeSwap(gem, dai);
        uint256 sellAmount;
        unchecked {
            // phantom overflow can't happen here because:
            // 1. sellToken has decimals = 18 (sellToken is DAI, USDS, or USDD)
            // 2. PSM prohibits gemToken with decimals > 18 (sellToken is USDC or USDT)
            sellAmount = (sellToken.fastBalanceOf(address(this)) * bps).unsafeDiv(BASIS);
        }
        if (buyGem) {
            unchecked {
                uint256 feeDivisor = psm.fastTout() + WAD; // eg. 1.001 * 10 ** 18 with 0.1% fee [tout is in wad];
                // overflow can't happen at all because DAI, USDS, and USDD are reasonable and PSM prohibits gemToken with decimals > 18
                buyAmount = (sellAmount * GEM_basis).unsafeDiv(feeDivisor);
                if (buyAmount < amountOutMin) {
                    revertTooMuchSlippage(buyToken, amountOutMin, buyAmount);
                }

                psm.fastBuyGem(recipient, buyAmount);
            }
        } else {
            psm.fastSellGem(recipient, sellAmount);
            unchecked {
                buyAmount = sellAmount * WAD / GEM_basis;
                buyAmount -= (buyAmount * psm.fastTin()).unsafeDiv(WAD);
            }
            if (buyAmount < amountOutMin) {
                revertTooMuchSlippage(buyToken, amountOutMin, buyAmount);
            }
        }
    }
}
