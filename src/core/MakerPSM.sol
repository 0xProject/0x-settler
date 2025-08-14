// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";

import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {UnsafeMath} from "../utils/UnsafeMath.sol";
import {revertTooMuchSlippage} from "./SettlerErrors.sol";
import {Ternary} from "../utils/Ternary.sol";

import {SettlerAbstract} from "../SettlerAbstract.sol";

interface IPSM {
    /// @dev Get the fee for selling DAI to USDC in PSM
    /// @return tout toll out [wad]
    function tout() external view returns (uint256);

    /// @dev Get the address of the underlying vault powering PSM
    /// @return address of gemJoin contract
    function gemJoin() external view returns (address);

    /// @dev Sell USDC for DAI
    /// @param usr The address of the account trading USDC for DAI.
    /// @param gemAmt The amount of USDC to sell in USDC base units
    /// @return daiOutWad The amount of Dai bought.
    function sellGem(address usr, uint256 gemAmt) external returns (uint256 daiOutWad);

    /// @dev Buy USDC for DAI
    /// @param usr The address of the account trading DAI for USDC
    /// @param gemAmt The amount of USDC to buy in USDC base units
    /// @return daiInWad The amount of Dai required to sell.
    function buyGem(address usr, uint256 gemAmt) external returns (uint256 daiInWad);
}

library FastPSM {
    function fastSellGem(IPSM psm, address usr, uint256 gemAmt) internal returns (uint256 daiOutWad) {
        assembly ("memory-safe") {
            mstore(0x34, gemAmt)
            mstore(0x14, usr)
            mstore(0x00, 0x95991276000000000000000000000000) // selector for `sellGem(address,uint256)` with `usr`'s padding

            if iszero(call(gas(), psm, 0x00, 0x10, 0x44, 0x00, 0x20)) {
                let ptr := and(0xffffffffffffffffffffffff, mload(0x40))
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
            if iszero(gt(returndatasize(), 0x1f)) { revert(0x00, 0x00) }

            mstore(0x34, 0x00)
            daiOutWad := mload(0x00)
        }
    }

    function fastBuyGem(IPSM psm, address usr, uint256 gemAmt) internal returns (uint256 daiInWad) {
        assembly ("memory-safe") {
            mstore(0x34, gemAmt)
            mstore(0x14, usr)
            mstore(0x00, 0x8d7ef9bb000000000000000000000000) // selector for `buyGem(address,uint256)` with `usr`'s padding

            if iszero(call(gas(), psm, 0x00, 0x10, 0x44, 0x00, 0x20)) {
                let ptr := and(0xffffffffffffffffffffffff, mload(0x40))
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
            if iszero(gt(returndatasize(), 0x1f)) { revert(0x00, 0x00) }

            mstore(0x34, 0x00)
            daiInWad := mload(0x00)
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
IPSM constant LitePSM = IPSM(0xf6e72Db5454dd049d0788e411b06CfAF16853042);
IPSM constant SkyPSM = IPSM(0xA188EEC8F81263234dA3622A406892F3D630f98c);

abstract contract MakerPSM is SettlerAbstract {
    using UnsafeMath for uint256;
    using SafeTransferLib for IERC20;
    using FastPSM for IPSM;
    using Ternary for bool;

    uint256 private constant USDC_basis = 1_000_000;

    constructor() {
        assert(block.chainid == 1 || block.chainid == 31337);
        assert(USDC_basis == 10 ** USDC.decimals());
        DAI.safeApprove(address(LitePSM), type(uint256).max);
        USDS.safeApprove(address(SkyPSM), type(uint256).max);
        // LitePSM is its own join
        USDC.safeApprove(address(LitePSM), type(uint256).max);
        // SkyPSM is its own join
        USDC.safeApprove(address(SkyPSM), type(uint256).max);
    }

    function sellToMakerPsm(address recipient, uint256 bps, bool buyGem, uint256 amountOutMin, IPSM psm, IERC20 dai)
        internal
        returns (uint256 buyAmount)
    {
        // If `psm/dai` is not `SkyPSM/USDS` or `LitePSM/DAI`, this interaction will likely fail
        // as those pairs are the ones with configured approvals in the constructor.
        (IERC20 sellToken, IERC20 buyToken) = buyGem.maybeSwap(USDC, dai);
        uint256 sellAmount;
        unchecked {
            // phantom overflow can't happen here because:
            // 1. sellToken has decimals = 18 (sellToken is DAI or USDS)
            // 2. PSM prohibits gemToken with decimals > 18 (sellToken is USDC)
            sellAmount = (sellToken.fastBalanceOf(address(this)) * bps).unsafeDiv(BASIS);
        }
        if (buyGem) {
            unchecked {
                uint256 feeDivisor = psm.fastTout() + WAD; // eg. 1.001 * 10 ** 18 with 0.1% fee [tout is in wad];
                // overflow can't happen at all because DAI and USDS are reasonable and PSM prohibits gemToken with decimals > 18
                buyAmount = (sellAmount * USDC_basis).unsafeDiv(feeDivisor);
                if (buyAmount < amountOutMin) {
                    revertTooMuchSlippage(buyToken, amountOutMin, buyAmount);
                }

                // dai.safeApproveIfBelow(address(psm), sellAmount);
                psm.fastBuyGem(recipient, buyAmount);
            }
        } else {
            // USDC.safeApproveIfBelow(psm.gemJoin(), sellAmount);
            buyAmount = psm.fastSellGem(recipient, sellAmount);
            if (buyAmount < amountOutMin) {
                revertTooMuchSlippage(buyToken, amountOutMin, buyAmount);
            }
        }
    }
}
