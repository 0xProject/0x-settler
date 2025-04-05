// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";

import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {UnsafeMath} from "../utils/UnsafeMath.sol";
import {revertTooMuchSlippage} from "./SettlerErrors.sol";

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
}

// Maker units https://github.com/makerdao/dss/blob/master/DEVELOPING.md
// wad: fixed point decimal with 18 decimals (for basic quantities, e.g. balances)
uint256 constant WAD = 10 ** 18;

IERC20 constant DAI = IERC20(0x6B175474E89094C44Da98b954EedeAC495271d0F);
IERC20 constant USDC = IERC20(0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48);
IPSM constant LitePSM = IPSM(0xf6e72Db5454dd049d0788e411b06CfAF16853042);

abstract contract MakerPSM is SettlerAbstract {
    using UnsafeMath for uint256;
    using SafeTransferLib for IERC20;
    using FastPSM for IPSM;

    uint256 private immutable USDC_basis;

    constructor() {
        assert(block.chainid == 1 || block.chainid == 31337);
        DAI.safeApprove(address(LitePSM), type(uint256).max);
        // LitePSM is its own join
        USDC.safeApprove(address(LitePSM), type(uint256).max);
        USDC_basis = 10 ** USDC.decimals();
    }

    function sellToMakerPsm(address recipient, uint256 bps, bool buyGem, uint256 amountOutMin)
        internal
        returns (uint256 buyAmount)
    {
        if (buyGem) {
            unchecked {
                // phantom overflow can't happen here because DAI has decimals = 18
                uint256 sellAmount = (DAI.fastBalanceOf(address(this)) * bps).unsafeDiv(BASIS);

                uint256 feeDivisor = LitePSM.tout() + WAD; // eg. 1.001 * 10 ** 18 with 0.1% fee [tout is in wad];
                // overflow can't happen at all because DAI is reasonable and PSM prohibits gemToken with decimals > 18
                buyAmount = (sellAmount * USDC_basis).unsafeDiv(feeDivisor);
                if (buyAmount < amountOutMin) {
                    revertTooMuchSlippage(USDC, amountOutMin, buyAmount);
                }

                // DAI.safeApproveIfBelow(address(LitePSM), sellAmount);
                LitePSM.fastBuyGem(recipient, buyAmount);
            }
        } else {
            // phantom overflow can't happen here because PSM prohibits gemToken with decimals > 18
            uint256 sellAmount;
            unchecked {
                sellAmount = (USDC.fastBalanceOf(address(this)) * bps).unsafeDiv(BASIS);
            }
            // USDC.safeApproveIfBelow(LitePSM.gemJoin(), sellAmount);
            buyAmount = LitePSM.fastSellGem(recipient, sellAmount);
            if (buyAmount < amountOutMin) {
                revertTooMuchSlippage(DAI, amountOutMin, buyAmount);
            }
        }
    }
}
