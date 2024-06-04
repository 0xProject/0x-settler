// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20, IERC20Meta} from "../IERC20.sol";

import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {UnsafeMath} from "../utils/UnsafeMath.sol";

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
    function sellGem(address usr, uint256 gemAmt) external;

    /// @dev Buy USDC for DAI
    /// @param usr The address of the account trading DAI for USDC
    /// @param gemAmt The amount of USDC to buy in USDC base units
    function buyGem(address usr, uint256 gemAmt) external;
}

abstract contract MakerPSM {
    using UnsafeMath for uint256;
    using SafeTransferLib for IERC20;
    using SafeTransferLib for IERC20Meta;

    // Maker units https://github.com/makerdao/dss/blob/master/DEVELOPING.md
    // wad: fixed point decimal with 18 decimals (for basic quantities, e.g. balances)
    uint256 internal constant WAD = 10 ** 18;

    IERC20 internal constant DAI = IERC20(0x6B175474E89094C44Da98b954EedeAC495271d0F);

    constructor() {
        assert(block.chainid == 1 || block.chainid == 31337);
    }

    function sellToMakerPsm(address recipient, IERC20Meta gemToken, uint256 bps, IPSM psm, bool buyGem) internal {
        if (buyGem) {
            // phantom overflow can't happen here because DAI has decimals = 18
            uint256 sellAmount = (DAI.balanceOf(address(this)) * bps).unsafeDiv(10_000);
            unchecked {
                uint256 feeDivisor = psm.tout() + WAD; // eg. 1.001 * 10 ** 18 with 0.1% fee [tout is in wad];
                // overflow can't happen at all because DAI is reasonable and PSM prohibits gemToken with decimals > 18
                uint256 buyAmount = (sellAmount * 10 ** uint256(gemToken.decimals())).unsafeDiv(feeDivisor);

                DAI.safeApproveIfBelow(address(psm), sellAmount);
                psm.buyGem(recipient, buyAmount);
            }
        } else {
            // phantom overflow can't happen here because PSM prohibits gemToken with decimals > 18
            uint256 sellAmount = (gemToken.balanceOf(address(this)) * bps).unsafeDiv(10_000);
            gemToken.safeApproveIfBelow(psm.gemJoin(), sellAmount);
            psm.sellGem(recipient, sellAmount);
        }
    }
}
