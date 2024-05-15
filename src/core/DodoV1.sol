// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "../IERC20.sol";
import {SettlerAbstract} from "../SettlerAbstract.sol";
import {TooMuchSlippage} from "./SettlerErrors.sol";
import {FullMath} from "../vendor/FullMath.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";

interface IDodo {
    function sellBaseToken(uint256 amount, uint256 minReceiveQuote, bytes calldata data) external returns (uint256);
    function buyBaseToken(uint256 amount, uint256 maxPayQuote, bytes calldata data) external returns (uint256);
}

interface IDodoHelper {
    function querySellQuoteToken(IDodo dodo, uint256 amount) external view returns (uint256);
}

abstract contract DodoV1 is SettlerAbstract {
    using FullMath for uint256;
    using SafeTransferLib for IERC20;

    IDodoHelper private constant _dodoHelper = IDodoHelper(0x533dA777aeDCE766CEAe696bf90f8541A4bA80Eb);
    // curl 'https://api.dodoex.io/dodo-contract/list?version=v1,v2' | jq
    // sepolia 0xa1609A1fa7DC16c025feA194c02b2822441b8c10
    // base 0x8eA40e8Da3ae64Bad5E77a5f7DB346499F543baC
    // optimism 0x56f8E27B27BFF96B5203c95977e8982f62bE70C2

    constructor() {
        assert(block.chainid == 1 || block.chainid == 31337);
    }

    function sellToDodoV1(IERC20 sellToken, uint256 bps, address dodo, bool baseNotQuote, uint256 minBuyAmount)
        internal
    {
        uint256 sellAmount = sellToken.balanceOf(address(this)).mulDiv(bps, 10_000);
        sellToken.safeApproveIfBelow(dodo, sellAmount);
        uint256 buyAmount;
        if (baseNotQuote) {
            buyAmount = IDodo(dodo).sellBaseToken(sellAmount, 1 wei, new bytes(0));
        } else {
            buyAmount = _dodoHelper.querySellQuoteToken(IDodo(dodo), sellAmount);
            IDodo(dodo).buyBaseToken(buyAmount, sellAmount, new bytes(0));
        }
        if (buyAmount < minBuyAmount) {
            revert TooMuchSlippage(address(sellToken), minBuyAmount, buyAmount);
        }
    }
}
