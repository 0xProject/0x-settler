// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Test} from "@forge-std/Test.sol";
import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ERC20} from "@solmate/tokens/ERC20.sol";
import {Permit2PaymentTakerSubmitted} from "src/core/Permit2Payment.sol";
import {Permit2PaymentAbstract} from "src/core/Permit2PaymentAbstract.sol";
import {uint512} from "src/utils/512Math.sol";
import {Renegade, ARBITRUM_SELECTOR, BASE_SELECTOR} from "src/core/Renegade.sol";
import {Utils} from "../Utils.sol";

abstract contract RenegadeDummy is Permit2PaymentTakerSubmitted, Renegade {
    function sell(address target, IERC20 sellToken, bool baseForQuote, bytes memory data, uint256 minBuyAmount)
        public
        payable
    {
        sellToRenegade(target, sellToken, baseForQuote, data, minBuyAmount);
    }

    function _tokenId() internal pure override returns (uint256) {
        revert("unimplemented");
    }

    function _hasMetaTxn() internal pure override returns (bool) {
        return false;
    }

    function _dispatch(uint256, uint256, bytes calldata, AllowedSlippage memory) internal pure override returns (bool) {
        revert("unimplemented");
    }

    function _div512to256(uint512, uint512) internal view override returns (uint256) {
        revert("unimplemented");
    }

    function _isRestrictedTarget(address target)
        internal
        view
        override(Permit2PaymentTakerSubmitted, Permit2PaymentAbstract)
        returns (bool)
    {
        return super._isRestrictedTarget(target);
    }
}

contract RenegadeArbitrumDummy is RenegadeDummy {
    function _renegadeSelector() internal pure override returns (uint32) {
        return ARBITRUM_SELECTOR;
    }
}

contract RenegadeBaseDummy is RenegadeDummy {
    function _renegadeSelector() internal pure override returns (uint32) {
        return BASE_SELECTOR;
    }
}

abstract contract RenegadeTest is Utils, Test {
    uint256 chainId;
    uint32 selector;
    RenegadeDummy renegade;
    address target = makeAddr("target");
    address token = makeAddr("token");

    constructor(uint256 _chainId) {
        chainId = _chainId;
    }

    function setUp() public virtual {
        // select test chain
        vm.chainId(chainId);

        // configure chain
        bytes memory renegadeCreationCode;
        if (chainId == 42161) {
            selector = ARBITRUM_SELECTOR;
            renegadeCreationCode = type(RenegadeArbitrumDummy).creationCode;
        } else if (chainId == 8453) {
            selector = BASE_SELECTOR;
            renegadeCreationCode = type(RenegadeBaseDummy).creationCode;
        } else {
            revert("unsupported chain");
        }

        // deploy renegade contract
        address _renegade;
        assembly ("memory-safe") {
            _renegade := create(0x00, add(0x20, renegadeCreationCode), mload(renegadeCreationCode))
            if iszero(_renegade) { revert(0x00, 0x00) }
        }
        renegade = RenegadeDummy(_renegade);
    }

    function testSellNative() public {
        uint256 amount = 2000;

        _mockExpectCall(target, amount, abi.encodeWithSelector(bytes4(selector), amount, amount), new bytes(0));
        renegade.sell{value: amount}(
            target, IERC20(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE), false, abi.encode(amount * 2, amount * 2), 0
        );
    }

    function testSellQuote() public {
        uint256 amount = 3000;

        _mockExpectCall(target, abi.encodeWithSelector(bytes4(selector), amount, amount * 2 / 3), new bytes(0));
        _mockExpectCall(token, abi.encodeCall(IERC20.balanceOf, (address(renegade))), abi.encode(amount));
        _mockExpectCall(token, abi.encodeCall(IERC20.allowance, (address(renegade), target)), abi.encode(0));
        _mockExpectCall(token, abi.encodeCall(IERC20.approve, (target, type(uint256).max)), new bytes(0));
        renegade.sell(target, IERC20(token), false, abi.encode(amount * 3, amount * 2), 0);
    }

    function testSellBase() public {
        // Test selling the base asset (word 1). Data = (quoteAmount=6000, baseAmount=9000).
        // newSellAmount (base balance) = 3000.
        // baseForQuote = true:
        //   newBaseAmount = 3000
        //   newQuoteAmount = 6000 * 3000 / 9000 = 2000
        //   buyAmount = newQuoteAmount = 2000
        // Expected call to GasSponsor: (newQuoteAmount=2000, newBaseAmount=3000)
        uint256 amount = 3000;

        _mockExpectCall(target, abi.encodeWithSelector(bytes4(selector), amount * 2 / 3, amount), new bytes(0));
        _mockExpectCall(token, abi.encodeCall(IERC20.balanceOf, (address(renegade))), abi.encode(amount));
        _mockExpectCall(token, abi.encodeCall(IERC20.allowance, (address(renegade), target)), abi.encode(0));
        _mockExpectCall(token, abi.encodeCall(IERC20.approve, (target, type(uint256).max)), new bytes(0));
        renegade.sell(target, IERC20(token), true, abi.encode(amount * 2, amount * 3), 0);
    }
}

contract RenegadeArbitrumUnitTest is RenegadeTest(42161) {}

contract RenegadeBaseUnitTest is RenegadeTest(8453) {}
