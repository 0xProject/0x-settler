// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {ENS} from "../utils/ENS.sol";
import {Panic} from "../utils/Panic.sol";
import {UnsafeMath} from "../utils/UnsafeMath.sol";

import {StalePriceData, PriceTooHigh, PriceTooLow} from "./SettlerErrors.sol";

import {SettlerAbstract} from "../SettlerAbstract.sol";

interface IAggregatorV3 {
    function decimals() external view returns (uint8);
    function latestRoundData()
        external
        view
        returns (uint80 roundId, int256 answer, uint256 /* startedAt */, uint256 updatedAt); // uint80 answeredInRound
}

abstract contract Chainlink is SettlerAbstract {
    using ENS for string;
    using ENS for bytes32;
    using UnsafeMath for int256;
    using UnsafeMath for uint8;

    // keccak256(bytes.concat(
    //     keccak256(bytes.concat(
    //         bytes32(0),
    //         keccak256("eth")
    //     )),
    //     keccak256("data")
    // ))
    bytes32 private constant _DATA_DOT_ETH_NODE = 0x4a9dd6923a809a49d009b308182940df46ac3a45ee16c1133f90db66596dae1f;
    // keccak256("aggregator")
    bytes32 private constant _AGGREGATOR_NODE = 0xe124d7cc79a19705865fa21b784ba187cd393559e960c0c071132cb60354d1a3;

    function consultChainlink(string memory feedName, int256 priceThreshold, uint8 expectedDecimals, uint256 staleThreshold) internal view {
        // namehash of `string.concat("aggregator.", feedName, ".data.eth")`
        bytes32 node;
        assembly ("memory-safe") {
            mstore(0x00, _DATA_DOT_ETH_NODE)
            mstore(0x20, keccak256(add(0x20, feedName), mload(feedName)))
            mstore(0x00, keccak256(0x00, 0x40))
            mstore(0x20, _AGGREGATOR_NODE)
            node := keccak256(0x00, 0x40)
        }

        // resolve the ENS node
        IAggregatorV3 aggregator = IAggregatorV3(node.toAddr());

        // query the oracle
        (uint80 roundId, int256 answer,, uint256 updatedAt) = aggregator.latestRoundData();
        if (roundId == 0 || block.timestamp - updatedAt > staleThreshold) {
            revert StalePriceData(roundId, answer, updatedAt);
        }
        if (answer <= 0) {
            Panic.panic(Panic.ARITHMETIC_OVERFLOW);
        }

        // adjust for decimals
        uint8 decimals = aggregator.decimals();
        if (decimals > expectedDecimals) {
            uint256 shift = decimals.unsafeSub(expectedDecimals);
            if (shift == 255) {
                Panic.panic(Panic.ARITHMETIC_OVERFLOW);
            }
            priceThreshold *= int256(1 << shift);
        } else if (decimals < expectedDecimals) {
            uint256 shift = expectedDecimals.unsafeSub(decimals);
            if (shift == 255) {
                Panic.panic(Panic.ARITHMETIC_OVERFLOW);
            }
            answer *= int256(1 << shift);
        }

        // check the price
        if (priceThreshold < 0) {
            if (priceThreshold.unsafeNeg() > answer) {
                revert PriceTooHigh(answer, priceThreshold.unsafeNeg());
            }
        } else {
            if (priceThreshold < answer) {
                revert PriceTooLow(answer, priceThreshold);
            }
        }
    }
}
