// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";

import {SettlerBasePairTest} from "./SettlerBasePairTest.t.sol";
import {ICurveV2Pool} from "./vendor/ICurveV2Pool.sol";
import {IZeroEx} from "./vendor/IZeroEx.sol";

import {LibBytes} from "../utils/LibBytes.sol";
import {ActionDataBuilder} from "../utils/ActionDataBuilder.sol";

import {SafeTransferLib} from "src/vendor/SafeTransferLib.sol";

import {IAllowanceHolder} from "src/allowanceholder/IAllowanceHolder.sol";
import {Settler} from "src/Settler.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {RfqOrderSettlement} from "src/core/RfqOrderSettlement.sol";

abstract contract AllowanceHolderPairTest is SettlerBasePairTest {
    using SafeTransferLib for IERC20;
    using LibBytes for bytes;

    function setUp() public virtual override {
        super.setUp();
        // Trusted Forwarder / Allowance Holder
        safeApproveIfBelow(fromToken(), FROM, address(allowanceHolder), amount());
        safeApproveIfBelow(toToken(), FROM, address(allowanceHolder), amount());
        safeApproveIfBelow(toToken(), MAKER, address(PERMIT2), amount());
    }

    function uniswapV3Path() internal virtual returns (bytes memory);
    function uniswapV2Pool() internal virtual returns (address);

    function testAllowanceHolder_uniswapV3() public skipIf(uniswapV3Path().length == 0) {
        bytes[] memory actions = ActionDataBuilder.build(
            // Perform a transfer into Settler via AllowanceHolder
            abi.encodeCall(
                ISettlerActions.TRANSFER_FROM,
                (
                    address(settler),
                    defaultERC20PermitTransfer(address(fromToken()), amount(), 0 /* nonce */ ),
                    new bytes(0) /* sig (empty) */
                )
            ),
            // Execute UniswapV3 from the Settler balance
            abi.encodeCall(ISettlerActions.UNISWAPV3, (FROM, 10_000, uniswapV3Path(), 0))
        );

        IAllowanceHolder _allowanceHolder = allowanceHolder;
        Settler _settler = settler;
        IERC20 _fromToken = fromToken();
        uint256 _amount = amount();
        //_warm_allowanceHolder_slots(address(fromToken()), amount());

        vm.startPrank(FROM, FROM); // prank both msg.sender and tx.origin
        snapStartName("allowanceHolder_uniswapV3");
        //_cold_account_access();

        _allowanceHolder.exec(
            address(_settler),
            address(_fromToken),
            _amount,
            payable(address(_settler)),
            abi.encodeCall(
                _settler.execute,
                (
                    ISettlerBase.AllowedSlippage({
                        recipient: payable(address(0)),
                        buyToken: IERC20(address(0)),
                        minAmountOut: 0 ether
                    }),
                    actions,
                    bytes32(0)
                )
            )
        );
        snapEnd();
    }

    function testAllowanceHolder_uniswapV3VIP() public skipIf(uniswapV3Path().length == 0) {
        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(
                // Perform a transfer into directly to the UniswapV3 pool via AllowanceHolder on demand
                ISettlerActions.UNISWAPV3_VIP,
                (
                    FROM,
                    defaultERC20PermitTransfer(address(fromToken()), amount(), 0 /* nonce */ ),
                    uniswapV3Path(),
                    new bytes(0), // sig (empty)
                    0
                )
            )
        );

        IAllowanceHolder _allowanceHolder = allowanceHolder;
        Settler _settler = settler;
        IERC20 _fromToken = fromToken();
        uint256 _amount = amount();
        //_warm_allowanceHolder_slots(address(fromToken()), amount());

        vm.startPrank(FROM, FROM); // prank both msg.sender and tx.origin
        snapStartName("allowanceHolder_uniswapV3VIP");
        //_cold_account_access();

        _allowanceHolder.exec(
            address(_settler),
            address(_fromToken),
            _amount,
            payable(address(_settler)),
            abi.encodeCall(
                _settler.execute,
                (
                    ISettlerBase.AllowedSlippage({
                        recipient: payable(address(0)),
                        buyToken: IERC20(address(0)),
                        minAmountOut: 0 ether
                    }),
                    actions,
                    bytes32(0)
                )
            )
        );
        snapEnd();
    }

    function testAllowanceHolder_uniswapV3VIP_contract() public skipIf(uniswapV3Path().length == 0) {
        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(
                // Perform a transfer into directly to the UniswapV3 pool via AllowanceHolder on demand
                ISettlerActions.UNISWAPV3_VIP,
                (
                    FROM,
                    defaultERC20PermitTransfer(address(fromToken()), amount(), 0 /* nonce */ ),
                    uniswapV3Path(),
                    new bytes(0), // sig (empty)
                    0
                )
            )
        );

        IAllowanceHolder _allowanceHolder = allowanceHolder;
        Settler _settler = settler;
        IERC20 _fromToken = fromToken();
        uint256 _amount = amount();
        //_warm_allowanceHolder_slots(address(fromToken()), amount());

        vm.startPrank(FROM); // Do not prank tx.origin, msg.sender != tx.origin
        snapStartName("allowanceHolder_uniswapV3VIP_contract");
        //_cold_account_access();

        _allowanceHolder.exec(
            address(_settler),
            address(_fromToken),
            _amount,
            payable(address(_settler)),
            abi.encodeCall(
                _settler.execute,
                (
                    ISettlerBase.AllowedSlippage({
                        recipient: payable(address(0)),
                        buyToken: IERC20(address(0)),
                        minAmountOut: 0 ether
                    }),
                    actions,
                    bytes32(0)
                )
            )
        );
        snapEnd();
    }

    function testAllowanceHolder_rfq_VIP() public skipIf(true) { // action `RFQ_VIP` is disabled
        ISignatureTransfer.PermitTransferFrom memory makerPermit =
            defaultERC20PermitTransfer(address(toToken()), amount(), PERMIT2_MAKER_NONCE);
        ISignatureTransfer.PermitTransferFrom memory takerPermit =
            defaultERC20PermitTransfer(address(fromToken()), amount(), 0);

        RfqOrderSettlement.Consideration memory makerConsideration = RfqOrderSettlement.Consideration({
            token: fromToken(),
            amount: amount(),
            counterparty: FROM,
            partialFillAllowed: false
        });

        bytes32 makerWitness = keccak256(bytes.concat(CONSIDERATION_TYPEHASH, abi.encode(makerConsideration)));
        bytes memory makerSig = getPermitWitnessTransferSignature(
            makerPermit, address(settler), MAKER_PRIVATE_KEY, RFQ_PERMIT2_WITNESS_TYPEHASH, makerWitness, permit2Domain
        );

        bytes memory takerSig = new bytes(0);

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.RFQ_VIP, (FROM, takerPermit, makerPermit, MAKER, makerSig, takerSig))
        );

        IAllowanceHolder _allowanceHolder = allowanceHolder;
        Settler _settler = settler;
        IERC20 _fromToken = fromToken();
        uint256 _amount = amount();
        //_warm_allowanceHolder_slots(address(_fromToken), _amount);

        vm.startPrank(FROM, FROM);
        snapStartName("allowanceHolder_rfq");
        //_cold_account_access();

        _allowanceHolder.exec(
            address(_settler),
            address(_fromToken),
            _amount,
            payable(address(_settler)),
            abi.encodeCall(
                _settler.execute,
                (
                    ISettlerBase.AllowedSlippage({
                        recipient: payable(address(0)),
                        buyToken: IERC20(address(0)),
                        minAmountOut: 0 ether
                    }),
                    actions,
                    bytes32(0)
                )
            )
        );
        snapEnd();
    }

    function testAllowanceHolder_rfq_proportionalFee() public {
        ISignatureTransfer.PermitTransferFrom memory makerPermit =
            defaultERC20PermitTransfer(address(toToken()), amount(), PERMIT2_MAKER_NONCE);
        ISignatureTransfer.PermitTransferFrom memory takerPermit =
            defaultERC20PermitTransfer(address(fromToken()), amount(), 0);

        RfqOrderSettlement.Consideration memory makerConsideration = RfqOrderSettlement.Consideration({
            token: fromToken(),
            amount: amount(),
            counterparty: FROM,
            partialFillAllowed: true
        });

        bytes32 makerWitness = keccak256(bytes.concat(CONSIDERATION_TYPEHASH, abi.encode(makerConsideration)));
        bytes memory makerSig = getPermitWitnessTransferSignature(
            makerPermit, address(settler), MAKER_PRIVATE_KEY, RFQ_PERMIT2_WITNESS_TYPEHASH, makerWitness, permit2Domain
        );

        bytes memory takerSig = new bytes(0);

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.TRANSFER_FROM, (address(settler), takerPermit, takerSig)),
            abi.encodeCall(
                ISettlerActions.BASIC,
                (
                    address(fromToken()),
                    1_000,
                    address(fromToken()),
                    0x24,
                    abi.encodeCall(fromToken().transfer, (BURN_ADDRESS, 0))
                )
            ),
            abi.encodeCall(ISettlerActions.RFQ, (FROM, makerPermit, MAKER, makerSig, address(fromToken()), amount()))
        );

        IAllowanceHolder _allowanceHolder = allowanceHolder;
        Settler _settler = settler;
        IERC20 _fromToken = fromToken();
        uint256 _amount = amount();
        //_warm_allowanceHolder_slots(address(_fromToken), _amount);

        vm.startPrank(FROM, FROM);
        snapStartName("allowanceHolder_rfq_proportionalFee_sellToken");
        //_cold_account_access();

        _allowanceHolder.exec(
            address(_settler),
            address(_fromToken),
            _amount,
            payable(address(_settler)),
            abi.encodeCall(
                _settler.execute,
                (
                    ISettlerBase.AllowedSlippage({
                        recipient: payable(address(0)),
                        buyToken: IERC20(address(0)),
                        minAmountOut: 0 ether
                    }),
                    actions,
                    bytes32(0)
                )
            )
        );
        snapEnd();
    }

    function testAllowanceHolder_uniswapV2_single_chain() public skipIf(uniswapV2Pool() == address(0)) {
        // |7|6|5|4|3|2|1|0| - bit positions in swapInfo (uint8)
        // |0|0|0|0|0|0|F|Z| - Z: zeroForOne flag, F: sellTokenHasFee flag
        bool sellTokenHasFee = false;
        uint24 swapInfo = (address(fromToken()) < address(toToken()) ? 1 : 0) | (sellTokenHasFee ? 2 : 0) | (30 << 8);

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(
                ISettlerActions.TRANSFER_FROM,
                (
                    uniswapV2Pool(),
                    defaultERC20PermitTransfer(address(fromToken()), amount(), 0 /* nonce */ ),
                    new bytes(0) /* sig (empty) */
                )
            ),
            abi.encodeCall(ISettlerActions.UNISWAPV2, (FROM, address(fromToken()), 0, uniswapV2Pool(), swapInfo, 0))
        );

        IAllowanceHolder _allowanceHolder = allowanceHolder;
        Settler _settler = settler;
        IERC20 _fromToken = fromToken();
        uint256 _amount = amount();
        _warm_allowanceHolder_slots(address(fromToken()), amount());

        vm.startPrank(FROM); // Do not prank tx.origin, msg.sender != tx.origin
        snapStartName("allowanceHolder_uniswapV2_single_chain");
        _cold_account_access();

        _allowanceHolder.exec(
            address(_settler),
            address(_fromToken),
            _amount,
            payable(address(_settler)),
            abi.encodeCall(
                _settler.execute,
                (
                    ISettlerBase.AllowedSlippage({
                        recipient: payable(address(0)),
                        buyToken: IERC20(address(0)),
                        minAmountOut: 0 ether
                    }),
                    actions,
                    bytes32(0)
                )
            )
        );
        snapEnd();
    }

    function testAllowanceHolder_empty() public {
        bytes[] memory actions = new bytes[](0);
        bytes memory call = abi.encodeCall(
            settler.execute,
            (
                ISettlerBase.AllowedSlippage({
                    recipient: payable(address(0)),
                    buyToken: IERC20(address(0)),
                    minAmountOut: 0 ether
                }),
                actions,
                bytes32(0)
            )
        );

        IAllowanceHolder _allowanceHolder = allowanceHolder;
        Settler _settler = settler;

        vm.startPrank(FROM, FROM);
        snapStartName("allowanceHolder_empty");
        _allowanceHolder.exec(address(0), address(0), 0, payable(address(_settler)), call);
        snapEnd();
    }

    /// @dev With a future deployment with EIP1153 these storage slots will be transient
    /// and therefor cost the same as if they were already warm
    /// TODO should we keep this on of have it as a flag if we deploy prior to EIP1153
    function _warm_allowanceHolder_slots(address token, uint256 amount) internal {
        bytes32 allowedSlot = keccak256(abi.encodePacked(address(settler), FROM, token));
        bytes32 allowedValue = bytes32(amount);
        vm.store(address(allowanceHolder), allowedSlot, allowedValue);
    }

    function _cold_account_access() internal {
        // `_warm_allowanceHolder_slots` also warms the whole `AllowanceHolder`
        // account. in order to pretend that we didn't just do that, we do a
        // cold account access inside the metered path. this costs an
        // erroneously-extra 100 gas.
        assembly ("memory-safe") {
            let _pop := call(gas(), 0xdead, 0, 0x00, 0x00, 0x00, 0x00)
        }
    }
}
