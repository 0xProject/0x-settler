// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Test} from "@forge-std/Test.sol";
import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {MockERC20} from "@solmate/test/utils/mocks/MockERC20.sol";
import {PropAmmMux, IPropAMM} from "src/PropAmmMux.sol";

contract VoidReturnERC20 is MockERC20("Tether", "USDT", 6) {
    function transferFrom(address from, address to, uint256 amount) public override returns (bool) {
        super.transferFrom(from, to, amount);
        assembly ("memory-safe") {
            return(0x00, 0x00)
        }
    }
}

contract MockPropAmm is IPropAMM {
    uint256 public quotedOut;
    uint256 public swapOut;
    bool public revertQuote;
    bool public revertSwap;
    bool public shortQuoteReturn;
    bool public burnGasOnQuote;
    bool public burnGasOnSwap;
    uint256 public quoteCalls;

    function setBehavior(uint256 quotedOut_, uint256 swapOut_, bool revertQuote_, bool revertSwap_) external {
        quotedOut = quotedOut_;
        swapOut = swapOut_;
        revertQuote = revertQuote_;
        revertSwap = revertSwap_;
    }

    function setShortQuoteReturn(bool v) external {
        shortQuoteReturn = v;
    }

    function setBurnGas(bool onQuote, bool onSwap) external {
        burnGasOnQuote = onQuote;
        burnGasOnSwap = onSwap;
    }

    function quote(IERC20, IERC20, uint256) external returns (uint256) {
        quoteCalls++;
        if (burnGasOnQuote) {
            while (true) {}
        }
        if (revertQuote) revert("stale");
        if (shortQuoteReturn) {
            assembly ("memory-safe") {
                return(0x00, 0x10)
            }
        }
        return quotedOut;
    }

    function swap(IERC20 tokenIn, IERC20 tokenOut, uint256 amountIn, uint256, address recipient, uint256)
        external
        returns (uint256)
    {
        if (burnGasOnSwap) {
            while (true) {}
        }
        if (revertSwap) revert("stale");
        require(tokenIn.balanceOf(address(this)) >= amountIn, "not pushed");
        MockERC20(address(tokenOut)).mint(recipient, swapOut);
        return swapOut;
    }
}

contract PropAmmMuxUnitTest is Test {
    PropAmmMux internal mux;
    MockERC20 internal tokenIn;
    MockERC20 internal tokenOut;
    MockPropAmm internal v0;
    MockPropAmm internal v1;
    MockPropAmm internal v2;

    address internal constant PAYER = address(0x1111);
    address internal constant RECIPIENT = address(0x2222);
    IPropAMM internal constant NO_PRIMARY = IPropAMM(address(0));

    function setUp() public {
        mux = new PropAmmMux();
        tokenIn = new MockERC20("In", "IN", 18);
        tokenOut = new MockERC20("Out", "OUT", 18);
        v0 = new MockPropAmm();
        v1 = new MockPropAmm();
        v2 = new MockPropAmm();

        tokenIn.mint(PAYER, 1000 ether);
        vm.prank(PAYER);
        tokenIn.approve(address(mux), type(uint256).max);
    }

    function _backups2() private view returns (IPropAMM[] memory vs) {
        vs = new IPropAMM[](2);
        vs[0] = v1;
        vs[1] = v2;
    }

    function _venues3() private view returns (IPropAMM[] memory vs) {
        vs = new IPropAMM[](3);
        vs[0] = v0;
        vs[1] = v1;
        vs[2] = v2;
    }

    function test_primaryHitsWithoutQuotingBackups() public {
        v0.setBehavior(0, 500, true, false);
        v1.setBehavior(600, 600, false, false);
        v2.setBehavior(700, 700, false, false);

        vm.prank(PAYER);
        mux.swap(
            IERC20(address(tokenIn)), IERC20(address(tokenOut)), 100, 450, RECIPIENT, block.timestamp, v0, _backups2()
        );
        assertEq(v0.quoteCalls(), 0, "primary never quoted");
        assertEq(v1.quoteCalls(), 0, "backup 1 not quoted on primary hit");
        assertEq(v2.quoteCalls(), 0, "backup 2 not quoted on primary hit");
        assertEq(tokenIn.balanceOf(address(v0)), 100);
        assertEq(tokenOut.balanceOf(RECIPIENT), 500);
    }

    function test_primaryReverts_picksHighestBackup() public {
        v0.setBehavior(0, 0, true, true);
        v1.setBehavior(510, 510, false, false);
        v2.setBehavior(530, 530, false, false);

        vm.prank(PAYER);
        mux.swap(
            IERC20(address(tokenIn)), IERC20(address(tokenOut)), 100, 500, RECIPIENT, block.timestamp, v0, _backups2()
        );
        assertEq(tokenIn.balanceOf(address(v0)), 0, "reverted primary transfer rolled back");
        assertEq(tokenIn.balanceOf(address(v2)), 100);
        assertEq(tokenOut.balanceOf(RECIPIENT), 530);
    }

    function test_primaryUnderDelivers_rollsBackAndUsesBackup() public {
        v0.setBehavior(550, 499, false, false);
        v1.setBehavior(505, 505, false, false);
        v2.setBehavior(0, 0, true, true);

        vm.prank(PAYER);
        mux.swap(
            IERC20(address(tokenIn)), IERC20(address(tokenOut)), 100, 500, RECIPIENT, block.timestamp, v0, _backups2()
        );
        assertEq(tokenIn.balanceOf(address(v0)), 0, "under-delivering primary rolled back");
        assertEq(tokenIn.balanceOf(address(v1)), 100);
        assertEq(tokenOut.balanceOf(RECIPIENT), 505);
    }

    function test_bestMode_picksMaxAndSkipsZeroOrShortReturn() public {
        v0.setBehavior(0, 0, false, false);
        v1.setBehavior(999, 999, false, false);
        v1.setShortQuoteReturn(true);
        v2.setBehavior(420, 420, false, false);

        vm.prank(PAYER);
        mux.swap(
            IERC20(address(tokenIn)), IERC20(address(tokenOut)), 100, 0, RECIPIENT, block.timestamp, NO_PRIMARY, _venues3()
        );
        assertEq(tokenIn.balanceOf(address(v2)), 100);
        assertEq(tokenOut.balanceOf(RECIPIENT), 420);
    }

    function test_overQuotingVenue_revertsAgainstItsOwnQuote() public {
        // v0 over-quotes (1000) to beat honest v1 (700), then delivers only minOut (500).
        v0.setBehavior(1000, 500, false, false);
        v1.setBehavior(700, 700, false, false);
        v2.setBehavior(0, 0, true, true);

        vm.prank(PAYER);
        vm.expectRevert(abi.encodeWithSelector(PropAmmMux.InsufficientOutput.selector, 1000, 500));
        mux.swap(
            IERC20(address(tokenIn)), IERC20(address(tokenOut)), 100, 500, RECIPIENT, block.timestamp, NO_PRIMARY, _venues3()
        );
    }

    function test_winningBackupSwapReverts_revertsWholeCall() public {
        v0.setBehavior(600, 600, false, true);
        v1.setBehavior(550, 550, false, false);
        v2.setBehavior(0, 0, true, true);

        vm.prank(PAYER);
        vm.expectRevert("stale");
        mux.swap(
            IERC20(address(tokenIn)), IERC20(address(tokenOut)), 100, 500, RECIPIENT, block.timestamp, NO_PRIMARY, _venues3()
        );
    }

    function test_gasBurningQuote_doesNotStarveHealthyBackup() public {
        v0.setBurnGas(true, false);
        v1.setBehavior(520, 520, false, false);
        v2.setBehavior(0, 0, true, true);

        vm.prank(PAYER);
        mux.swap{gas: 600_000}(
            IERC20(address(tokenIn)), IERC20(address(tokenOut)), 100, 500, RECIPIENT, block.timestamp, NO_PRIMARY, _venues3()
        );
        assertEq(tokenIn.balanceOf(address(v1)), 100);
        assertEq(tokenOut.balanceOf(RECIPIENT), 520);
    }

    function test_gasBurningPrimary_doesNotStarveHealthyBackup() public {
        v0.setBurnGas(false, true);
        v1.setBehavior(520, 520, false, false);
        v2.setBehavior(0, 0, true, true);

        vm.prank(PAYER);
        mux.swap{gas: 700_000}(
            IERC20(address(tokenIn)), IERC20(address(tokenOut)), 100, 500, RECIPIENT, block.timestamp, v0, _backups2()
        );
        assertEq(tokenIn.balanceOf(address(v0)), 0);
        assertEq(tokenIn.balanceOf(address(v1)), 100);
        assertEq(tokenOut.balanceOf(RECIPIENT), 520);
    }

    function test_zeroQuotesAllBelowMinOutAndEmpty_revertNoLiveVenue() public {
        v0.setBehavior(0, 0, false, false);
        v1.setBehavior(0, 0, true, true);
        v2.setBehavior(0, 0, false, false);

        vm.prank(PAYER);
        vm.expectRevert(PropAmmMux.NoLiveVenue.selector);
        mux.swap(
            IERC20(address(tokenIn)), IERC20(address(tokenOut)), 100, 0, RECIPIENT, block.timestamp, NO_PRIMARY, _venues3()
        );

        v0.setBehavior(490, 490, false, false);
        v1.setBehavior(499, 499, false, false);
        uint256 balBefore = tokenIn.balanceOf(PAYER);
        vm.prank(PAYER);
        vm.expectRevert(PropAmmMux.NoLiveVenue.selector);
        mux.swap(
            IERC20(address(tokenIn)), IERC20(address(tokenOut)), 100, 500, RECIPIENT, block.timestamp, NO_PRIMARY, _venues3()
        );
        assertEq(tokenIn.balanceOf(PAYER), balBefore);

        IPropAMM[] memory empty = new IPropAMM[](0);
        vm.prank(PAYER);
        vm.expectRevert(PropAmmMux.NoLiveVenue.selector);
        mux.swap(
            IERC20(address(tokenIn)), IERC20(address(tokenOut)), 100, 1, RECIPIENT, block.timestamp, NO_PRIMARY, empty
        );
    }

    function test_security_nonSelfTrySwap_thirdPartyCaller_andWeirdVenues() public {
        vm.prank(PAYER);
        vm.expectRevert(PropAmmMux.OnlySelf.selector);
        mux._trySwap(v0, PAYER, IERC20(address(tokenIn)), IERC20(address(tokenOut)), 100, 1, RECIPIENT, block.timestamp);

        // Third party with zero balance cannot spend PAYER's standing allowance to mux.
        v0.setBehavior(500, 500, false, false);
        address attacker = address(0xbad);
        vm.prank(attacker);
        vm.expectRevert();
        mux.swap(
            IERC20(address(tokenIn)), IERC20(address(tokenOut)), 100, 500, attacker, block.timestamp, v0, _backups2()
        );
        assertEq(tokenIn.balanceOf(PAYER), 1000 ether);

        // Venues set to mux or token addresses and duplicates are handled cleanly.
        v1.setBehavior(510, 510, false, false);
        IPropAMM[] memory weird = new IPropAMM[](4);
        weird[0] = IPropAMM(address(mux));
        weird[1] = IPropAMM(address(tokenIn));
        weird[2] = v1;
        weird[3] = v1;

        vm.prank(PAYER);
        mux.swap(
            IERC20(address(tokenIn)), IERC20(address(tokenOut)), 100, 500, RECIPIENT, block.timestamp, NO_PRIMARY, weird
        );
        assertEq(tokenOut.balanceOf(RECIPIENT), 510);
    }

    function test_voidReturnToken_succeeds() public {
        VoidReturnERC20 usdt = new VoidReturnERC20();
        usdt.mint(PAYER, 1000);
        vm.prank(PAYER);
        usdt.approve(address(mux), type(uint256).max);

        v0.setBehavior(500, 500, false, false);
        v1.setBehavior(0, 0, true, true);
        v2.setBehavior(0, 0, true, true);

        vm.prank(PAYER);
        mux.swap(
            IERC20(address(usdt)), IERC20(address(tokenOut)), 100, 500, RECIPIENT, block.timestamp, NO_PRIMARY, _venues3()
        );
        assertEq(usdt.balanceOf(address(v0)), 100);
        assertEq(tokenOut.balanceOf(RECIPIENT), 500);
    }

    function testFuzz_swap_picksMaxAndEnforcesQuote(
        bool usePrimary,
        uint64 pSwap,
        uint64 q1,
        uint64 s1,
        uint64 q2,
        uint64 minOut
    ) public {
        v0.setBehavior(0, pSwap, true, pSwap == 0);
        v1.setBehavior(q1, s1, q1 == 0, false);
        v2.setBehavior(q2, q2, q2 == 0, false);

        vm.prank(PAYER);
        if (usePrimary && pSwap > 0 && pSwap >= minOut) {
            mux.swap(
                IERC20(address(tokenIn)), IERC20(address(tokenOut)), 100, minOut, RECIPIENT, block.timestamp, v0, _backups2()
            );
            assertEq(tokenOut.balanceOf(RECIPIENT), pSwap);
            return;
        }

        IPropAMM primary = usePrimary ? v0 : NO_PRIMARY;
        bool v1Eligible = q1 > 0 && q1 >= minOut;
        bool v2Eligible = q2 > 0 && q2 >= minOut;

        if (!v1Eligible && !v2Eligible) {
            vm.expectRevert(PropAmmMux.NoLiveVenue.selector);
            mux.swap(
                IERC20(address(tokenIn)), IERC20(address(tokenOut)), 100, minOut, RECIPIENT, block.timestamp, primary, _backups2()
            );
        } else if (v1Eligible && (!v2Eligible || q1 >= q2)) {
            if (s1 < q1) {
                vm.expectRevert(abi.encodeWithSelector(PropAmmMux.InsufficientOutput.selector, q1, s1));
            }
            mux.swap(
                IERC20(address(tokenIn)), IERC20(address(tokenOut)), 100, minOut, RECIPIENT, block.timestamp, primary, _backups2()
            );
            if (s1 >= q1) assertEq(tokenOut.balanceOf(RECIPIENT), s1);
        } else {
            mux.swap(
                IERC20(address(tokenIn)), IERC20(address(tokenOut)), 100, minOut, RECIPIENT, block.timestamp, primary, _backups2()
            );
            assertEq(tokenOut.balanceOf(RECIPIENT), q2);
        }
    }
}
