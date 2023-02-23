// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;

import "./VeriAuctionTokenForEth_problems_setup.t.sol";

contract VeriAuctionTokenForEth_problems_test is VeriAuctionTokenForEth_problems_setup {
    //========================================
    // Variables
    //========================================

    //========================================
    // Setup
    //========================================

    function setUp() public {
        veriAuctionTokenForEth_problems_setup();
        startAuction();
    }

    //========================================
    // Tests
    //========================================

    //====================
    // commitTokens()
    //
    // TODO: Add more tests of edge cases and reverting paths
    //====================

    function test_commitTokens_updatesCommitment(uint256 ethToCommit) public {
        //----------
        // Setup
        //----------

        vm.assume(ethToCommit > 0);
        vm.assume(type(uint256).max / 10**token.decimals() >= ethToCommit);

        vm.deal(alice, ethToCommit);

        //----------
        // Execute
        //----------

        vm.prank(alice);
        veriAuction.commitEth{value: ethToCommit}();

        //----------
        // Test
        //----------

        vm.prank(alice);
        uint256 commitedAmount = veriAuction.getCommitment();

        assertEq(commitedAmount, ethToCommit);
    }

    //====================
    // resignFromAuction()
    //
    // TODO: Add more tests of edge cases and reverting paths
    //====================

    function test_resignFromAuction_whenAuctionNotFinalReturnsEth(address payable commiter, uint256 ethToCommit)
        public
    {
        //----------
        // Setup
        //----------

        vm.assume(isPayable(commiter));
        vm.assume(commiter != address(0));
        vm.assume(commiter != address(utils));
        vm.assume(commiter != address(token));
        vm.assume(commiter != address(veriAuction));

        commitEthToAuction(commiter, ethToCommit);
        uint256 initialAuctionEthBalance = address(veriAuction).balance;
        assertEq(
            initialAuctionEthBalance,
            ethToCommit,
            "testResignFromAuctionWhenAuctionNotFinalReturnsEth: commitEthToAuction() does not work as expected"
        );

        uint256 initialCommiterEthBalance = commiter.balance;

        //----------
        // Execute
        //----------

        vm.prank(commiter);
        veriAuction.resignFromAuction();

        //----------
        // Test
        //----------

        uint256 newAuctionEthBalance = address(veriAuction).balance;
        assertEq(initialAuctionEthBalance - ethToCommit, newAuctionEthBalance);

        uint256 newCommiterEthBalance = commiter.balance;
        assertEq(initialCommiterEthBalance + ethToCommit, newCommiterEthBalance);
    }

    //====================
    // claimTokens()
    //
    // TODO: Add more tests of edge cases and reverting paths
    //====================

    function test_claimTokens_canNotClaimIfAuctionNotFinalized(address caller) public {
        //----------
        // Setup
        //----------

        vm.expectRevert("VeriAuctionTokenForEth (claimTokens): Auction not finalized yet");

        //----------
        // Execute
        //----------

        vm.prank(caller);
        veriAuction.claimTokens();

        //----------
        // Test
        //----------

        // Succedes if function reverts with string
    }

    function test_claimTokens_canClaimTokens(
        address payable commiter1,
        address payable commiter2,
        uint256 ethToCommit
    ) public {
        //----------
        // Setup
        //----------

        vm.assume(commiter1 != commiter2);
        checkCommiterAddress(commiter1);
        checkCommiterAddress(commiter2);

        commitEthToAuction(commiter1, ethToCommit);
        commitEthToAuction(commiter2, ethToCommit);

        assertEq(token.balanceOf(commiter1), 0);
        assertEq(token.balanceOf(commiter2), 0);

        veriAuction.finalize();

        //----------
        // Execute
        //----------

        vm.prank(commiter1);
        veriAuction.claimTokens();

        //----------
        // Test
        //----------

        assertEq(token.balanceOf(commiter1), amountOfTokensToDistribute / 2);
        assertEq(token.balanceOf(commiter2), 0);
        assertEq(commiter1.balance, 0);
        assertEq(address(veriAuction).balance, 2 * ethToCommit);
    }
}
