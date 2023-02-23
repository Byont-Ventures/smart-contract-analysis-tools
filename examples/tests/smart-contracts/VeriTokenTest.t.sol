// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;

import "forge-std/Test.sol";
import "./Utils/Utils.sol";
import "@smart-contracts/VeriToken.sol";

contract VeriTokenTest is Test {
    //======================================================
    // Events
    //======================================================
    event Transfer(address indexed from, address indexed to, uint256 value);

    //======================================================
    // Variables
    //======================================================
    Utils utils;
    VeriToken veriToken;

    //=======================================================
    // setup
    //=======================================================

    function setUp() public {
        // vm comes from Test -> Script
        utils = new Utils(vm);
        veriToken = new VeriToken();
    }

    //=======================================================
    // tests
    //=======================================================

    //===========================
    // decimals
    //===========================

    function test_decimals_returnsCorrect() public {
        assertEq(veriToken.decimals(), 6);
    }

    //===========================
    // mint
    //===========================

    function test_mint_canMintToSender(address user, uint256 amount) public {
        vm.assume(user != address(0));
        assertEq(veriToken.balanceOf(user), 0);

        vm.expectEmit(true, true, false, true);
        emit Transfer(address(0), user, amount);

        vm.prank(user);
        veriToken.mint(amount);

        assertEq(veriToken.balanceOf(user), amount);
    }

    function test_mint_revertsOnSenderAddressZero() public {
        vm.expectRevert("ERC20: mint to the zero address");

        vm.prank(address(0));
        veriToken.mint(123);
    }
}
