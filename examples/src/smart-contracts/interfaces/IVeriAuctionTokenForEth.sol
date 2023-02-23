// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;

interface IVeriAuctionTokenForEth {
    //========================================
    // Events
    //========================================
    event Commited(address indexed user, uint256 amount, uint256 totalCommited, uint256 newPrice);
    event Claimed(address indexed user, uint256 amount, uint256 price);

    //========================================
    // Functions
    //========================================

    // TODO: Add natspec and indicate which functions emit which event.

    /// @notice Commit a certain amount of ETH.
    /// @custom:emits Commited
    function commitEth() external payable;

    /// @notice Let a user resign from the auction.
    ///         As long as the auction is not finalized this will decrease the price of an auction token.
    ///         When the auction is finalized the price can't change anymore (due to the ETH balance being recorded).
    ///         Instead, when the auction is finalized, the otherwise claimable auction tokens can be withdrawn from
    ///         the contract by the owner of the contract.
    /// @dev User the delete keyword to get some gas back.
    /// @custom:emits fdsfdsfds
    function resignFromAuction() external;

    /// @notice Claim an amount of tokens based of the share of a user
    function claimTokens() external;
}
