// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;
pragma abicoder v2;

import "@smart-contracts/interfaces/IVeriAuctionTokenForEth.sol";
import "@openzeppelin/contracts/token/ERC20/extensions/IERC20Metadata.sol";
import "@openzeppelin/contracts/access/Ownable.sol";

contract VeriAuctionTokenForEth_problems is IVeriAuctionTokenForEth, Ownable {
    //========================================
    // Variables
    //========================================

    IERC20Metadata public immutable auctionToken;
    uint256 public immutable amountToDistribute;

    // Store this separately to not have to do an external call.
    uint256 private immutable auctionTokenDecimals;

    bool auctionStarted;
    uint256 finalEthBalance;
    mapping(address => uint256) private commited;

    uint256 unclaimableTokenAmount;

    //========================================
    // constructor
    //========================================
    constructor(address veriTokenAddress, uint256 _amountToDistribute) Ownable() {
        auctionToken = IERC20Metadata(veriTokenAddress);
        auctionTokenDecimals = 18; // auctionToken.decimals();

        require(
            _amountToDistribute >= 10**auctionTokenDecimals,
            "VeriAuctionTokenForEth (constructor): must distribute at least one whole token"
        );
        require(
            type(uint256).max / _amountToDistribute >= 1e18,
            "VeriAuctionTokenForEth (constructor): size if _amountToDistribute could cause an overflow when claiming tokens"
        );

        amountToDistribute = _amountToDistribute;
        auctionStarted = false;
        finalEthBalance = 0;
        unclaimableTokenAmount = 0;
    }

    //========================================
    // functions: IVeriAuctionTokenForEth
    //========================================

    //====================
    // Auction unstarted
    //====================

    function depositAuctionTokens() external onlyOwner {
        // The deployer of this auction contract should have approved the auction
        // contract to transfer the auction token before deploying this contract.
        auctionToken.transferFrom(msg.sender, address(this), amountToDistribute);
        auctionStarted = true;
    }

    //====================
    // Auction active
    //====================

    //==========
    // External
    //==========

    /// @inheritdoc IVeriAuctionTokenForEth
    function commitEth() external payable override {
        require(auctionStarted, "VeriAuctionTokenForEth (commitEth): Auction not started");
        require(!auctionFinalized(), "VeriAuctionTokenForEth (commitEth): Auction is finalized");
        require(msg.value > 0, "VeriAuctionTokenForEth (commitEth): commitment must be greater than 0");
        require(
            type(uint256).max / 10**auctionTokenDecimals >= getEthBalance(),
            "VeriAuctionTokenForEth (commitEth): would result in too much ETH in the auction"
        );
        require(
            type(uint256).max / 1e18 >= commited[msg.sender] + msg.value,
            "VeriAuctionTokenForEth (commitEth): would result is a too large commitment"
        );

        // Notice that no total counter is used.
        // This means that ETH can be send to the contract by another contract
        // that calls selfdestruct with the fund address set to this address.
        // Such an action would increase the price of the auction token.
        commited[msg.sender] += msg.value;

        emit Commited(msg.sender, msg.value, getEthBalance(), getCurrentPrice());
    }

    /// @inheritdoc IVeriAuctionTokenForEth
    function resignFromAuction() external override {
        require(commited[msg.sender] > 0, "VeriAuctionTokenForEth (resignFromAuction): must have commited some ETH");

        if (auctionFinalized()) {
            // Gas savings
            uint256 _unclaimableTokenAmount = unclaimableTokenAmount;
            _unclaimableTokenAmount += calculateClaimableAmount();
            require(
                _unclaimableTokenAmount <= amountToDistribute,
                "VeriAuctionTokenForEth (resignFromAuction): unclaimable amount would be larger than total tokens to distribute"
            );
            unclaimableTokenAmount = _unclaimableTokenAmount;
        }

        uint256 commitment = commited[msg.sender];
        require(
            getEthBalance() >= commitment,
            "VeriAuctionTokenForEth (resignFromAuction): contract doesn't have enough ETH"
        );

        // In these three lines the re-entrancy attack happens.
        (bool transferSuccess, ) = msg.sender.call{value: commitment}("");
        require(transferSuccess, "VeriAuctionTokenForEth (resignFromAuction): failed to send ETH");

        delete commited[msg.sender];
    }

    /// @notice The auction is closed and the total amount if ETH is fixed.
    function finalize() external onlyOwner {
        require(auctionStarted, "VeriAuctionTokenForEth (finalize): Auction not started");
        finalEthBalance = getEthBalance();
    }

    //====================
    // Auction Final
    //====================

    //==========
    // External
    //==========

    /// @inheritdoc IVeriAuctionTokenForEth
    function claimTokens() external override {
        require(auctionFinalized(), "VeriAuctionTokenForEth (claimTokens): Auction not finalized yet");

        uint256 claimableAmount = calculateClaimableAmount();

        // The writer of this functino might think that using the delete before the transfer prevents
        // a re-entrancy attack. It actually succeedes in doing that. But it can still be part of another
        // attack.
        // These two lines can also be part of the re-entrancy attack in resignFromAuction().
        // Than not only ETH was stolen, but the attacker would also get its share of the auction tokens.
        delete commited[msg.sender];
        auctionToken.transfer(msg.sender, claimableAmount);
    }

    /// @notice The owner can claim the tokens that will not be distrubuted due to people resigning.
    /// @dev User the delete keyword to get some gas back.
    function claimUndistributedAuctionTokens() external onlyOwner {
        uint256 tokensToSend = unclaimableTokenAmount;
        delete unclaimableTokenAmount;

        // The transfer will fail on insufficient balance
        auctionToken.transfer(owner(), tokensToSend);
    }

    //====================
    // Helpers
    //====================

    //==========
    // External
    //==========

    function getCommitment() external view returns (uint256) {
        return commited[msg.sender];
    }

    //==========
    // Public
    //==========
    function auctionFinalized() public view returns (bool finialized) {
        return finalEthBalance > 0;
    }

    /// @notice Calculates the price of one whole auction token in eth.
    /// @dev The use of this.balance make for a possible exploit that can increase the
    ///      price of an auction token.
    function getCurrentPrice() public view returns (uint256 pricePerAuctionToken) {
        require(amountToDistribute > 0, "VeriAuctionTokenForEth (getCurrentPrice): no tokens to distribute");
        require(
            type(uint256).max / 10**auctionTokenDecimals >= getEthBalance(),
            "VeriAuctionTokenForEth (getCurrentPrice): too much ETH in the contract"
        );

        pricePerAuctionToken = (getEthBalance() * 10**auctionTokenDecimals) / amountToDistribute;
    }

    /// @notice Calculate the amount of tokens can be claimed based on the ETH balance in when the auction
    ///         was closed.
    function calculateClaimableAmount() public view returns (uint256 claimableAmount) {
        require(auctionFinalized(), "VeriAuctionTokenForEth (calculateClaimableAmount): auction not finalized yet");

        // Note that if we would have used getCurrentPrice() in the contract, then someone
        // could send eth to the contract using the selfdestruct method and make it so that
        // no one can claim tokens due to getCurrentPrice() reverting.
        // Even though a lot of ETH should be sent to the contract, theoratically it is possible.
        //
        //  Example:
        // claimableAmount = (commited[msg.sender] * 10**auctionTokenDecimals) / getCurrentPrice();

        // We know that share will always be <= 1e18
        // The constructor already takes care of preventing an overflow in (share * amountToDistribute)
        uint256 share = (commited[msg.sender] * 1e18) / finalEthBalance;
        claimableAmount = (share * amountToDistribute) / 1e18;
    }

    //==========
    // internal
    //==========

    /// @notice Get the eth balance of this contract
    function getEthBalance() internal view returns (uint256) {
        // By using simply address(this).balance the eth balance can
        // be influenced by another contract calling selfdestruct and
        // sending its funds to this contract.
        // Increasing the auction token price
        return address(this).balance;
    }
}
