# Code report

## Slither



Compiled with solc

Number of lines: 473 (+ 0 in dependencies, + 0 in tests)

Number of assembly lines: 0

Number of contracts: 6 (+ 0 in dependencies, + 0 tests) 



Number of optimization issues: 0

Number of informational issues: 5

Number of low issues: 1

Number of medium issues: 1

Number of high issues: 4

ERCs: ERC20



For more information about the detected items see the [Slither documentation](https://github.com/crytic/slither/wiki/Detector-Documentation).


### solc-version

- Impact: `Informational`
- Confidence: `High`


### solc-version

- Impact: `Informational`
- Confidence: `High`


```Solidity
// examples/src/smart-contracts/interfaces/IVeriAuctionTokenForEth.sol

2 pragma solidity ^0.8.13;
```

### solc-version

- Impact: `Informational`
- Confidence: `High`


```Solidity
// examples/src/smart-contracts/VeriAuctionTokenForEth_problems.sol

2 pragma solidity ^0.8.13;
```

### low-level-calls

- Impact: `Informational`
- Confidence: `High`


**In Function**

```Solidity
// examples/src/smart-contracts/VeriAuctionTokenForEth_problems.sol

95     function resignFromAuction() external override {
96         require(commited[msg.sender] > 0, "VeriAuctionTokenForEth (resignFromAuction): must have commited some ETH");
97 
98         if (auctionFinalized()) {
99             // Gas savings
100             uint256 _unclaimableTokenAmount = unclaimableTokenAmount;
101             _unclaimableTokenAmount += calculateClaimableAmount();
102             require(
103                 _unclaimableTokenAmount <= amountToDistribute,
104                 "VeriAuctionTokenForEth (resignFromAuction): unclaimable amount would be larger than total tokens to distribute"
105             );
106             unclaimableTokenAmount = _unclaimableTokenAmount;
107         }
108 
109         uint256 commitment = commited[msg.sender];
110         require(
111             getEthBalance() >= commitment,
112             "VeriAuctionTokenForEth (resignFromAuction): contract doesn't have enough ETH"
113         );
114 
115         // In these three lines the re-entrancy attack happens.
116         (bool transferSuccess, ) = msg.sender.call{value: commitment}("");
117         require(transferSuccess, "VeriAuctionTokenForEth (resignFromAuction): failed to send ETH");
118 
119         delete commited[msg.sender];
120     }
```

**Lines of relevance**

```Solidity
// examples/src/smart-contracts/VeriAuctionTokenForEth_problems.sol

116         (bool transferSuccess, ) = msg.sender.call{value: commitment}("");
```

### naming-convention

- Impact: `Informational`
- Confidence: `High`


### reentrancy-benign

- Impact: `Low`
- Confidence: `Medium`


**In Function**

```Solidity
// examples/src/smart-contracts/VeriAuctionTokenForEth_problems.sol

56     function depositAuctionTokens() external onlyOwner {
57         // The deployer of this auction contract should have approved the auction
58         // contract to transfer the auction token before deploying this contract.
59         auctionToken.transferFrom(msg.sender, address(this), amountToDistribute);
60         auctionStarted = true;
61     }
```

**Lines of relevance**

```Solidity
// examples/src/smart-contracts/VeriAuctionTokenForEth_problems.sol

59         auctionToken.transferFrom(msg.sender, address(this), amountToDistribute);
```

**Lines of relevance**

```Solidity
// examples/src/smart-contracts/VeriAuctionTokenForEth_problems.sol

59         auctionToken.transferFrom(msg.sender, address(this), amountToDistribute);
```

**Lines of relevance**

```Solidity
// examples/src/smart-contracts/VeriAuctionTokenForEth_problems.sol

60         auctionStarted = true;
```

### divide-before-multiply

- Impact: `Medium`
- Confidence: `Medium`


**In Function**

```Solidity
// examples/src/smart-contracts/VeriAuctionTokenForEth_problems.sol

195     function calculateClaimableAmount() public view returns (uint256 claimableAmount) {
196         require(auctionFinalized(), "VeriAuctionTokenForEth (calculateClaimableAmount): auction not finalized yet");
197 
198         // Note that if we would have used getCurrentPrice() in the contract, then someone
199         // could send eth to the contract using the selfdestruct method and make it so that
200         // no one can claim tokens due to getCurrentPrice() reverting.
201         // Even though a lot of ETH should be sent to the contract, theoratically it is possible.
202         //
203         //  Example:
204         // claimableAmount = (commited[msg.sender] * 10**auctionTokenDecimals) / getCurrentPrice();
205 
206         // We know that share will always be <= 1e18
207         // The constructor already takes care of preventing an overflow in (share * amountToDistribute)
208         uint256 share = (commited[msg.sender] * 1e18) / finalEthBalance;
209         claimableAmount = (share * amountToDistribute) / 1e18;
210     }
```

**Lines of relevance**

```Solidity
// examples/src/smart-contracts/VeriAuctionTokenForEth_problems.sol

208         uint256 share = (commited[msg.sender] * 1e18) / finalEthBalance;
```

**Lines of relevance**

```Solidity
// examples/src/smart-contracts/VeriAuctionTokenForEth_problems.sol

209         claimableAmount = (share * amountToDistribute) / 1e18;
```

### reentrancy-eth

- Impact: `High`
- Confidence: `Medium`


**In Function**

```Solidity
// examples/src/smart-contracts/VeriAuctionTokenForEth_problems.sol

95     function resignFromAuction() external override {
96         require(commited[msg.sender] > 0, "VeriAuctionTokenForEth (resignFromAuction): must have commited some ETH");
97 
98         if (auctionFinalized()) {
99             // Gas savings
100             uint256 _unclaimableTokenAmount = unclaimableTokenAmount;
101             _unclaimableTokenAmount += calculateClaimableAmount();
102             require(
103                 _unclaimableTokenAmount <= amountToDistribute,
104                 "VeriAuctionTokenForEth (resignFromAuction): unclaimable amount would be larger than total tokens to distribute"
105             );
106             unclaimableTokenAmount = _unclaimableTokenAmount;
107         }
108 
109         uint256 commitment = commited[msg.sender];
110         require(
111             getEthBalance() >= commitment,
112             "VeriAuctionTokenForEth (resignFromAuction): contract doesn't have enough ETH"
113         );
114 
115         // In these three lines the re-entrancy attack happens.
116         (bool transferSuccess, ) = msg.sender.call{value: commitment}("");
117         require(transferSuccess, "VeriAuctionTokenForEth (resignFromAuction): failed to send ETH");
118 
119         delete commited[msg.sender];
120     }
```

**Lines of relevance**

```Solidity
// examples/src/smart-contracts/VeriAuctionTokenForEth_problems.sol

116         (bool transferSuccess, ) = msg.sender.call{value: commitment}("");
```

**Lines of relevance**

```Solidity
// examples/src/smart-contracts/VeriAuctionTokenForEth_problems.sol

119         delete commited[msg.sender];
```

### unchecked-transfer

- Impact: `High`
- Confidence: `Medium`


**In Function**

```Solidity
// examples/src/smart-contracts/VeriAuctionTokenForEth_problems.sol

137     function claimTokens() external override {
138         require(auctionFinalized(), "VeriAuctionTokenForEth (claimTokens): Auction not finalized yet");
139 
140         uint256 claimableAmount = calculateClaimableAmount();
141 
142         // The writer of this functino might think that using the delete before the transfer prevents
143         // a re-entrancy attack. It actually succeedes in doing that. But it can still be part of another
144         // attack.
145         // These two lines can also be part of the re-entrancy attack in resignFromAuction().
146         // Than not only ETH was stolen, but the attacker would also get its share of the auction tokens.
147         delete commited[msg.sender];
148         auctionToken.transfer(msg.sender, claimableAmount);
149     }
```

**Lines of relevance**

```Solidity
// examples/src/smart-contracts/VeriAuctionTokenForEth_problems.sol

148         auctionToken.transfer(msg.sender, claimableAmount);
```

### unchecked-transfer

- Impact: `High`
- Confidence: `Medium`


**In Function**

```Solidity
// examples/src/smart-contracts/VeriAuctionTokenForEth_problems.sol

153     function claimUndistributedAuctionTokens() external onlyOwner {
154         uint256 tokensToSend = unclaimableTokenAmount;
155         delete unclaimableTokenAmount;
156 
157         // The transfer will fail on insufficient balance
158         auctionToken.transfer(owner(), tokensToSend);
159     }
```

**Lines of relevance**

```Solidity
// examples/src/smart-contracts/VeriAuctionTokenForEth_problems.sol

158         auctionToken.transfer(owner(), tokensToSend);
```

### unchecked-transfer

- Impact: `High`
- Confidence: `Medium`


**In Function**

```Solidity
// examples/src/smart-contracts/VeriAuctionTokenForEth_problems.sol

56     function depositAuctionTokens() external onlyOwner {
57         // The deployer of this auction contract should have approved the auction
58         // contract to transfer the auction token before deploying this contract.
59         auctionToken.transferFrom(msg.sender, address(this), amountToDistribute);
60         auctionStarted = true;
61     }
```

**Lines of relevance**

```Solidity
// examples/src/smart-contracts/VeriAuctionTokenForEth_problems.sol

59         auctionToken.transferFrom(msg.sender, address(this), amountToDistribute);
```
## Mythril



```json

{

  "issues": [],

  "meta": {

    "mythril_execution_info": {

      "analysis_duration": 19629487514

    }

  },

  "sourceFormat": "text",

  "sourceList": [

    "#utility.yul",

    "././examples/./src/smart-contracts/VeriAuctionTokenForEth_problems.sol",

    "examples/node_modules/@openzeppelin/contracts/access/Ownable.sol",

    "examples/node_modules/@openzeppelin/contracts/token/ERC20/IERC20.sol",

    "examples/node_modules/@openzeppelin/contracts/token/ERC20/extensions/IERC20Metadata.sol",

    "examples/node_modules/@openzeppelin/contracts/utils/Context.sol",

    "examples/src/smart-contracts//interfaces/IVeriAuctionTokenForEth.sol"

  ],

  "sourceType": "solidity-file"

}

```

