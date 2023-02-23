# Code report

## Slither



Compiled with solc

Number of lines: 26 (+ 0 in dependencies, + 0 in tests)

Number of assembly lines: 0

Number of contracts: 1 (+ 0 in dependencies, + 0 tests) 



Number of optimization issues: 1

Number of informational issues: 4

Number of low issues: 1

Number of medium issues: 0

Number of high issues: 1



For more information about the detected items see the [Slither documentation](https://github.com/crytic/slither/wiki/Detector-Documentation).


### constable-states

- Impact: `Optimization`
- Confidence: `High`


```Solidity
// examples/src/smart-contracts/EtherStore.sol

6     uint256 public withdrawalLimit = 1 ether;
```

### solc-version

- Impact: `Informational`
- Confidence: `High`


```Solidity
// examples/src/smart-contracts/EtherStore.sol

2 pragma solidity ^0.8.13;
```

### solc-version

- Impact: `Informational`
- Confidence: `High`


### low-level-calls

- Impact: `Informational`
- Confidence: `High`


**In Function**

```Solidity
// examples/src/smart-contracts/EtherStore.sol

14     function withdrawFunds(uint256 _weiToWithdraw) public {
15         require(balances[msg.sender] >= _weiToWithdraw);
16         // limit the withdrawal
17         require(_weiToWithdraw <= withdrawalLimit);
18         // limit the time allowed to withdraw
19         require(block.timestamp >= lastWithdrawTime[msg.sender] + 1 weeks);
20 
21         (bool success, ) = msg.sender.call{value: _weiToWithdraw}("");
22         require(success);
23         balances[msg.sender] -= _weiToWithdraw;
24         lastWithdrawTime[msg.sender] = block.timestamp;
25     }
```

**Lines of relevance**

```Solidity
// examples/src/smart-contracts/EtherStore.sol

21         (bool success, ) = msg.sender.call{value: _weiToWithdraw}("");
```

### naming-convention

- Impact: `Informational`
- Confidence: `High`


```Solidity
// examples/src/smart-contracts/EtherStore.sol

14     function withdrawFunds(uint256 _weiToWithdraw) public {
```

### timestamp

- Impact: `Low`
- Confidence: `Medium`


**In Function**

```Solidity
// examples/src/smart-contracts/EtherStore.sol

14     function withdrawFunds(uint256 _weiToWithdraw) public {
15         require(balances[msg.sender] >= _weiToWithdraw);
16         // limit the withdrawal
17         require(_weiToWithdraw <= withdrawalLimit);
18         // limit the time allowed to withdraw
19         require(block.timestamp >= lastWithdrawTime[msg.sender] + 1 weeks);
20 
21         (bool success, ) = msg.sender.call{value: _weiToWithdraw}("");
22         require(success);
23         balances[msg.sender] -= _weiToWithdraw;
24         lastWithdrawTime[msg.sender] = block.timestamp;
25     }
```

**Lines of relevance**

```Solidity
// examples/src/smart-contracts/EtherStore.sol

19         require(block.timestamp >= lastWithdrawTime[msg.sender] + 1 weeks);
```

### reentrancy-eth

- Impact: `High`
- Confidence: `Medium`


**In Function**

```Solidity
// examples/src/smart-contracts/EtherStore.sol

14     function withdrawFunds(uint256 _weiToWithdraw) public {
15         require(balances[msg.sender] >= _weiToWithdraw);
16         // limit the withdrawal
17         require(_weiToWithdraw <= withdrawalLimit);
18         // limit the time allowed to withdraw
19         require(block.timestamp >= lastWithdrawTime[msg.sender] + 1 weeks);
20 
21         (bool success, ) = msg.sender.call{value: _weiToWithdraw}("");
22         require(success);
23         balances[msg.sender] -= _weiToWithdraw;
24         lastWithdrawTime[msg.sender] = block.timestamp;
25     }
```

**Lines of relevance**

```Solidity
// examples/src/smart-contracts/EtherStore.sol

21         (bool success, ) = msg.sender.call{value: _weiToWithdraw}("");
```

**Lines of relevance**

```Solidity
// examples/src/smart-contracts/EtherStore.sol

23         balances[msg.sender] -= _weiToWithdraw;
```

**Lines of relevance**

```Solidity
// examples/src/smart-contracts/EtherStore.sol

24         lastWithdrawTime[msg.sender] = block.timestamp;
```
