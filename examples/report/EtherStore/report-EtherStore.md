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
## Mythril



```json

{

  "issues": [

    {

      "description": {

        "head": "A control flow decision is made based on The block.timestamp environment variable.",

        "tail": "The block.timestamp environment variable is used to determine a control flow decision. Note that the values of variables like coinbase, gaslimit, block number and timestamp are predictable and can be manipulated by a malicious miner. Also keep in mind that attackers know hashes of earlier blocks. Don't use any of those environment variables as sources of randomness and be aware that use of these variables introduces a certain level of trust into miners."

      },

      "extra": {

        "discoveryTime": 2778852224,

        "testCases": [

          {

            "initialState": {

              "accounts": {

                "0x0": {

                  "balance": "0x0",

                  "code": "60806040526004361061004a5760003560e01c80631031ec311461004f578063155dd5ee1461008c57806327e235e3146100b55780637ddfe78d146100f2578063e2c41dbc1461011d575b600080fd5b34801561005b57600080fd5b50610076600480360381019061007191906103e1565b610127565b6040516100839190610427565b60405180910390f35b34801561009857600080fd5b506100b360048036038101906100ae919061046e565b61013f565b005b3480156100c157600080fd5b506100dc60048036038101906100d791906103e1565b610308565b6040516100e99190610427565b60405180910390f35b3480156100fe57600080fd5b50610107610320565b6040516101149190610427565b60405180910390f35b610125610326565b005b60016020528060005260406000206000915090505481565b80600260003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002054101561018b57600080fd5b60005481111561019a57600080fd5b62093a80600160003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020546101e891906104ca565b4210156101f457600080fd5b60003373ffffffffffffffffffffffffffffffffffffffff168260405161021a9061052f565b60006040518083038185875af1925050503d8060008114610257576040519150601f19603f3d011682016040523d82523d6000602084013e61025c565b606091505b505090508061026a57600080fd5b81600260003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060008282546102b99190610544565b9250508190555042600160003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020819055505050565b60026020528060005260406000206000915090505481565b60005481565b34600260003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600082825461037591906104ca565b92505081905550565b600080fd5b600073ffffffffffffffffffffffffffffffffffffffff82169050919050565b60006103ae82610383565b9050919050565b6103be816103a3565b81146103c957600080fd5b50565b6000813590506103db816103b5565b92915050565b6000602082840312156103f7576103f661037e565b5b6000610405848285016103cc565b91505092915050565b6000819050919050565b6104218161040e565b82525050565b600060208201905061043c6000830184610418565b92915050565b61044b8161040e565b811461045657600080fd5b50565b60008135905061046881610442565b92915050565b6000602082840312156104845761048361037e565b5b600061049284828501610459565b91505092915050565b7f4e487b7100000000000000000000000000000000000000000000000000000000600052601160045260246000fd5b60006104d58261040e565b91506104e08361040e565b92508282019050808211156104f8576104f761049b565b5b92915050565b600081905092915050565b50565b60006105196000836104fe565b915061052482610509565b600082019050919050565b600061053a8261050c565b9150819050919050565b600061054f8261040e565b915061055a8361040e565b92508282039050818111156105725761057161049b565b5b9291505056fea264697066735822122022cf86d3bbeb3a33922c0f2d2e1328331a8b75f3e84893fe32f4f12aa65808ca64736f6c63430008110033",

                  "nonce": 0,

                  "storage": "{}"

                },

                "0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef": {

                  "balance": "0x0",

                  "code": "",

                  "nonce": 0,

                  "storage": "{}"

                }

              }

            },

            "steps": [

              {

                "address": "0x0",

                "blockCoinbase": "0xcbcbcbcbcbcbcbcbcbcbcbcbcbcbcbcbcbcbcbcb",

                "blockDifficulty": "0xa7d7343662e26",

                "blockGasLimit": "0x7d0000",

                "blockNumber": "0x66e393",

                "blockTime": "0x5bfa4639",

                "calldata": "0x155dd5ee0000000000000000000000000000000000000000000000000000002000000000",

                "gasLimit": "0x7d000",

                "gasPrice": "0x773594000",

                "input": "0x155dd5ee0000000000000000000000000000000000000000000000000000002000000000",

                "name": "withdrawFunds(uint256)",

                "origin": "0xaffeaffeaffeaffeaffeaffeaffeaffeaffeaffe",

                "resolved_input": [

                  137438953472

                ],

                "value": "0x0"

              }

            ]

          }

        ]

      },

      "locations": [

        {

          "sourceMap": "495:1:0"

        }

      ],

      "severity": "Low",

      "swcID": "SWC-116",

      "swcTitle": "Timestamp Dependence"

    },

    {

      "description": {

        "head": "Any sender can withdraw Ether from the contract account.",

        "tail": "Arbitrary senders other than the contract creator can profitably extract Ether from the contract account. Verify the business logic carefully and make sure that appropriate security controls are in place to prevent unexpected loss of funds."

      },

      "extra": {

        "discoveryTime": 8471895933,

        "testCases": [

          {

            "initialState": {

              "accounts": {

                "0x0": {

                  "balance": "0x1000a821604148013",

                  "code": "60806040526004361061004a5760003560e01c80631031ec311461004f578063155dd5ee1461008c57806327e235e3146100b55780637ddfe78d146100f2578063e2c41dbc1461011d575b600080fd5b34801561005b57600080fd5b50610076600480360381019061007191906103e1565b610127565b6040516100839190610427565b60405180910390f35b34801561009857600080fd5b506100b360048036038101906100ae919061046e565b61013f565b005b3480156100c157600080fd5b506100dc60048036038101906100d791906103e1565b610308565b6040516100e99190610427565b60405180910390f35b3480156100fe57600080fd5b50610107610320565b6040516101149190610427565b60405180910390f35b610125610326565b005b60016020528060005260406000206000915090505481565b80600260003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002054101561018b57600080fd5b60005481111561019a57600080fd5b62093a80600160003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020546101e891906104ca565b4210156101f457600080fd5b60003373ffffffffffffffffffffffffffffffffffffffff168260405161021a9061052f565b60006040518083038185875af1925050503d8060008114610257576040519150601f19603f3d011682016040523d82523d6000602084013e61025c565b606091505b505090508061026a57600080fd5b81600260003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060008282546102b99190610544565b9250508190555042600160003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020819055505050565b60026020528060005260406000206000915090505481565b60005481565b34600260003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600082825461037591906104ca565b92505081905550565b600080fd5b600073ffffffffffffffffffffffffffffffffffffffff82169050919050565b60006103ae82610383565b9050919050565b6103be816103a3565b81146103c957600080fd5b50565b6000813590506103db816103b5565b92915050565b6000602082840312156103f7576103f661037e565b5b6000610405848285016103cc565b91505092915050565b6000819050919050565b6104218161040e565b82525050565b600060208201905061043c6000830184610418565b92915050565b61044b8161040e565b811461045657600080fd5b50565b60008135905061046881610442565b92915050565b6000602082840312156104845761048361037e565b5b600061049284828501610459565b91505092915050565b7f4e487b7100000000000000000000000000000000000000000000000000000000600052601160045260246000fd5b60006104d58261040e565b91506104e08361040e565b92508282019050808211156104f8576104f761049b565b5b92915050565b600081905092915050565b50565b60006105196000836104fe565b915061052482610509565b600082019050919050565b600061053a8261050c565b9150819050919050565b600061054f8261040e565b915061055a8361040e565b92508282039050818111156105725761057161049b565b5b9291505056fea264697066735822122022cf86d3bbeb3a33922c0f2d2e1328331a8b75f3e84893fe32f4f12aa65808ca64736f6c63430008110033",

                  "nonce": 0,

                  "storage": "{}"

                },

                "0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef": {

                  "balance": "0x10800004080002",

                  "code": "",

                  "nonce": 0,

                  "storage": "{}"

                }

              }

            },

            "steps": [

              {

                "address": "0x0",

                "blockCoinbase": "0xcbcbcbcbcbcbcbcbcbcbcbcbcbcbcbcbcbcbcbcb",

                "blockDifficulty": "0xa7d7343662e26",

                "blockGasLimit": "0x7d0000",

                "blockNumber": "0x66e393",

                "blockTime": "0x5bfa4639",

                "calldata": "0x155dd5ee0000000000000000000000000000000000000000000000008002020a040c8011",

                "gasLimit": "0x7d000",

                "gasPrice": "0x773594000",

                "input": "0x155dd5ee0000000000000000000000000000000000000000000000008002020a040c8011",

                "name": "withdrawFunds(uint256)",

                "origin": "0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef",

                "resolved_input": [

                  9223937228849053713

                ],

                "value": "0x0"

              }

            ]

          }

        ]

      },

      "locations": [

        {

          "sourceMap": "551:1:0"

        }

      ],

      "severity": "High",

      "swcID": "SWC-105",

      "swcTitle": "Unprotected Ether Withdrawal"

    },

    {

      "description": {

        "head": "A call to a user-supplied address is executed.",

        "tail": "An external message call to an address specified by the caller is executed. Note that the callee account might contain arbitrary code and could re-enter any function within this contract. Reentering the contract in an intermediate state may lead to unexpected behaviour. Make sure that no state modifications are executed after this call and/or reentrancy guards are in place."

      },

      "extra": {

        "discoveryTime": 8178097009,

        "testCases": [

          {

            "initialState": {

              "accounts": {

                "0x0": {

                  "balance": "0x3fffffe880045e381",

                  "code": "60806040526004361061004a5760003560e01c80631031ec311461004f578063155dd5ee1461008c57806327e235e3146100b55780637ddfe78d146100f2578063e2c41dbc1461011d575b600080fd5b34801561005b57600080fd5b50610076600480360381019061007191906103e1565b610127565b6040516100839190610427565b60405180910390f35b34801561009857600080fd5b506100b360048036038101906100ae919061046e565b61013f565b005b3480156100c157600080fd5b506100dc60048036038101906100d791906103e1565b610308565b6040516100e99190610427565b60405180910390f35b3480156100fe57600080fd5b50610107610320565b6040516101149190610427565b60405180910390f35b610125610326565b005b60016020528060005260406000206000915090505481565b80600260003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002054101561018b57600080fd5b60005481111561019a57600080fd5b62093a80600160003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020546101e891906104ca565b4210156101f457600080fd5b60003373ffffffffffffffffffffffffffffffffffffffff168260405161021a9061052f565b60006040518083038185875af1925050503d8060008114610257576040519150601f19603f3d011682016040523d82523d6000602084013e61025c565b606091505b505090508061026a57600080fd5b81600260003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060008282546102b99190610544565b9250508190555042600160003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020819055505050565b60026020528060005260406000206000915090505481565b60005481565b34600260003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600082825461037591906104ca565b92505081905550565b600080fd5b600073ffffffffffffffffffffffffffffffffffffffff82169050919050565b60006103ae82610383565b9050919050565b6103be816103a3565b81146103c957600080fd5b50565b6000813590506103db816103b5565b92915050565b6000602082840312156103f7576103f661037e565b5b6000610405848285016103cc565b91505092915050565b6000819050919050565b6104218161040e565b82525050565b600060208201905061043c6000830184610418565b92915050565b61044b8161040e565b811461045657600080fd5b50565b60008135905061046881610442565b92915050565b6000602082840312156104845761048361037e565b5b600061049284828501610459565b91505092915050565b7f4e487b7100000000000000000000000000000000000000000000000000000000600052601160045260246000fd5b60006104d58261040e565b91506104e08361040e565b92508282019050808211156104f8576104f761049b565b5b92915050565b600081905092915050565b50565b60006105196000836104fe565b915061052482610509565b600082019050919050565b600061053a8261050c565b9150819050919050565b600061054f8261040e565b915061055a8361040e565b92508282039050818111156105725761057161049b565b5b9291505056fea264697066735822122022cf86d3bbeb3a33922c0f2d2e1328331a8b75f3e84893fe32f4f12aa65808ca64736f6c63430008110033",

                  "nonce": 0,

                  "storage": "{}"

                },

                "0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef": {

                  "balance": "0x100002",

                  "code": "",

                  "nonce": 0,

                  "storage": "{}"

                }

              }

            },

            "steps": [

              {

                "address": "0x0",

                "blockCoinbase": "0xcbcbcbcbcbcbcbcbcbcbcbcbcbcbcbcbcbcbcbcb",

                "blockDifficulty": "0xa7d7343662e26",

                "blockGasLimit": "0x7d0000",

                "blockNumber": "0x66e393",

                "blockTime": "0x5bfa4639",

                "calldata": "0x155dd5ee000000000000000000000000000000000000000000000003fffff86000197780",

                "gasLimit": "0x7d000",

                "gasPrice": "0x773594000",

                "input": "0x155dd5ee000000000000000000000000000000000000000000000003fffff86000197780",

                "name": "withdrawFunds(uint256)",

                "origin": "0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef",

                "resolved_input": [

                  7.3786967911063716e19

                ],

                "value": "0x0"

              }

            ]

          }

        ]

      },

      "locations": [

        {

          "sourceMap": "551:1:0"

        }

      ],

      "severity": "Low",

      "swcID": "SWC-107",

      "swcTitle": "Reentrancy"

    },

    {

      "description": {

        "head": "Read of persistent state following external call",

        "tail": "The contract account state is accessed after an external call to a user defined address. To prevent reentrancy issues, consider accessing the state only before the call, especially if the callee is untrusted. Alternatively, a reentrancy lock can be used to prevent untrusted callees from re-entering the contract in an intermediate state."

      },

      "extra": {

        "discoveryTime": 8646210432,

        "testCases": [

          {

            "initialState": {

              "accounts": {

                "0x0": {

                  "balance": "0x5000000000000001",

                  "code": "60806040526004361061004a5760003560e01c80631031ec311461004f578063155dd5ee1461008c57806327e235e3146100b55780637ddfe78d146100f2578063e2c41dbc1461011d575b600080fd5b34801561005b57600080fd5b50610076600480360381019061007191906103e1565b610127565b6040516100839190610427565b60405180910390f35b34801561009857600080fd5b506100b360048036038101906100ae919061046e565b61013f565b005b3480156100c157600080fd5b506100dc60048036038101906100d791906103e1565b610308565b6040516100e99190610427565b60405180910390f35b3480156100fe57600080fd5b50610107610320565b6040516101149190610427565b60405180910390f35b610125610326565b005b60016020528060005260406000206000915090505481565b80600260003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002054101561018b57600080fd5b60005481111561019a57600080fd5b62093a80600160003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020546101e891906104ca565b4210156101f457600080fd5b60003373ffffffffffffffffffffffffffffffffffffffff168260405161021a9061052f565b60006040518083038185875af1925050503d8060008114610257576040519150601f19603f3d011682016040523d82523d6000602084013e61025c565b606091505b505090508061026a57600080fd5b81600260003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060008282546102b99190610544565b9250508190555042600160003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020819055505050565b60026020528060005260406000206000915090505481565b60005481565b34600260003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600082825461037591906104ca565b92505081905550565b600080fd5b600073ffffffffffffffffffffffffffffffffffffffff82169050919050565b60006103ae82610383565b9050919050565b6103be816103a3565b81146103c957600080fd5b50565b6000813590506103db816103b5565b92915050565b6000602082840312156103f7576103f661037e565b5b6000610405848285016103cc565b91505092915050565b6000819050919050565b6104218161040e565b82525050565b600060208201905061043c6000830184610418565b92915050565b61044b8161040e565b811461045657600080fd5b50565b60008135905061046881610442565b92915050565b6000602082840312156104845761048361037e565b5b600061049284828501610459565b91505092915050565b7f4e487b7100000000000000000000000000000000000000000000000000000000600052601160045260246000fd5b60006104d58261040e565b91506104e08361040e565b92508282019050808211156104f8576104f761049b565b5b92915050565b600081905092915050565b50565b60006105196000836104fe565b915061052482610509565b600082019050919050565b600061053a8261050c565b9150819050919050565b600061054f8261040e565b915061055a8361040e565b92508282039050818111156105725761057161049b565b5b9291505056fea264697066735822122022cf86d3bbeb3a33922c0f2d2e1328331a8b75f3e84893fe32f4f12aa65808ca64736f6c63430008110033",

                  "nonce": 0,

                  "storage": "{}"

                },

                "0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef": {

                  "balance": "0x10000000000",

                  "code": "",

                  "nonce": 0,

                  "storage": "{}"

                }

              }

            },

            "steps": [

              {

                "address": "0x0",

                "blockCoinbase": "0xcbcbcbcbcbcbcbcbcbcbcbcbcbcbcbcbcbcbcbcb",

                "blockDifficulty": "0xa7d7343662e26",

                "blockGasLimit": "0x7d0000",

                "blockNumber": "0x66e393",

                "blockTime": "0x5bfa4639",

                "calldata": "0x155dd5ee0000000000000000000000000000000000000000000000000000000000000000",

                "gasLimit": "0x7d000",

                "gasPrice": "0x773594000",

                "input": "0x155dd5ee0000000000000000000000000000000000000000000000000000000000000000",

                "name": "withdrawFunds(uint256)",

                "origin": "0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef",

                "resolved_input": [

                  0

                ],

                "value": "0x0"

              }

            ]

          }

        ]

      },

      "locations": [

        {

          "sourceMap": "687:1:0"

        }

      ],

      "severity": "Medium",

      "swcID": "SWC-107",

      "swcTitle": "Reentrancy"

    },

    {

      "description": {

        "head": "Write to persistent state following external call",

        "tail": "The contract account state is accessed after an external call to a user defined address. To prevent reentrancy issues, consider accessing the state only before the call, especially if the callee is untrusted. Alternatively, a reentrancy lock can be used to prevent untrusted callees from re-entering the contract in an intermediate state."

      },

      "extra": {

        "discoveryTime": 8693127155,

        "testCases": [

          {

            "initialState": {

              "accounts": {

                "0x0": {

                  "balance": "0x5000000000000001",

                  "code": "60806040526004361061004a5760003560e01c80631031ec311461004f578063155dd5ee1461008c57806327e235e3146100b55780637ddfe78d146100f2578063e2c41dbc1461011d575b600080fd5b34801561005b57600080fd5b50610076600480360381019061007191906103e1565b610127565b6040516100839190610427565b60405180910390f35b34801561009857600080fd5b506100b360048036038101906100ae919061046e565b61013f565b005b3480156100c157600080fd5b506100dc60048036038101906100d791906103e1565b610308565b6040516100e99190610427565b60405180910390f35b3480156100fe57600080fd5b50610107610320565b6040516101149190610427565b60405180910390f35b610125610326565b005b60016020528060005260406000206000915090505481565b80600260003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002054101561018b57600080fd5b60005481111561019a57600080fd5b62093a80600160003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020546101e891906104ca565b4210156101f457600080fd5b60003373ffffffffffffffffffffffffffffffffffffffff168260405161021a9061052f565b60006040518083038185875af1925050503d8060008114610257576040519150601f19603f3d011682016040523d82523d6000602084013e61025c565b606091505b505090508061026a57600080fd5b81600260003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060008282546102b99190610544565b9250508190555042600160003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020819055505050565b60026020528060005260406000206000915090505481565b60005481565b34600260003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600082825461037591906104ca565b92505081905550565b600080fd5b600073ffffffffffffffffffffffffffffffffffffffff82169050919050565b60006103ae82610383565b9050919050565b6103be816103a3565b81146103c957600080fd5b50565b6000813590506103db816103b5565b92915050565b6000602082840312156103f7576103f661037e565b5b6000610405848285016103cc565b91505092915050565b6000819050919050565b6104218161040e565b82525050565b600060208201905061043c6000830184610418565b92915050565b61044b8161040e565b811461045657600080fd5b50565b60008135905061046881610442565b92915050565b6000602082840312156104845761048361037e565b5b600061049284828501610459565b91505092915050565b7f4e487b7100000000000000000000000000000000000000000000000000000000600052601160045260246000fd5b60006104d58261040e565b91506104e08361040e565b92508282019050808211156104f8576104f761049b565b5b92915050565b600081905092915050565b50565b60006105196000836104fe565b915061052482610509565b600082019050919050565b600061053a8261050c565b9150819050919050565b600061054f8261040e565b915061055a8361040e565b92508282039050818111156105725761057161049b565b5b9291505056fea264697066735822122022cf86d3bbeb3a33922c0f2d2e1328331a8b75f3e84893fe32f4f12aa65808ca64736f6c63430008110033",

                  "nonce": 0,

                  "storage": "{}"

                },

                "0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef": {

                  "balance": "0x10000000000",

                  "code": "",

                  "nonce": 0,

                  "storage": "{}"

                }

              }

            },

            "steps": [

              {

                "address": "0x0",

                "blockCoinbase": "0xcbcbcbcbcbcbcbcbcbcbcbcbcbcbcbcbcbcbcbcb",

                "blockDifficulty": "0xa7d7343662e26",

                "blockGasLimit": "0x7d0000",

                "blockNumber": "0x66e393",

                "blockTime": "0x5bfa4639",

                "calldata": "0x155dd5ee0000000000000000000000000000000000000000000000000000000000000000",

                "gasLimit": "0x7d000",

                "gasPrice": "0x773594000",

                "input": "0x155dd5ee0000000000000000000000000000000000000000000000000000000000000000",

                "name": "withdrawFunds(uint256)",

                "origin": "0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef",

                "resolved_input": [

                  0

                ],

                "value": "0x0"

              }

            ]

          }

        ]

      },

      "locations": [

        {

          "sourceMap": "703:1:0"

        }

      ],

      "severity": "Medium",

      "swcID": "SWC-107",

      "swcTitle": "Reentrancy"

    },

    {

      "description": {

        "head": "Write to persistent state following external call",

        "tail": "The contract account state is accessed after an external call to a user defined address. To prevent reentrancy issues, consider accessing the state only before the call, especially if the callee is untrusted. Alternatively, a reentrancy lock can be used to prevent untrusted callees from re-entering the contract in an intermediate state."

      },

      "extra": {

        "discoveryTime": 8715837240,

        "testCases": [

          {

            "initialState": {

              "accounts": {

                "0x0": {

                  "balance": "0x5000000000000001",

                  "code": "60806040526004361061004a5760003560e01c80631031ec311461004f578063155dd5ee1461008c57806327e235e3146100b55780637ddfe78d146100f2578063e2c41dbc1461011d575b600080fd5b34801561005b57600080fd5b50610076600480360381019061007191906103e1565b610127565b6040516100839190610427565b60405180910390f35b34801561009857600080fd5b506100b360048036038101906100ae919061046e565b61013f565b005b3480156100c157600080fd5b506100dc60048036038101906100d791906103e1565b610308565b6040516100e99190610427565b60405180910390f35b3480156100fe57600080fd5b50610107610320565b6040516101149190610427565b60405180910390f35b610125610326565b005b60016020528060005260406000206000915090505481565b80600260003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002054101561018b57600080fd5b60005481111561019a57600080fd5b62093a80600160003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020546101e891906104ca565b4210156101f457600080fd5b60003373ffffffffffffffffffffffffffffffffffffffff168260405161021a9061052f565b60006040518083038185875af1925050503d8060008114610257576040519150601f19603f3d011682016040523d82523d6000602084013e61025c565b606091505b505090508061026a57600080fd5b81600260003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060008282546102b99190610544565b9250508190555042600160003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020819055505050565b60026020528060005260406000206000915090505481565b60005481565b34600260003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600082825461037591906104ca565b92505081905550565b600080fd5b600073ffffffffffffffffffffffffffffffffffffffff82169050919050565b60006103ae82610383565b9050919050565b6103be816103a3565b81146103c957600080fd5b50565b6000813590506103db816103b5565b92915050565b6000602082840312156103f7576103f661037e565b5b6000610405848285016103cc565b91505092915050565b6000819050919050565b6104218161040e565b82525050565b600060208201905061043c6000830184610418565b92915050565b61044b8161040e565b811461045657600080fd5b50565b60008135905061046881610442565b92915050565b6000602082840312156104845761048361037e565b5b600061049284828501610459565b91505092915050565b7f4e487b7100000000000000000000000000000000000000000000000000000000600052601160045260246000fd5b60006104d58261040e565b91506104e08361040e565b92508282019050808211156104f8576104f761049b565b5b92915050565b600081905092915050565b50565b60006105196000836104fe565b915061052482610509565b600082019050919050565b600061053a8261050c565b9150819050919050565b600061054f8261040e565b915061055a8361040e565b92508282039050818111156105725761057161049b565b5b9291505056fea264697066735822122022cf86d3bbeb3a33922c0f2d2e1328331a8b75f3e84893fe32f4f12aa65808ca64736f6c63430008110033",

                  "nonce": 0,

                  "storage": "{}"

                },

                "0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef": {

                  "balance": "0x10000000000",

                  "code": "",

                  "nonce": 0,

                  "storage": "{}"

                }

              }

            },

            "steps": [

              {

                "address": "0x0",

                "blockCoinbase": "0xcbcbcbcbcbcbcbcbcbcbcbcbcbcbcbcbcbcbcbcb",

                "blockDifficulty": "0xa7d7343662e26",

                "blockGasLimit": "0x7d0000",

                "blockNumber": "0x66e393",

                "blockTime": "0x5bfa4639",

                "calldata": "0x155dd5ee0000000000000000000000000000000000000000000000000000000000000000",

                "gasLimit": "0x7d000",

                "gasPrice": "0x773594000",

                "input": "0x155dd5ee0000000000000000000000000000000000000000000000000000000000000000",

                "name": "withdrawFunds(uint256)",

                "origin": "0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef",

                "resolved_input": [

                  0

                ],

                "value": "0x0"

              }

            ]

          }

        ]

      },

      "locations": [

        {

          "sourceMap": "771:1:0"

        }

      ],

      "severity": "Medium",

      "swcID": "SWC-107",

      "swcTitle": "Reentrancy"

    }

  ],

  "meta": {

    "mythril_execution_info": {

      "analysis_duration": 8751570225

    }

  },

  "sourceFormat": "evm-byzantium-bytecode",

  "sourceList": [

    "0x41e281d97b6dfcafbee35b37cd9a24b430095e7e93c24e1e344480ad7b12edef"

  ],

  "sourceType": "raw-bytecode"

}

```

