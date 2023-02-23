# Smart contract formal verification

## Context

In order to see how the formal verification (FV) tools can work in real world scenarios, we need a real world scenario. It should be simple enough however to make it easy to debug and analyze manually.

## Setup

```bash
$ yarn install
```

```bash
$ curl -L https://foundry.paradigm.xyz | bash
$ source ~/.bashrc
$ foundryup
```

```bash
$ git submodule update --init --recursive
```

## Usage

### Normal smart-contract development

```bash
$ yarn run sc:test
```

### Report generation with security-scans

Installing Rust.

```bash
$ curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
$ source ~/.bashrc
```

Copy the configuration file.

```bash
$ cp ./security-scans/analysis-config-example.toml ./analysis-config.toml
```

Update `./analysis-config.toml` as seen fit. The run the report generator.

```bash
$ yarn --cwd ../ run   \
    scan:generate-report            \
    ${PWD}/analysis-config.toml
```

kevm

```bash
$ yarn --cwd ../ run   \
    scan:kevm                       \
    ${PWD}                          \
    ../                \
    ./src/smart-contracts           \
    ./kevm-specs                    \
    VeriToken
```

# Creating contracts with problems

## [VeriAuctionTokenForEth_problems.sol](./smart-contracts/src/VeriAuctionTokenForEth_problems.sol)

Some attacks are demonstrated in [VeriAuctionTokenForEth_problems_reentrancy.t.sol](./smart-contracts/test/VeriAuctionTokenForEth_problems_reentrancy.t.sol) which uses [VeriAuctionTokenForEth_reentrancy_attacker.sol](./smart-contracts/test/Attackers/VeriAuctionTokenForEth_reentrancy_attacker.sol) as the attacking contract. The comments in [VeriAuctionTokenForEth_problems.sol](./smart-contracts/src/VeriAuctionTokenForEth_problems.sol) also give some description about the possible exploits.

Currently two attacks are tested to work using the [unit tests](./smart-contracts/test/VeriAuctionTokenForEth_problems_reentrancy.t.sol).

### Getting a large amount of ETH out of the contract

The auction contract allows for users to resign from the auction. This could be a legitimate feature in a auction for certain use cases. However, since ETH is used as the commitment token, this ETH also has to be sent back to the user. The [attacker](./smart-contracts/test/Attackers/VeriAuctionTokenForEth_reentrancy_attacker.sol) can then implement it's fallback function such that the `resignFromAuction()` function is called multiple times. Each time making the auction send the amount of committed ETH back to the attacker.

This is possible due to these lines in [VeriAuctionTokenForEth_problems.sol](./smart-contracts/src/VeriAuctionTokenForEth_problems.sol):

```Solidity
// VeriAuctionTokenForEth_problems.sol

function resignFromAuction() external override {

    ...

    // In these three lines the re-entrancy attack happens.
    (bool transferSuccess, ) = msg.sender.call{value: commitment}("");
    require(transferSuccess, "VeriAuctionTokenForEth (resignFromAuction): failed to send ETH");

    delete commited[msg.sender];
}
```

The attacker's code would like like as shown below. Still this attack might fail when there is not enough ETH in the auction contract left. So the attacker could also check first if there is still enough balance to steal.

```Solidity
// VeriAuctionTokenForEth_reentrancy_attacker.sol

fallback () external payable {
    if(timesToAttack > 0) {
        timesToAttack--;
        (bool success, ) = msg.sender.call(abi.encodeWithSelector(IVeriAuctionTokenForEth.resignFromAuction.selector));
        require(success, "Failed to claim ETH");
    }
}
```

An easy fix is the following:

```Solidity
// VeriAuctionTokenForEth_problems.sol

function resignFromAuction() external override {

    ...

    // Prevent re-entrancy attack by setting the commitment to 0 before transferring the ETH.
    delete commited[msg.sender];

    (bool transferSuccess, ) = msg.sender.call{value: commitment}("");
    require(transferSuccess, "VeriAuctionTokenForEth (resignFromAuction): failed to send ETH");
}
```

### Getting both the commitment and the claimable tokens

This attack is similar to the previous attack. The difference however is that now the attacker can only get it's own commited ETH back plus the tokens which would be claimable would the attacker have called `claimTokens()`.

First the attacker has to call the `resignFromAuction()` function as in the previous attack. The attacker now does something different in the fallback function. It simply calls `claimTokens()` as shown below.

```Solidity
// VeriAuctionTokenForEth_reentrancy_attacker.sol

fallback () external payable {
    (bool success, ) = msg.sender.call(abi.encodeWithSelector(IVeriAuctionTokenForEth.claimTokens.selector));
    require(success, "Failed to claim tokens");
}
```

The developer of `claimTokens()` new that it is good to update the local state before calling external functions and thus deleted the commited amount before sending the tokens. However, this didn't prevent the attacker from having already received the commited ETH.

```Solidity
// VeriAuctionTokenForEth_problems.sol

function claimTokens() external override {

    ...

    delete commited[msg.sender];
    auctionToken.transfer(msg.sender, claimableAmount);
}
```

Preventing this attack is exactly the same as for the previous attack.
