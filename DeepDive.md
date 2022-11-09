# Deep dive

- [Possible exploits in the smart contracts](#possible-exploits-in-the-smart-contracts)
- [Analysis techniques](#analysis-techniques)

# Possible exploits in the smart contracts

A nice source that explains several exploits and how to prevent them can be seen [here](https://medium.com/hackernoon/hackpedia-16-solidity-hacks-vulnerabilities-their-fixes-and-real-world-examples-f3210eba5148).

Some of these are:

- Re-entrancy
  - When sending ETH to a contract address, that address can create custom logic in its fallback function (`function () payable {}`). This logic can then execute anything it wants. It can call the contract that sent the ETH again and try to make it send more ETH.
- Rounding errors
  - A shared savings contract between known people where everyone can take out x% every n days. It can happen that the result results in fewer tokens received than expected due to rounding error. The impact of this depends on how much worth the token is that is withdrawn.
- Updating storage slots in caller context with `delegatecall()`
  - Overwriting an address
  - Overwriting a value used as the denominator with a huge value, resulting in the division being 0
- Partly prevent front-running using a check of gas price
  - Front-running is when someone scan the memory pool with incomming transactions (txs), sees a transaction (tx) and copies its calldata by with a higher gas price. This would lead to the miner being more likely to pick the tx with the higher gas price. While not necessarily a vulnerability of a the smart contract, it can be good to keep in mind that this can be partly prevented by checking for a maximum gas price.
- Sending ETH to a contract through selfdestruct of other contact
  - If there would be a pool contract with ETH and an ERC20 token we could make all swaps fail the assert checks for a non-decreasing K value if `this.balance` and an ETH balance counter would be used interchangeably.
  - An auction contract takes ETH and distributes an ERC20 token. Again if `this.balance` and an internal ETH balance counter are used interchangeably, someone can influence this price by sending eth if the price is denominated with `this.balance`.
- Forgetting an access guard on a function
  - Could lead to someone taking ownership of the contract
- Under/Overflow problems are not a problem anymore with newer Solidity versions.

More examples can be found [here](https://hacken.io/discover/smart-contract-vulnerabilities/).

There is also the Smart Contract Weakness Classification and Test Cases registry ([SWC registry](https://swcregistry.io/)) which lists level problems with examples.

# Analysis techniques

### Satisfiable Modulo Theory (SMT)

In short, SMT allows us to define a set of constraints and determine if it can be true or not (satisfiability). The SMT solver which is used in most formal verification tools for the EVM is [z3](https://github.com/Z3Prover/z3). Note that z3 is more than only a SMT solver (see the [manual](https://microsoft.github.io/z3guide/)).

SMT is used by almost all verification tools.

#### Example

As a very simple example using an online z3 runner: https://jfmc.github.io/z3-play. This page also describes much more complex features of z3.

Let say that we have integers `a` and `b` with the following:

- Assumption: `a > 15`
- Requirement: `a + b > 100`

The following check will say that is **satisfiable**.

```z3
(declare-const a Int)
(declare-const b Int)

(assert (> a 15))
(assert (> (+ a b) 100))

(check-sat)
(get-model)
```

Running this in the online tool results in the following output. Saying that if `a = 16` and `b = 85` that all requirements are met (which is true since `16 + 85 = 101`).

```
sat
(
  (define-fun b () Int
    85)
  (define-fun a () Int
    16)
)
```

However, now we only know that it is possible. We don't know if `a + b` can be less than 100. For that we will try to prove the negation of our requirement.

```z3
(declare-const a Int)
(declare-const b Int)

(assert (> a 15))
(assert (not (> (+ a b) 100)))

(check-sat)
(get-model)
```

Resulting in the following output. This says that the negation of our requirement can be satisfied. Meaning that the requirement is not met. A counter-example to our requirement is given as `a = 16` and `b = 84` resulting in `16 + 84 = 100`. The requirement is indeed violated.

```
sat
(
  (define-fun b () Int
    84)
  (define-fun a () Int
    16)
)
```

If we make the assumption that `a > 100` and `b > 0` however, the requirement is met as can be seen:

```z3
(declare-const a Int)
(declare-const b Int)

(assert (> a 100))
(assert (> b 0))
(assert (not (> (+ a b) 100)))

(check-sat)
(get-model)
```

Resulting in:

```
Error: unsat
(error "line 9 column 10: model is not available")
```

### Symbolic execution

Symbolic execution takes multiple paths in the code. But instead of using concrete values, symbolic values are used. So when an input variable (after some manipulation) would be used in a branch, the program would take both branches. When one of the branches would then throw as error, the tool would determine a concrete value which would cause the taking of this branch.

This [slideset](https://www-verimag.imag.fr/~mounier/Enseignement/Software_Security/ConcolicExecution.pdf#page=32) has an example of sumbolic execution.
The second speaker of [this talk](https://youtu.be/RunMhlTtdKw?t=2033) explain the basics of how it is done in hevm.
An overview of symbolic execution in general with an example can be found [here](https://www.youtube.com/watch?v=wOO5jpoFIss).

### Model checking

Model checking works on the state machine of a system.

An example of a symbolic model checker is [NuSMV](https://nusmv.fbk.eu/). In NuSMV a user will define all the possible conditional transitions. Usually this would be generated with a custom script when possible since a complete system can be quite large/complex. Then the user will define the specifications to check for using temporal logic. Whenever NuSMV find a trace (a sequence of transitions) that violates this specification it will print the trace.

The tool [SPACER](https://arieg.bitbucket.io/pdf/synasc2019.pdfß) enables model checking in z3 using horn clauses.

### Matching logic

http://www.matching-logic.org/
https://www.youtube.com/watch?v=Awsv0BlJgbo

Matching logic can define a multitude of other logics.

Matching logic lets someone define a language's semantics as rewrite rules.

In matching logic a 'state' in a program is represented as a configuration. A rewrite rule `lhs => rhs` means that when the `lhs` matches the current configuration, it will be rewritten to the `rhs`.

## Verifying source code vs bytecode

Here only tools uses in the repo are considered.

Works on Solidity code:

- SMTChecker

Working on bytecode:

- hevm
- kevm

The main benefit of working with bytecode is that you are working with the code which will actually be deployed. You are not dependent of potential error in the compiler.

# More sources

- [Ethereum Formal Verification Blog](https://fv.ethereum.org/)
- [Formal Systems Laboratory](https://fsl.cs.illinois.edu/)
- [A list of formal verification tools for ethereum](https://github.com/leonardoalt/ethereum_formal_verification_overview)
- [Smart contract vulnerabilities](https://hacken.io/discover/smart-contract-vulnerabilities/)
