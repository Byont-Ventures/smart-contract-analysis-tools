- [Analysis techniques](#analysis-techniques)
    - [Example: Satisfiable Modulo Theory (SMT)](#example-satisfiable-modulo-theory-smt)
      - [Checking if the requirement can hold](#checking-if-the-requirement-can-hold)
      - [Checking if the requirement will always hold](#checking-if-the-requirement-will-always-hold)
    - [Example: Symbolic execution](#example-symbolic-execution)
      - [Example](#example)
    - [Constraint Horn Clauses (CHC)](#constraint-horn-clauses-chc)
    - [Matching logic](#matching-logic)
  - [Verifying source code vs bytecode](#verifying-source-code-vs-bytecode)
- [More sources](#more-sources)

# Analysis techniques

Analyzing software can be done using several techniques. What you will notice, however, when learning more about all these techniques is that there is not always a clear division between them.

A lot of times multiple techniques are extensions of other techniques. In particular, [Satisfiable Modulo Theory (SMT)](#satisfiable-modulo-theory-smt) is one of the more fundamental techniques used. The main purpose of SMT is to check if the variables in a program can have a certain initial value such that a requirement is met. In other words, if there is a **satisfiable** assignment for the variables.

[Symbolic execution](#symbolic-execution) is a technique that checks all branches of a program to see if there are failing branches. If it finds a failing branch it will check if that branch can be reached using SMT. But SMT is also used during other stages in symbolic execution to avoid wasting processing time on branches that can't be reached anyway.

Another technique is to use [Constraint Horn Clauses (CHC)](#constraint-horn-clauses-chc). This will transfer the source code into logic and checks if certain failing paths can be found. CHC is a layer on top of SMT and is similar to symbolic execution.

What this introduction tries to make clear is that, (1) SMT is the backbone in software analysis, and (2) one technique doesn't exclude the other.

### Example: Satisfiable Modulo Theory (SMT)

To get a better idea of what an SMT checker does, we will go over a simple example. We will use [z3](https://github.com/Z3Prover/z3) as this is the most used SMT checker for automatic analysis tools for Solidity.

An online z3 runner can be used if you want to try the examples yourself: https://microsoft.github.io/z3guide/playground/Freeform%20Editing

Let's say that we have integers `a` and `b` with the following:

- Assumption: `a > 15`
- Requirement: `a + b > 100`

In Solidity this could look like this:

```Solidity
function specialAdd(int256 a, int256 b) returns (int256 c) {
    require(a > 15);

    c = a + b;

    assert(c > 100);
}
```

#### Checking if the requirement can hold

We can first check if the requirement (`a + b > 100`) can hold at al. This can be done with the following checks in z3. The syntax used is [SMTLib](https://microsoft.github.io/z3guide/docs/logic/basiccommands).

It is important to note that here we only check that there is **at least one** assignment for `a` and `b` that makes sure that `a + b > 100`.

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

However, now we only know that it is possible. We don't know yet if `a + b` is always more than 100.

#### Checking if the requirement will always hold

To check if our requirement always holds we will check for the **negation** of our requirement. Meaning that we are checking if the requirement can be violated. The only change is that we put `(not ...)` around our requirement.

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

This example shows that SMT tools can be used to check if logical requirements can be violated and that they can give a counter-example if it is violated.

For more complex systems you would generally not write these rules in z3 manually, but instead, generate them using a higher-level tool.

### Example: Symbolic execution

Consider the function `sumIsEven()`.

```Solidity
function sumIsEven(uint256 a, uint256 b) returns (bool) {
    uint256 sum = a + b;
    bool isEven = (sum % 2 == 0);

    return isEven;
}
```

First, let's make the difference between **concrete execution** and **symbolic execution** clear.

- **Concrete execution:** the parameters `a` and `b` would be assigned actual values (like `4` and `13`). The variable `sum` would be a concrete value (the result of `a + b`, for exampl,e `4 + 13 = 17`) and the function would return **either** `true` or `false`.
- **Symbolic execution:** the execution assigns the parameter `a` the symbolic value `A` and assigns to `b` the symbolic value `B`. The variable `sum` would now be assigned the symbolic value `A + B`. This can't be simplified due to `A` and `B` being symbolic. Since `sum % 2 == 0` is an if-statement in disguise, the execution splits into two branches. One where `isEven = true` and one where `isEven = false`. The execution now checks both branches further. A more visual example of this flow can be found below.

So when a variable would be used in a branch to determine which path to take, the symbolic execution would take both branches. When one of the branches would then throw an error, the tool would determine a concrete value (get a counter-example using an SMT checker) that would cause the program to take this branch.

#### Example

In the example below this process can be seen in action. The program has multiple possible paths starting from the top. the variables `x` and `y` are assigned the symbolic values `X` and `Y` respectively. Each time that the symbolic execution learns something about a variable it will be stored in the Path Condition (`PC`) for that particular path. One branch in the image below knows that the symbolic values meet `X <= Y` in that branch. While in the other branch the program knows that `X > Y` holds. This is simply based on the condition required for that path (the if-statement).

In between the two if-statements, the symbolic values are used for some arithmetic which is again done symbolically. In the end, the variable `x` is equal to the symbolic value `Y` while variable `y` equals the symbolic value `X`

In the end, there is one path that has a failing assert. The path condition (`PC`) there is `X > Y && Y > X`. Note that the left side of the `&&` is from the first branch while the right side is from the second branch.

Determining if this branch can be reached is done with an SMT checker. We saw in the example of the SMT checker already how to do simple checks in z3. Running the following code in the [online tool](https://microsoft.github.io/z3guide/playground/Freeform%20Editing) results in `unsat`. Meaning that the path is not reachable and thus we know that the loop does what it is expected to do.

```z3
(declare-const X Int)
(declare-const Y Int)

(assert (and (> X Y) (> Y X)))

(check-sat)
```

<img src="./img/Example-of-symbolic-execution-of-a-code.jpg" alt="Symbolic execution example" width="80%"/>

Source: https://www.researchgate.net/publication/314950910_Software_Static_Energy_Modeling_for_Modern_Processors

### Constraint Horn Clauses (CHC)

A set of CHC described the program with logic. It still uses an SMT checker as the backend.

For more information see https://www.cs.fsu.edu/~grigory/hornspec.pdf with the related presentation https://www.youtube.com/watch?v=kbtnye_q3PA.

### Matching logic

Docs: http://www.matching-logic.org/

Matching logic is used as the backbone of the K-framework on which KEVM is built.

## Verifying source code vs bytecode

The main benefit of working with bytecode is that you are working with the code which will be deployed. You are not dependent on potential errors in the compiler.

# More sources

- [Ethereum Formal Verification Blog](https://fv.ethereum.org/)
- [Formal Systems Laboratory](https://fsl.cs.illinois.edu/)
- [A list of formal verification tools for ethereum](https://github.com/leonardoalt/ethereum_formal_verification_overview)
- [Smart contract vulnerabilities](https://hacken.io/discover/smart-contract-vulnerabilities/)
