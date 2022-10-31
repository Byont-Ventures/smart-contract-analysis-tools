# SMTChecker (solc)

[SMTChecker](https://docs.soliditylang.org/en/v0.8.17/smtchecker.html) is a model checker. SMTChecker makes uses of a [Bounded Model Checker](https://docs.soliditylang.org/en/v0.8.17/smtchecker.html#model-checking-engines) (BMC) and a [Constraint Horn Clauses engine](https://docs.soliditylang.org/en/v0.8.17/smtchecker.html#constrained-horn-clauses-chc) (CHC). A good video about [horn clauses](https://www.youtube.com/watch?v=hgw59_HBU2A) The CHC engine (that uses a Horn solver (SPACER, part of z3)) takes the whole contract into account over multiple transactions. It should be notes that the BMC (that uses an SMT solver) in SMTChecker is relatively lightweight as it only checks a function in isolation.

Somewhat outdated, but it shows te difficulties of writing a good checker: https://www.aon.com/cyber-solutions/aon_cyber_labs/exploring-soliditys-model-checker/
https://fv.ethereum.org/2021/01/18/smtchecker-and-synthesis-of-external-functions/

Using the custom Docker image because the [official solc image](https://hub.docker.com/r/ethereum/solc) doesn't include z3 and/or cvc4.

For more information about the SMTChecker see the [Solidity docs](https://docs.soliditylang.org/en/v0.8.17/smtchecker.html).

# Limiations
