# Security scans & formal verification

This repository is meant to be used as a submodule in existing projects.

An example project that makes use of this repository is [smart-contract-analysis-tools-example](https://github.com/Byont-Ventures/smart-contract-analysis-tools-example).

- [Setup and usage](#setup-and-usage)
- [Available tools](#available-tools)

# Setup and usage

## Pre-requisites

- Docker should be installed
  - Make sure that Docker can run without sudo ([docs](https://docs.docker.com/engine/install/linux-postinstall/)).

## Installing Rust

```bash
$ curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
$ source ~/.bashrc
```

## Adding as submodule

In the root of your project run the following command. Afterwards, this repository can be found as a submodule under `<your project root>/security-scans/`.

```bash
$ git submodule add https://github.com/Byont-Ventures/smart-contract-analysis-tools security-scans
```

## Generating a report

### Security scans and report generation

Copy [analysis-config-example.toml](./analysis-config-example.toml) to the root of your project and update as required.

In this configuration file you can define the required paths for your project. You can also enable or disable different tools to run for the report generation.

After updating the configuration run the following command from your project root. Depending on which tools are enabled it can take from several seconds to an hour.

```bash
$ yarn --cwd <path to this submodule> run   \
    scan:generate-report                    \
    <absolute path to config file>
```

# Available tools

**DISCLAIMER**

> It is important to remember that no tool on it's own will find all problems in your smart contract. Nor are all found problems actual problems.
>
> We process the results from the tools to our best effort in order to give the most useful report.
>
> No guaranties about the security of your contract can be claimed based solely on the report.

More information about the techniques used in the tools can be found in the [analysis-techniques.md](./docs/pages/analysis-techniques.md) document.

## Slither (version 0.9.0)

- [**git**](https://github.com/crytic/slither/tree/0.9.0)
- **Estimated runtime:** a couple of seconds

Slither is a static analysis tool. It checks the code for several known [problems](https://github.com/crytic/slither/wiki/Detector-Documentation) when writing solidity code.

What is good about Slither is that in a very short time you get an idea of the quality of your code.

## Mythril (version 0.23.10)

- [**git**](https://github.com/ConsenSys/mythril/tree/v0.23.10)
- **Estimated runtime:** 30 minutes

Mythril is a symbolic execution tools that tries to find problems linked to the [SWC registry](https://swcregistry.io/). When it finds a problems it tries to create a sequence of transaction that will lead to the found problem.

## SMTChecker (version depends on solc version)

- [**docs**](https://docs.soliditylang.org/en/v0.8.17/smtchecker.html)
- **Estimated runtime:** 20 minutes

The SMTChecker is a tool that combines both a bounded model checker and a constraint Horn clause solver.

## KEVM (version 1.0.1-0e96c8d)

- [**git**](https://github.com/runtimeverification/evm-semantics/tree/v1.0.1-0e96c8d)
- **Estimated runtime:** 30 minutes

> This tool is not available yet for the report generation. Some more needs to be done on this.

KEVM is an implementation of the EVM in the [k-framework](https://github.com/runtimeverification/k). The k-framework is based on [matching logic](http://www.matching-logic.org/).

### Usage

While most tools don't require any user input other than some flags and the source files, kevm is different. For it to work you have to define for each function the expected state with optional pre- and postconditions. Additionally, sometimes you have to add custom rules for the analysis to work. Due to the manual changes required, the specifications for the contracts should be created outside of the submodule. The path to these specifications should be configured under the `[kevm]` section at `kevm_spec_rel_path` in the `analysis.toml` (here called [`./analysis-config-example.toml`](./analysis-config-example.toml)) file.

The specification file **MUST** have the name `<contract name>-spec.md`. An example can be found at [VeriToken-spec.md](./kevm-example-spec/VeriToken-spec.md).

> TODO: Currently updating `analysis.toml` for kevm doesn't do anything. Instead, run the command below to run kevm.

From the root of the project repository that uses this as a submodule run the following command

```bash
$ yarn --cwd ./security-scans run                   \
    scan:kevm                                       \
    ${PWD}                                          \
    <Relative path to the this submodule>           \
    <Relative path to the contract source folder>   \
    <Relative path to the kevm specs folder>        \
    <contract name without .sol>
```

As an example:

```bash
$ yarn --cwd ./security-scans run   \
    scan:kevm                       \
    ${PWD}                          \
    ./security-scans                \
    ./src/smart-contracts           \
    ./kevm-specs                    \
    VeriToken
```
