# Security scans & formal verification

This repository is meant to be used as a submodule in existing projects.

# Setup and usage

## Pre-requisites

- Docker should be installed
  - Make sure that Docker can run without sudo ([docs](https://docs.docker.com/engine/install/linux-postinstall/)).

## Installing Rust

```bash
$ curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
$ source ~/.bashrc
```

## Usage

### Security scans and report generation

Copy [analysis-config-example.toml](./analysis-config-example.toml) and update as required.

The configuration of for the report generation is done in a `.toml` file. This chosen over json mainly because both Foundry and Rust use toml files for their configuration as well. On top of that, toml supports comments while json doesn't.

```bash
$ yarn --cwd <path to this folder> run  \
    scan:generate-report                \
    <absolute path to config file>
```

### KEVM

While most tools don't require any user input other than some flags and the source files, kevm is different. For it to work you have to define for each function the expected state with optional pre- and postconditions. Additionally, sometimes you have to add custom rules for the analysis to work. Due to the manual changes required, the specifications for the contracts should be created outside of the submodule (**or docker image if we want to use that instead**). The path to these specifications should be configured under the `[kevm]` section at `kevm_spec_rel_path` in the `analysis.toml` file.

From the root of the project repository that uses this is as a submodule.

```bash
$ yarn --cwd ./security-scans run   \
    scan:kevm                       \
    ${PWD}                          \
    ./security-scans                \
    ./src/smart-contracts           \
    ./kevm-specs                    \
    VeriToken
```
