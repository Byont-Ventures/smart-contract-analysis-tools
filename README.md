# Security scans & formal verification

This repository is meant to be used as a submodule in existing projects.

# Setup and usage

## Pre-requisites

- Docker should be installed

## Installing Rust

```bash
$ curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
$ source ~/.bashrc
```

## Update configs

> TODO: read the solc version to use from the project's foundry.toml and use that everywhere

### Update remappings

> TODO: Make a script that automatically reads the remappings from foundry.toml in the main project

In:

- [./slither/slither.config.json](./slither/slither.config.json)
- [./SMTChecker/run-SMTChecker.sh](./SMTChecker/run-SMTChecker.sh)

## Usage

The configuration of for the report generation is done in a `.toml` file. This chosen over json mainly because both Foundry and Rust use toml files for their configuration as well. On top of that, toml supports comments while json doesn't.

```bash
$ yarn --cwd <path to this folder> run  \
    scan:generate-report                \
    <absolute path to config file>
```
