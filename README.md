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

Copy [analysis-config-example.toml](./analysis-config-example.toml) and update as required.

The configuration of for the report generation is done in a `.toml` file. This chosen over json mainly because both Foundry and Rust use toml files for their configuration as well. On top of that, toml supports comments while json doesn't.

```bash
$ yarn --cwd <path to this folder> run  \
    scan:generate-report                \
    <absolute path to config file>
```
