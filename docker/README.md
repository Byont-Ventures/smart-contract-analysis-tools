# Docker

## Images

> NOTE: Currently only amd64 / x86-64 compatible images are available.

- analysis-tools: [ghcr.io/byont-ventures/analysis-tools:latest](https://github.com/orgs/Byont-Ventures/packages/container/package/analysis-tools)
- kevm: [ghcr.io/byont-ventures/kevm:latest](https://github.com/orgs/Byont-Ventures/packages/container/package/kevm)

## Build and push images

You might need sudo depending on your system.

To build the dockerfile to use `hevm`, `slither` and the `SMTChecker` run:

```bash
$ ./releaseDockerAnalysisTools.sh
```

Building the image to use `kevm` requires:

```bash
$ ./releaseDockerKevm.sh
```
