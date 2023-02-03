#!/bin/bash

projectRoot=$1
contractName=$2
functionSig=$3
solcVersion=$3

mkdir -p $(dirname "$0")/results/${contractName}
outputFile=$(dirname "$0")/results/${contractName}/${contractName}-hevm.result

echo ""                                                                     | tee ${outputFile}
echo "================================================================="    | tee -a ${outputFile}
echo "Generate bin-runtime: solc ${solcVersion}"                            | tee -a ${outputFile}
echo "================================================================="    | tee -a ${outputFile}
echo ""                                                                     | tee -a ${outputFile}

docker run --rm -v ${projectRoot}s:/prj ethereum/solc:${solcVersion}    \
    --base-path /prj                                                    \
    --include-path /prj/node_modules                                    \
    --include-path /prj/lib                                             \
    -o /prj/src/smart-contracts/solc-out                                \
    --bin-runtime                                                       \
    --overwrite                                                         \
    /prj/src/smart-contracts/${contractName}.sol 2>&1 | tee -a ${outputFile}

echo ""                                                                     | tee -a ${outputFile}
echo "================================================================="    | tee -a ${outputFile}
echo "Function: ${functionSig}"                                             | tee -a ${outputFile}
echo "================================================================="    | tee -a ${outputFile}
echo ""                                                                     | tee -a ${outputFile}

# The assertions options are described [here](https://docs.soliditylang.org/en/latest/control-structures.html#panic-via-assert-and-error-via-require).
docker run --rm ghcr.io/byont-ventures/analysis-tools:01-02-2023_11-18 /bin/bash -c "             \
    solc-select install ${solcVersion}                                                  \
    && solc-select use ${solcVersion}                                                   \
    && hevm symbolic --smttimeout 60000                                                 \
    --assertions '[0x00, 0x01, 0x11, 0x12, 021, 0x22, 0x31, 0x32, 0x41, 0x51]'          \
    --storage-model InitialS                                                            \
    --code $(< ${projectRoot}/src/smart-contracts/solc-out/${contractName}.bin-runtime) \
    --sig '${functionSig}'" 2>&1 | tee -a ${outputFile}