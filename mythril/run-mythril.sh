#!/bin/bash

projectRoot=$1
pathToSecurityScansFromRoot=$2
pathToSourceFileFromRoot=$3
contractName=$4

if [ -z "${contractName}" ]
then
    echo ""
    echo "Please provide the name of the contract without '.sol'"
    echo ""
    exit 1
fi

mkdir -p $(dirname "$0")/results/${contractName}
outputFile=$(dirname "$0")/results/${contractName}/${contractName}-Mythril.result

echo ""                                                                     | tee ${outputFile}
echo "================================================================="    | tee -a ${outputFile}
echo "Generate bin-runtime: solc ${solcVersion}"                            | tee -a ${outputFile}
echo "================================================================="    | tee -a ${outputFile}
echo ""                                                                     | tee -a ${outputFile}

docker run --rm -v ${projectRoot}:/prj ethereum/solc:${solcVersion}     \
    --base-path /prj                                                    \
    ds-test/=libs/forge-std/lib/ds-test/src/                            \
    forge-std/=libs/forge-std/src/                                      \
    @openzeppelin/=node_modules/@openzeppelin/                          \
    @smart-contracts=src/smart-contracts/                               \
    -o /prj/${pathToSourceFileFromRoot}/solc-out                        \
    --opcodes                                                           \
    --asm                                                               \
    --bin-runtime                                                       \
    --overwrite                                                         \
    /prj/src/smart-contracts/${contractName}.sol 2>&1 | tee -a ${outputFile}

echo ""                                                                     | tee -a ${outputFile}
echo "================================================================="    | tee -a ${outputFile}    
echo "Run Mythril: callgraph"                                               | tee -a ${outputFile}
echo "================================================================="    | tee -a ${outputFile}
echo ""                                                                     | tee -a ${outputFile}
  
docker run --rm -v ${projectRoot}:/prj mythril/myth:0.23.10 \
     -v 4                                                   \
    analyze                                                 \
    --solv ${solcVersion}                                   \
    -g /prj/${pathToSecurityScansFromRoot}/mythril/results/${contractName}/${contractName}-graph-Mythril.html \
    -f /prj/${pathToSourceFileFromRoot}/solc-out/${contractName}.bin-runtime \
    --bin-runtime                                           \
    2>&1 | tee -a ${outputFile}

echo ""                                                                     | tee -a ${outputFile}
echo "================================================================="    | tee -a ${outputFile}    
echo "Run Mythril analyze"                                                  | tee -a ${outputFile}
echo "================================================================="    | tee -a ${outputFile}
echo "" 

docker run --rm -v ${projectRoot}:/prj mythril/myth:0.23.10 \
     -v 4                                                   \
    analyze                                                 \
    --solv ${solcVersion}                                   \
    -o jsonv2                                               \
    --transaction-count 3                                   \
    --parallel-solving                                      \
    --strategy bfs                                          \
    --max-depth 128                                         \
    --call-depth-limit 3                                    \
    --no-onchain-data                                       \
    --pruning-factor 1                                      \
    -f /prj/${pathToSourceFileFromRoot}/solc-out/${contractName}.bin-runtime \
    --bin-runtime                                           \
    2>&1 | tee -a ${outputFile}