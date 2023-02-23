#!/bin/bash

projectRoot=$1
pathToSecurityScansFromRoot=$2
pathToSourceFileFromRoot=$3
contractName=$4
solcVersion=$5
remappings=$6

if [ -z "${contractName}" ]
then
    echo ""
    echo "Please provide the name of the contract without '.sol'"
    echo ""
    exit 1
fi

mkdir -p $(dirname "$0")/results/${contractName}
outputFile=$(dirname "$0")/results/${contractName}/${contractName}-Mythril.result

dockerImage=ghcr.io/byont-ventures/analysis-toolbox:01-02-2023_11-18

echo ""                                                                     | tee ${outputFile}
echo "================================================================="    | tee -a ${outputFile}
echo "Pulling image ${dockerImage}"                                         | tee -a ${outputFile}
echo "================================================================="    | tee -a ${outputFile}
echo ""                                                                     | tee -a ${outputFile}

docker pull ${dockerImage}

echo ""                                                                     | tee -a ${outputFile}
echo "================================================================="    | tee -a ${outputFile}
echo "Generate bin-runtime: solc ${solcVersion}"                            | tee -a ${outputFile}
echo "================================================================="    | tee -a ${outputFile}
echo ""                                                                     | tee -a ${outputFile}

docker run --rm -v ${projectRoot}:/prj ${dockerImage} bash -c "     \
    solc --base-path /prj                                           \
        ${remappings}                                               \
        -o /prj/${pathToSourceFileFromRoot}/solc-out                \
        --opcodes                                                   \
        --asm                                                       \
        --bin-runtime                                               \
        --overwrite                                                 \
        /prj/${pathToSourceFileFromRoot}/${contractName}.sol" 2>&1 | tee -a ${outputFile}

echo ""                                                                     | tee -a ${outputFile}
echo "================================================================="    | tee -a ${outputFile}    
echo "Run Mythril: callgraph"                                               | tee -a ${outputFile}
echo "================================================================="    | tee -a ${outputFile}
echo ""                                                                     | tee -a ${outputFile}
  
docker run --rm -v ${projectRoot}:/prj ${dockerImage} bash -c "                                                 \
    myth -v 4                                                                                                   \
    analyze                                                                                                     \
    -g /prj/${pathToSecurityScansFromRoot}/mythril/results/${contractName}/${contractName}-graph-Mythril.html   \
    -f /prj/${pathToSourceFileFromRoot}/solc-out/${contractName}.bin-runtime                                    \
    --bin-runtime" 2>&1 | tee -a ${outputFile}

echo ""                                                                     | tee -a ${outputFile}
echo "================================================================="    | tee -a ${outputFile}    
echo "Run Mythril analyze"                                                  | tee -a ${outputFile}
echo "================================================================="    | tee -a ${outputFile}
echo "" 

docker run --rm -v ${projectRoot}:/prj ${dockerImage} bash -c "                 \
    myth -v 4                                                                   \
    analyze                                                                     \
    -o jsonv2                                                                   \
    --transaction-count 1                                                       \
    --parallel-solving                                                          \
    --strategy bfs                                                              \
    --max-depth 64                                                              \
    --call-depth-limit 2                                                        \
    --no-onchain-data                                                           \
    --pruning-factor 1                                                          \
    -f /prj/${pathToSourceFileFromRoot}/solc-out/${contractName}.bin-runtime    \
    --bin-runtime" 2>&1 | tee -a ${outputFile}