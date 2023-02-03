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
outputFile=$(dirname "$0")/results/${contractName}/${contractName}-SMTChecker.result

dockerImage=ghcr.io/byont-ventures/analysis-toolbox:latest

echo ""                                                                     | tee ${outputFile}
echo "================================================================="    | tee -a ${outputFile}
echo "Pulling latest ${dockerImage}"                                        | tee -a ${outputFile}
echo "================================================================="    | tee -a ${outputFile}
echo ""                                                                     | tee -a ${outputFile}

docker pull ${dockerImage}

echo ""                                                                     | tee -a ${outputFile}
echo "================================================================="    | tee -a ${outputFile}
echo "Running SMTChecker"                                                   | tee -a ${outputFile}
echo "================================================================="    | tee -a ${outputFile}
echo ""                                                                     | tee -a ${outputFile}

docker run --rm -v ${projectRoot}:/prj ${dockerImage} bash -c " \
    cd /prj                                                     \
    && solc                                                     \
    ${remappings}                                               \
    --model-checker-engine all                                  \
    --model-checker-solvers all                                 \
    --model-checker-targets all                                 \
    --model-checker-timeout 60000                               \
    /prj/${pathToSourceFileFromRoot}/${contractName}.sol" 2>&1 | tee -a ${outputFile}
