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

echo ""                                                                     | tee ${outputFile}
echo "================================================================="    | tee -a ${outputFile}
echo "Running SMTChecker"                                                   | tee -a ${outputFile}
echo "================================================================="    | tee -a ${outputFile}
echo ""                                                                     | tee -a ${outputFile}

docker run --pull --rm -v ${projectRoot}:/prj ghcr.io/byont-ventures/analysis-tools:latest bash -c " \
    cd /prj                                             \
    && solc-select use ${solcVersion}                   \
    && solc                                             \
    ${remappings}                                       \
    --model-checker-engine all                          \
    --model-checker-solvers all                         \
    --model-checker-targets all                         \
    --model-checker-timeout 60000                       \
    /prj/${pathToSourceFileFromRoot}/${contractName}.sol" 2>&1 | tee -a ${outputFile}
