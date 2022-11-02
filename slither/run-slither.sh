#!/bin/bash

projectRoot=$1
pathToSecurityScansFromRoot=$2
pathToSourceFileFromRoot=$3
contractName=$4
solcRemaps=$5

solcRemaps="ds-test/=libs/forge-std/lib/ds-test/src/,
    forge-std/=libs/forge-std/src/,
    @openzeppelin/=node_modules/@openzeppelin/,
    @smart-contracts=src/smart-contracts/"

if [ -z "${contractName}" ]
then
    echo ""
    echo "Please provide the name of the contract without '.sol'"
    echo ""
    exit 1
fi

mkdir -p $(dirname "$0")/results/${contractName}
outputFile=$(dirname "$0")/results/${contractName}/${contractName}-Slither.result

echo ""                                                                     | tee ${outputFile}
echo "================================================================="    | tee -a ${outputFile}
echo "Run Slither"                                                          | tee -a ${outputFile}
echo "================================================================="    | tee -a ${outputFile}        
echo ""                                                                     | tee -a ${outputFile}

docker run --rm -v ${projectRoot}:/prj ghcr.io/byont-ventures/analysis-tools:latest /bin/bash -c "  \
    cd /prj                                                                                         \
    && rm -f ${pathToSecurityScansFromRoot}/slither/results/${contractName}/${contractName}-output.json           \
    && slither --json ${pathToSecurityScansFromRoot}/slither/results/${contractName}/${contractName}-output.json  \
    --config-file ${pathToSecurityScansFromRoot}/slither/slither.config.json    \
    --solc-remaps ${solcRemaps}                                                 \
    ${pathToSourceFileFromRoot}/${contractName}.sol" 2>&1 | tee -a ${outputFile}
