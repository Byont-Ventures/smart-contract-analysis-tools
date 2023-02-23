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
echo "Run Mythril: callgraph"                                               | tee -a ${outputFile}
echo "================================================================="    | tee -a ${outputFile}
echo ""                                                                     | tee -a ${outputFile}

docker run --rm -v ${projectRoot}:/prj ${dockerImage} bash -c " \
    sed -i '67s/match\(.*\)/search(r\"\d+.\d+.\d+\", main_version).group(0)/' /mythril/mythril/mythril/mythril_disassembler.py  \
    && sed -i '67s/d+/\\\d+/g' /mythril/mythril/mythril/mythril_disassembler.py                                                 \
    && sed -i \"68s/^$/        log.info(main_version_number)/\" /mythril/mythril/mythril/mythril_disassembler.py                \
    && echo '{  \"remappings\": [ ${remappings} ] }' > /settings.json           \
    && cd /prj                                                                  \
    && myth -v 4                                                                \
    analyze                                                                     \
    -o jsonv2                                                                   \
    --transaction-count 2                                                       \
    --parallel-solving                                                          \
    --strategy bfs                                                              \
    --max-depth 64                                                              \
    --call-depth-limit 2                                                        \
    --no-onchain-data                                                           \
    --pruning-factor 1                                                          \
    --solv ${solcVersion}                                                       \
    --solc-args \"--base-path /prj\"                                            \
    --solc-json /settings.json                                                  \
    -g /prj/${pathToSecurityScansFromRoot}/mythril/results/${contractName}/${contractName}-graph-Mythril.html   \
     ./${pathToSourceFileFromRoot}/${contractName}.sol" 2>&1 | tee -a ${outputFile}

echo ""                                                                     | tee -a ${outputFile}
echo "================================================================="    | tee -a ${outputFile}    
echo "Run Mythril analyze"                                                  | tee -a ${outputFile}
echo "================================================================="    | tee -a ${outputFile}
echo "" 

# See https://github.com/ConsenSys/mythril/issues/1735 for the reason of the sed commands
docker run --rm -v ${projectRoot}:/prj ${dockerImage} bash -c " \
    sed -i '67s/match\(.*\)/search(r\"\d+.\d+.\d+\", main_version).group(0)/' /mythril/mythril/mythril/mythril_disassembler.py  \
    && sed -i '67s/d+/\\\d+/g' /mythril/mythril/mythril/mythril_disassembler.py                                                 \
    && echo '{  \"remappings\": [ ${remappings} ] }' > /settings.json           \
    && cd /prj                                                                  \
    && myth -v 4                                                                \
    analyze                                                                     \
    -o jsonv2                                                                   \
    --transaction-count 2                                                       \
    --parallel-solving                                                          \
    --strategy bfs                                                              \
    --max-depth 64                                                              \
    --call-depth-limit 2                                                        \
    --no-onchain-data                                                           \
    --pruning-factor 1                                                          \
    --solv ${solcVersion}                                                       \
    --solc-args \"--base-path /prj\"                                            \
    --solc-json /settings.json                                                  \
     ./${pathToSourceFileFromRoot}/${contractName}.sol" 2>&1 | tee -a ${outputFile}