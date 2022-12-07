#!/bin/bash

projectRoot=$1
pathToSecurityScansFromRoot=$2
pathToSourceFileFromRoot=$3
pathToKevmSpecFromRoot=$4
contractName=$5

solcVersion=0.8.13
# Even though 0.8.17 uses LONDON, there seem to be a problem with
# evm version >= BERLIN with regard to #accessStorage
# However, since the schedule seems to only be related to the gas costs (https://github.com/runtimeverification/evm-semantics/blob/v1.0.1-0e96c8d/evm.md#london-schedule),
# it seem fair enough to use ISTABUL instead.
# An issue about this is created: https://github.com/runtimeverification/evm-semantics/issues/1469
evmVersion=ISTANBUL

if [ -z "${contractName}" ]
then
    echo ""
    echo "Please provide the name of the contract without '.sol'"
    echo ""
    exit 1
fi

# If you get an error saying: ERROR: [Errno 2] No such file or directory: 'install'
# Do the following: (https://stackoverflow.com/questions/46013544/yarn-install-command-error-no-such-file-or-directory-install)
#    apt remove cmdtest
#    apt remove yarn
#    curl -sS https://dl.yarnpkg.com/debian/pubkey.gpg | sudo apt-key add -
#    echo "deb https://dl.yarnpkg.com/debian/ stable main" | sudo tee /etc/apt/sources.list.d/yarn.list
#    apt update
#    apt install yarn -y

mkdir -p $(dirname "$0")/results/${contractName}
outputFile=$(dirname "$0")/results/${contractName}/${contractName}-kevm.result

echo ""                                                                     | tee ${outputFile}
echo "================================================================="    | tee -a ${outputFile}
echo "Flatten the contract to be verified"                                  | tee -a ${outputFile}
echo "================================================================="    | tee -a ${outputFile}
echo ""                                                                     | tee -a ${outputFile}

docker run --rm -v ${projectRoot}:/prj ghcr.io/byont-ventures/kevm:AnalysisToolbox bash -c "    \
    cd /prj/                                                                                    \
    && forge flatten ${pathToSourceFileFromRoot}/${contractName}.sol                            git submodule update --init --recursive\
    --output ${pathToSecurityScansFromRoot}/flattened/${contractName}-flat.sol" 2>&1 | tee -a ${outputFile}

echo ""                                                                     | tee -a ${outputFile}
echo "================================================================="    | tee -a ${outputFile}
echo "Generate helper modules for kevm to make writing claims easier"       | tee -a ${outputFile}
echo "================================================================="    | tee -a ${outputFile}
echo ""                                                                     | tee -a ${outputFile}

docker run --rm -v ${projectRoot}:/prj ghcr.io/byont-ventures/kevm:AnalysisToolbox bash -c "                    \
    mkdir -p /prj/${pathToSecurityScansFromRoot}/kevm/generated                                                 \
    && svm install ${solcVersion} && svm use ${solcVersion}                                                     \
    && kevm solc-to-k /prj/${pathToSecurityScansFromRoot}/flattened/${contractName}-flat.sol ${contractName}    \
    --schedule ${evmVersion}                                                                                    \
    --pyk --verbose --profile --verbose --definition /root/evm-semantics/.build/usr/lib/kevm/haskell            \
    --main-module ${contractName}-VERIFICATION                                                                  \
    > /prj/${pathToSecurityScansFromRoot}/kevm/generated/${contractName}-bin-runtime.k" 2>&1 | tee -a ${outputFile}

echo ""                                                                     | tee -a ${outputFile}
echo "================================================================="    | tee -a ${outputFile}
echo "Generate the required files for verification"                         | tee -a ${outputFile}
echo "================================================================="    | tee -a ${outputFile}
echo ""                                                                     | tee -a ${outputFile}

# Whenever you change the specifications, run this command again.
docker run --rm -v ${projectRoot}:/prj ghcr.io/byont-ventures/kevm:AnalysisToolbox bash -c "            \
    kevm kompile --backend haskell /prj/${pathToKevmSpecFromRoot}/${contractName}-spec.md               \
        --definition /prj/${pathToSecurityScansFromRoot}/kevm/generated/${contractName}-spec/haskell    \
        --schedule ${evmVersion}                                                                        \
        --main-module VERIFICATION                                                                      \
        --syntax-module VERIFICATION                                                                    \
        --concrete-rules-file /root/evm-semantics/tests/specs/examples/concrete-rules.txt               \
        -I /root/evm-semantics/.build/usr/lib/kevm/include/kframework                                   \
        -I /root/evm-semantics/.build/usr/lib/kevm/blockchain-k-plugin/include/kframework               \
        --verbose" 2>&1 | tee -a ${outputFile}

echo ""                                                                     | tee -a ${outputFile}
echo "================================================================="    | tee -a ${outputFile}
echo "Verify the the Solidity contract"                                     | tee -a ${outputFile}
echo "================================================================="    | tee -a ${outputFile}
echo ""                                                                     | tee -a ${outputFile}

docker run --rm -v ${projectRoot}:/prj ghcr.io/byont-ventures/kevm:AnalysisToolbox bash -c "            \
    kevm prove --backend haskell /prj/${pathToKevmSpecFromRoot}/${contractName}-spec.md                 \
        --definition /prj/${pathToSecurityScansFromRoot}/kevm/generated/${contractName}-spec/haskell    \
        --schedule ${evmVersion}                                                                        \
        --verbose" 2>&1 | tee -a ${outputFile}