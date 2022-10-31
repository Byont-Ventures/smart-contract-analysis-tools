#!/bin/bash

projectRoot=$1
contractName=$2

echo ""
echo "================================================================="
echo "Setup the local environment"
echo "================================================================="
echo ""

cd ${projectRoot}
projectRoot=${PWD}

cd ${projectRoot}/smart-contracts

# If you get an error saying: ERROR: [Errno 2] No such file or directory: 'install'
# Do the following: (https://stackoverflow.com/questions/46013544/yarn-install-command-error-no-such-file-or-directory-install)
#    apt remove cmdtest
#    apt remove yarn
#    curl -sS https://dl.yarnpkg.com/debian/pubkey.gpg | sudo apt-key add -
#    echo "deb https://dl.yarnpkg.com/debian/ stable main" | sudo tee /etc/apt/sources.list.d/yarn.list
#    apt update
#    apt install yarn -y

yarn install
git submodule update --init --recursive -- lib/forge-std 
cd ${projectRoot}

echo ""
echo "================================================================="
echo "Flatten the contract to be verified"
echo "================================================================="
echo ""

docker run --rm -v ${projectRoot}:/prj ghcr.io/foundry-rs/foundry:latest "  \
    cd /prj/smart-contracts                                                 \
    && forge flatten src/${contractName}.sol                                \
    --output ../flattened/${contractName}-flat.sol"

echo ""
echo "================================================================="
echo "Generate helper modules for kevm to make writing claims easier"
echo "================================================================="
echo ""

docker run --rm -v ${projectRoot}:/prj ghcr.io/byont-ventures/kevm:latest bash -c "                 \
    mkdir -p /prj/kevm/generated                                                                    \
    && kevm solc-to-k /prj/flattened/${contractName}-flat.sol ${contractName}                       \
    --pyk --verbose --profile --verbose --definition root/evm-semantics/.build/usr/lib/kevm/haskell \
    --main-module ${contractName}-VERIFICATION                                                      \
    > /prj/kevm/generated/${contractName}-bin-runtime.k"

echo ""
echo "================================================================="
echo "Generate the required files for verification"
echo "================================================================="
echo ""

# Whenever you change the specifications, run this command again.
docker run --rm -v ${projectRoot}:/prj ghcr.io/byont-ventures/kevm:latest bash -c "         \
    kevm kompile --backend haskell /prj/kevm/${contractName}-spec.md                        \
        --definition /prj/kevm/generated/${contractName}-spec/haskell                       \
        --main-module VERIFICATION                                                          \
        --syntax-module VERIFICATION                                                        \
        --concrete-rules-file /root/evm-semantics/tests/specs/examples/concrete-rules.txt   \
        -I root/evm-semantics/.build/usr/lib/kevm/include/kframework                        \
        -I root/evm-semantics/.build/usr/lib/kevm/blockchain-k-plugin/include/kframework    \
        --verbose"

echo ""
echo "================================================================="
echo "Verify the the Solidity contract"
echo "================================================================="
echo ""

docker run --rm -v ${projectRoot}:/prj ghcr.io/byont-ventures/kevm:latest bash -c " \
    kevm prove --backend haskell /prj/kevm/${contractName}-spec.md                  \
        --definition /prj/kevm/generated/${contractName}-spec/haskell               \
        --verbose"