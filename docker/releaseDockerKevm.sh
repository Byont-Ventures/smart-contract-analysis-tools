#!/bin/bash

echo ""
echo "================================================================="
echo "Create builder if not present"
echo "================================================================="
echo ""

builderContainerName=kevmBuildxBuilder

docker buildx use ${builderContainerName} >/dev/null 2>&1

# $? Gets the return status of the previous command 
if [ $? -eq 1 ]; then
    echo "Container '${builderContainerName}' doesn't exist. Creating it now."
    docker buildx create --name ${builderContainerName} --driver docker-container --bootstrap
    docker buildx use ${builderContainerName}
fi

echo ""
echo "================================================================="
echo "Build and push Dockerfile.kevm"
echo "================================================================="
echo ""

dockerEnv=$(dirname "$0")
docker buildx build --push --platform=linux/amd64,linux/arm64 --pull -t ghcr.io/byont-ventures/kevm:kevm-0e96c8d -f ${dockerEnv}/Dockerfile.kevm ${dockerEnv}