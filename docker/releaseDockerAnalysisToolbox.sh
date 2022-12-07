#!/bin/bash

echo ""
echo "================================================================="
echo "Create builder if not present"
echo "================================================================="
echo ""

builderContainerName=analysisToolboxBuildxBuilder

# Suppress the output string
docker buildx use ${builderContainerName} >/dev/null 2>&1

# $? Gets the return status of the previous command 
if [ $? -eq 1 ]; then
    echo "Container '${builderContainerName}' doesn't exist. Creating it now."
    docker buildx create --name ${builderContainerName} --driver docker-container --bootstrap
    docker buildx use ${builderContainerName}
fi

echo ""
echo "================================================================="
echo "Build and push Dockerfile.hevm"
echo "================================================================="
echo ""

dockerEnv=$(dirname "$0")
docker buildx build --push --platform=linux/arm64 --pull -t ghcr.io/byont-ventures/analysis-toolbox:latest -f ${dockerEnv}/Dockerfile.analysisToolbox ${dockerEnv}
