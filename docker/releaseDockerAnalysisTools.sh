#!/bin/bash

echo ""
echo "================================================================="
echo "Build and push Dockerfile.hevm"
echo "================================================================="
echo ""

dockerEnv=$(dirname "$0")

docker buildx create --use
docker buildx build --push --platform=linux/amd64 --pull -t ghcr.io/byont-ventures/analysis-tools:latest -f ${dockerEnv}/Dockerfile.analysisTools ${dockerEnv}
