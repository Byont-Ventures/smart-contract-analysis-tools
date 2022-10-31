#!/bin/bash

echo ""
echo "================================================================="
echo "Build and push Dockerfile.kevm"
echo "================================================================="
echo ""

dockerEnv=$(dirname "$0")

docker buildx create --use
docker buildx build --push --platform=linux/amd64 --pull -t ghcr.io/byont-ventures/kevm:latest -f ${dockerEnv}/Dockerfile.kevm ${dockerEnv}
