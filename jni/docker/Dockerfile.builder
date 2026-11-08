# Pinned to a specific version of Ubuntu
ARG BASE_IMAGE=ubuntu:20.04@sha256:8feb4d8ca5354def3d8fce243717141ce31e2c428701f6682bd2fafe15388214
FROM ${BASE_IMAGE}

ENV DEBIAN_FRONTEND=noninteractive TZ=UTC PYTHONDONTWRITEBYTECODE=1

# Retain the package installs in the image.
RUN apt-get update -o Acquire::Retries=5 \
 && apt-get install -y --no-install-recommends -o Acquire::Retries=5 \
      build-essential wget unzip curl git patch python3 bzip2 ca-certificates zlib1g-dev \
      openjdk-17-jdk-headless \
 && rm -rf /var/lib/apt/lists/*
