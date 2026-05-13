FROM mcr.microsoft.com/devcontainers/base:ubuntu-22.04

ARG DAFNY_VERSION=4.11.0

RUN apt-get update \
    && apt-get install -y wget unzip dotnet-runtime-8.0 \
    && rm -rf /var/lib/apt/lists/*

RUN wget -q "https://github.com/dafny-lang/dafny/releases/download/v${DAFNY_VERSION}/dafny-${DAFNY_VERSION}-x64-ubuntu-22.04.zip" -O /tmp/dafny.zip \
    && unzip -q /tmp/dafny.zip -d /opt/ \
    && rm /tmp/dafny.zip \
    && ln -s /opt/dafny/dafny /usr/local/bin/dafny
