FROM mcr.microsoft.com/devcontainers/base:ubuntu-22.04

ARG DAFNY_VERSION=4.11.0
ARG DAFNY_EXT_VERSION=3.5.4

# .NET 8 SDK (includes runtime; needed by `dafny build` to compile to C#).
# Pre-installing the SDK avoids the Dafny VS Code extension fetching its own.
RUN apt-get update \
    && apt-get install -y --no-install-recommends \
        wget unzip ca-certificates \
        dotnet-sdk-8.0 \
    && rm -rf /var/lib/apt/lists/*

# Pre-install Dafny into /opt/dafny and expose on PATH.
RUN wget -q "https://github.com/dafny-lang/dafny/releases/download/v${DAFNY_VERSION}/dafny-${DAFNY_VERSION}-x64-ubuntu-22.04.zip" -O /tmp/dafny.zip \
    && unzip -q /tmp/dafny.zip -d /opt/ \
    && rm /tmp/dafny.zip \
    && ln -s /opt/dafny/dafny /usr/local/bin/dafny \
    && dafny --version

# Pre-bake the Dafny VS Code extension into the vscode-server extension cache,
# so the editor doesn't fetch it on every Codespace start.
RUN mkdir -p /home/vscode/.vscode-server/extensions \
    && wget -q "https://dafny-lang.gallery.vsassets.io/_apis/public/gallery/publisher/dafny-lang/extension/ide-vscode/${DAFNY_EXT_VERSION}/assetbyname/Microsoft.VisualStudio.Services.VSIXPackage" \
        -O /tmp/dafny-ext.vsix \
    && unzip -q /tmp/dafny-ext.vsix -d /tmp/dafny-ext \
    && mv /tmp/dafny-ext/extension "/home/vscode/.vscode-server/extensions/dafny-lang.ide-vscode-${DAFNY_EXT_VERSION}" \
    && rm -rf /tmp/dafny-ext /tmp/dafny-ext.vsix \
    && chown -R vscode:vscode /home/vscode/.vscode-server
