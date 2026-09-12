FROM python:3.12-bookworm

# A native Chromium install avoids the Ubuntu Firefox/Chromium snap wrappers.
RUN apt-get update && apt-get install -y --no-install-recommends \
    ca-certificates curl git nodejs build-essential libgmp-dev sudo zstd \
    && rm -rf /var/lib/apt/lists/*

ENV PLAYWRIGHT_BROWSERS_PATH=/opt/playwright-browsers
COPY scripts/requirements-browser.txt /tmp/requirements-browser.txt
RUN pip install --no-cache-dir -r /tmp/requirements-browser.txt \
    && python -m playwright install --with-deps chromium \
    && chmod -R a+rX /opt/playwright-browsers \
    && rm -rf /var/lib/apt/lists/*

RUN useradd --create-home --shell /bin/bash vscode \
    && usermod -aG sudo vscode \
    && echo 'vscode ALL=(ALL) NOPASSWD:ALL' > /etc/sudoers.d/vscode \
    && chmod 0440 /etc/sudoers.d/vscode
USER vscode
ENV ELAN_HOME=/home/vscode/.elan
ENV PATH=/home/vscode/.elan/bin:${PATH}
COPY lean-toolchain /tmp/riemann-lean-toolchain
RUN curl --proto '=https' --tlsv1.2 -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o /tmp/elan-init.sh \
    && sh /tmp/elan-init.sh -y --default-toolchain none \
    && elan toolchain install "$(cat /tmp/riemann-lean-toolchain)"
WORKDIR /workspaces/RiemannGaussian
