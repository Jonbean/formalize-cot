# Containerfile for Formalize-CoT
# Compatible with both Podman and Docker
# Build: podman build -t formalize-cot .
# Run: podman run -it --rm -v $(pwd):/workspace formalize-cot

FROM python:3.10.18-slim-bookworm

LABEL maintainer="formalize-cot"
LABEL description="Formalize-CoT: Natural Language Reasoning Formalization"

# Set environment variables
ENV PYTHONDONTWRITEBYTECODE=1 \
    PYTHONUNBUFFERED=1 \
    PIP_NO_CACHE_DIR=1 \
    PIP_DISABLE_PIP_VERSION_CHECK=1

# Install system dependencies
RUN apt-get update && apt-get install -y --no-install-recommends \
    git \
    curl \
    wget \
    build-essential \
    && rm -rf /var/lib/apt/lists/*

# Install elan (Lean version manager) for lean_interact
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain none
ENV PATH="/root/.elan/bin:${PATH}"

# Create workspace directory
WORKDIR /workspace

# Copy requirements first for better caching
COPY requirements.txt /workspace/requirements.txt

# Install Python dependencies
RUN pip install --upgrade pip && \
    pip install -r requirements.txt

# Clone and install AMRToolBox (optional - may fail if repo is private)
# If this fails, you can mount AMRToolBox as a volume later
RUN git clone https://github.com/Jonbean/AMRToolBox.git /opt/AMRToolBox && \
    cd /opt/AMRToolBox && \
    pip install -e . || echo "AMRToolBox installation skipped - clone manually if needed"

# Install Lean via lean_interact's install-lean command
RUN install-lean || echo "Lean installation will complete on first use"

# Copy the rest of the project
COPY . /workspace

# Create a non-root user (optional, for better security)
ARG UID=1000
ARG GID=1000
RUN groupadd -g ${GID} fcot || true && \
    useradd -m -u ${UID} -g ${GID} fcot || true

# Set default command
CMD ["/bin/bash"]

