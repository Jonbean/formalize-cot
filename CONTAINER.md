# Container Setup for Formalize-CoT

This document describes how to run Formalize-CoT in a containerized environment using Podman (or Docker).

## Prerequisites

- [Podman](https://podman.io/getting-started/installation) (recommended) or [Docker](https://docs.docker.com/get-docker/)
- Optional: `podman-compose` or `docker-compose` for compose workflows

## Quick Start

### 1. Build the Container

```bash
# Using the helper script (auto-detects podman/docker)
./container-run.sh build

# Or manually with podman
podman build -t formalize-cot -f Containerfile .

# Or with docker
docker build -t formalize-cot -f Containerfile .
```

### 2. Run Interactive Shell

```bash
# Using the helper script
./container-run.sh run

# Or manually
podman run -it --rm \
    -v $(pwd):/workspace:z \
    -e OPENAI_API_KEY="your-key-here" \
    -w /workspace \
    formalize-cot /bin/bash
```

### 3. Run with Compose (Background Mode)

```bash
# Start in background
./container-run.sh start

# Attach to shell
./container-run.sh shell

# Stop
./container-run.sh stop
```

## Helper Script Commands

The `container-run.sh` script provides convenient commands:

| Command | Description |
|---------|-------------|
| `build` | Build the container image |
| `run` | Run an interactive shell in a new container |
| `start` | Start the container in background |
| `stop` | Stop the running container |
| `shell` | Attach to running container's shell |
| `exec <cmd>` | Execute a command in the running container |
| `test` | Run formalization tests |
| `clean` | Remove container and image |
| `logs` | Show container logs |
| `status` | Show container status |

### Examples

```bash
# Build and run interactive session
./container-run.sh build
./container-run.sh run

# Run Lean formalization tests
./container-run.sh test --folder ./data/lean_files

# Execute a specific command
./container-run.sh exec python --version
./container-run.sh exec python translators/amr2lean/amr2lean.py --help

# Check status
./container-run.sh status
```

## Environment Variables

Set API keys before running the container:

```bash
# Option 1: Export in your shell
export OPENAI_API_KEY="sk-..."
export GOOGLE_API_KEY="..."
export ANTHROPIC_API_KEY="..."
./container-run.sh run

# Option 2: Create a .env file
cat > .env << EOF
OPENAI_API_KEY=sk-...
GOOGLE_API_KEY=...
ANTHROPIC_API_KEY=...
EOF

# Then use with podman-compose
podman-compose --env-file .env -f container-compose.yml up -d
```

## What's Included in the Container

The container image includes:

- **Python 3.10.18** - Base Python environment
- **All pip dependencies** - From `requirements.txt`
- **AMRToolBox** - Pre-installed from GitHub
- **Elan** - Lean version manager
- **Lean 4** - Installed via `lean_interact`
- **Git, curl, wget** - Common utilities

## Volume Mounts

By default, the container mounts:

- `.:/workspace` - Your project directory (read-write)
- `lean-elan:/root/.elan` - Persisted Lean toolchains (compose mode)

The `:z` flag is for SELinux systems (like Fedora). Remove it if not needed.

## Running Tests

Run the formalization test module inside the container:

```bash
# Quick test
./container-run.sh test --folder ./path/to/lean/files

# With all options
./container-run.sh exec python test/formalization-test.py \
    --folder ./data/lean_files \
    --output results.csv \
    --lean-version v4.23.0 \
    --verbose
```

## Customization

### Change Lean Version

Edit the `Containerfile` or pass it at runtime:

```bash
podman run -it --rm \
    -v $(pwd):/workspace:z \
    formalize-cot \
    python test/formalization-test.py --folder ./data --lean-version v4.25.0
```

### Add More Dependencies

1. Add to `requirements.txt`
2. Rebuild: `./container-run.sh build`

### Use as Non-Root User

The Containerfile includes optional non-root user setup. Uncomment and rebuild if needed.

## Troubleshooting

### Permission Denied on Linux

If you get permission errors on mounted volumes:

```bash
# Use :z flag for SELinux
podman run -v $(pwd):/workspace:z ...

# Or disable SELinux for the container
podman run --security-opt label=disable -v $(pwd):/workspace ...
```

### Lean Installation Issues

If Lean isn't working, try reinstalling inside the container:

```bash
./container-run.sh shell
install-lean
```

### Out of Memory

Lean can be memory-intensive. Increase container memory:

```bash
podman run --memory=4g ...
```

## File Structure

```
formalize-cot/
├── Containerfile           # Container build instructions
├── container-compose.yml   # Compose configuration
├── container-run.sh        # Helper script
├── .containerignore        # Files to exclude from build
└── CONTAINER.md            # This documentation
```

