#!/bin/bash
# Container management script for Formalize-CoT
# Supports both Podman and Docker

set -e

# Detect container runtime (prefer podman)
if command -v podman &> /dev/null; then
    RUNTIME="podman"
    COMPOSE="podman-compose"
elif command -v docker &> /dev/null; then
    RUNTIME="docker"
    COMPOSE="docker-compose"
else
    echo "Error: Neither podman nor docker found. Please install one of them."
    exit 1
fi

IMAGE_NAME="formalize-cot"
CONTAINER_NAME="formalize-cot"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

print_help() {
    echo "Formalize-CoT Container Management Script"
    echo ""
    echo "Usage: $0 <command>"
    echo ""
    echo "Commands:"
    echo "  build       Build the container image"
    echo "  run         Run an interactive shell in a new container"
    echo "  start       Start the container in background (using compose)"
    echo "  stop        Stop the running container"
    echo "  shell       Attach to running container's shell"
    echo "  exec <cmd>  Execute a command in the running container"
    echo "  test        Run formalization tests"
    echo "  clean       Remove container and image"
    echo "  logs        Show container logs"
    echo "  status      Show container status"
    echo ""
    echo "Examples:"
    echo "  $0 build                    # Build the container"
    echo "  $0 run                      # Start interactive session"
    echo "  $0 exec python --version   # Run a command"
    echo "  $0 test --folder ./data    # Run Lean tests"
}

build() {
    echo -e "${GREEN}Building container image...${NC}"
    $RUNTIME build -t $IMAGE_NAME -f Containerfile .
    echo -e "${GREEN}Build complete!${NC}"
}

run_interactive() {
    echo -e "${GREEN}Starting interactive container...${NC}"
    $RUNTIME run -it --rm \
        --name $CONTAINER_NAME \
        -v "$(pwd):/workspace:z" \
        -e OPENAI_API_KEY="${OPENAI_API_KEY:-}" \
        -e GOOGLE_API_KEY="${GOOGLE_API_KEY:-}" \
        -e ANTHROPIC_API_KEY="${ANTHROPIC_API_KEY:-}" \
        -w /workspace \
        $IMAGE_NAME /bin/bash
}

start_background() {
    echo -e "${GREEN}Starting container in background...${NC}"
    if command -v $COMPOSE &> /dev/null; then
        $COMPOSE -f container-compose.yml up -d
    else
        echo -e "${YELLOW}Compose not found, using runtime directly...${NC}"
        $RUNTIME run -d \
            --name $CONTAINER_NAME \
            -v "$(pwd):/workspace:z" \
            -e OPENAI_API_KEY="${OPENAI_API_KEY:-}" \
            -e GOOGLE_API_KEY="${GOOGLE_API_KEY:-}" \
            -e ANTHROPIC_API_KEY="${ANTHROPIC_API_KEY:-}" \
            -w /workspace \
            $IMAGE_NAME tail -f /dev/null
    fi
    echo -e "${GREEN}Container started!${NC}"
}

stop_container() {
    echo -e "${YELLOW}Stopping container...${NC}"
    if command -v $COMPOSE &> /dev/null; then
        $COMPOSE -f container-compose.yml down
    else
        $RUNTIME stop $CONTAINER_NAME 2>/dev/null || true
        $RUNTIME rm $CONTAINER_NAME 2>/dev/null || true
    fi
    echo -e "${GREEN}Container stopped!${NC}"
}

attach_shell() {
    echo -e "${GREEN}Attaching to container shell...${NC}"
    $RUNTIME exec -it $CONTAINER_NAME /bin/bash
}

exec_command() {
    shift  # Remove 'exec' from arguments
    $RUNTIME exec -it $CONTAINER_NAME "$@"
}

run_tests() {
    shift  # Remove 'test' from arguments
    echo -e "${GREEN}Running formalization tests...${NC}"
    $RUNTIME exec -it $CONTAINER_NAME python /workspace/test/formalization-test.py "$@"
}

clean() {
    echo -e "${YELLOW}Cleaning up...${NC}"
    $RUNTIME stop $CONTAINER_NAME 2>/dev/null || true
    $RUNTIME rm $CONTAINER_NAME 2>/dev/null || true
    $RUNTIME rmi $IMAGE_NAME 2>/dev/null || true
    echo -e "${GREEN}Cleanup complete!${NC}"
}

show_logs() {
    $RUNTIME logs $CONTAINER_NAME
}

show_status() {
    echo -e "${GREEN}Container Runtime: $RUNTIME${NC}"
    echo ""
    echo "Container Status:"
    $RUNTIME ps -a --filter "name=$CONTAINER_NAME"
    echo ""
    echo "Image Status:"
    $RUNTIME images $IMAGE_NAME
}

# Main script logic
case "${1:-}" in
    build)
        build
        ;;
    run)
        run_interactive
        ;;
    start)
        start_background
        ;;
    stop)
        stop_container
        ;;
    shell)
        attach_shell
        ;;
    exec)
        exec_command "$@"
        ;;
    test)
        run_tests "$@"
        ;;
    clean)
        clean
        ;;
    logs)
        show_logs
        ;;
    status)
        show_status
        ;;
    help|--help|-h)
        print_help
        ;;
    *)
        print_help
        exit 1
        ;;
esac


