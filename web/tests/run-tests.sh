#!/bin/bash
# TGP Integration Test Runner
# Runs automated integration tests for the web demo

set -e

echo "========================================="
echo "TGP Integration Test Suite"
echo "========================================="
echo ""

# Colors
GREEN='\033[0;32m'
RED='\033[0;31m'
YELLOW='\033[1;33m'
NC='\033[0m'

# Check if we're in the right directory
if [ ! -f "../index.html" ]; then
    echo -e "${RED}Error: Must run from web/tests directory${NC}"
    exit 1
fi

# Start a local web server in the background
echo -e "${YELLOW}[1/4]${NC} Starting local web server..."
cd ..
python3 -m http.server 8888 > /dev/null 2>&1 &
SERVER_PID=$!

# Wait for server to start
sleep 2

if ! curl -s http://localhost:8888 > /dev/null; then
    echo -e "${RED}Failed to start web server${NC}"
    kill $SERVER_PID 2>/dev/null || true
    exit 1
fi

echo -e "${GREEN}✓${NC} Server started (PID: $SERVER_PID)"
echo ""

# Open test suite in browser
echo -e "${YELLOW}[2/4]${NC} Opening test suite in browser..."
echo "URL: http://localhost:8888/tests/integration.test.html"
echo ""

# Detect OS and open browser
if command -v xdg-open > /dev/null; then
    xdg-open "http://localhost:8888/tests/integration.test.html" &
elif command -v open > /dev/null; then
    open "http://localhost:8888/tests/integration.test.html" &
elif command -v start > /dev/null; then
    start "http://localhost:8888/tests/integration.test.html" &
else
    echo -e "${YELLOW}Please open http://localhost:8888/tests/integration.test.html manually${NC}"
fi

echo ""
echo -e "${YELLOW}[3/4]${NC} Test suite loaded in browser"
echo ""
echo "========================================="
echo "INTERACTIVE TESTING"
echo "========================================="
echo ""
echo "The test suite is now running in your browser."
echo ""
echo -e "${GREEN}Actions:${NC}"
echo "  1. Click 'Run All Tests' in the browser"
echo "  2. Wait for all tests to complete"
echo "  3. Review the test summary"
echo ""
echo -e "${GREEN}When finished:${NC}"
echo "  • Press Ctrl+C to stop the server"
echo "  • Or run: kill $SERVER_PID"
echo ""
echo "========================================="
echo ""

# Cleanup function
cleanup() {
    echo ""
    echo -e "${YELLOW}Shutting down server...${NC}"
    kill $SERVER_PID 2>/dev/null || true
    echo -e "${GREEN}Done!${NC}"
    exit 0
}

# Register cleanup on Ctrl+C
trap cleanup INT TERM

# Wait for user to stop
echo -e "${YELLOW}[4/4]${NC} Server running. Press Ctrl+C to stop."
wait $SERVER_PID
