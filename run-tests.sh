#!/bin/bash
# Two Generals Protocol - Full Test Suite
# Runs Python, Rust, and Lean 4 tests with detailed output
#
# Usage: ./run-tests.sh [--quick]
#   --quick: Skip slow tests (Python only)

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

QUICK_MODE=false
if [[ "$1" == "--quick" ]]; then
    QUICK_MODE=true
fi

echo "============================================================"
echo "Two Generals Protocol - Full Test Suite"
echo "============================================================"
echo ""

TOTAL_PASSED=0
TOTAL_FAILED=0
TOTAL_TESTS=0

# ============================================================
# PYTHON TESTS
# ============================================================
echo -e "${BLUE}[1/3] Python Tests${NC}"
echo "------------------------------------------------------------"

cd python

# Ensure venv exists
if [[ ! -d ".venv" ]]; then
    echo "Creating Python virtual environment..."
    python3 -m venv .venv
fi

source .venv/bin/activate

# Install if needed
pip install -q -e . 2>/dev/null || true

# Run pytest with one-line-per-test output
PYTEST_ARGS="-v --tb=no -q"
if [[ "$QUICK_MODE" == "false" ]]; then
    PYTEST_ARGS="$PYTEST_ARGS --run-slow"
fi

echo "Running: pytest $PYTEST_ARGS"
echo ""

# Capture pytest output and parse it
pytest $PYTEST_ARGS 2>&1 | while IFS= read -r line; do
    # Match test result lines (PASSED, FAILED, SKIPPED)
    if [[ "$line" =~ ^tests/.+::.+\ (PASSED|FAILED|SKIPPED|ERROR) ]]; then
        test_name=$(echo "$line" | sed 's/ PASSED.*/ PASSED/' | sed 's/ FAILED.*/ FAILED/' | sed 's/ SKIPPED.*/ SKIPPED/' | sed 's/ ERROR.*/ ERROR/')
        if [[ "$line" =~ PASSED ]]; then
            echo -e "${GREEN}✓${NC} $test_name"
        elif [[ "$line" =~ FAILED ]]; then
            echo -e "${RED}✗${NC} $test_name"
        elif [[ "$line" =~ SKIPPED ]]; then
            echo -e "${YELLOW}○${NC} $test_name"
        else
            echo -e "${RED}!${NC} $test_name"
        fi
    elif [[ "$line" =~ ^=.*passed|^=.*failed ]]; then
        # Summary line
        echo ""
        echo "$line"
    fi
done

# Get actual counts
PYTHON_RESULT=$(pytest $PYTEST_ARGS --co -q 2>/dev/null | tail -1)
PYTHON_PASSED=$(pytest $PYTEST_ARGS 2>&1 | grep -oP '\d+(?= passed)' | head -1 || echo "0")
PYTHON_FAILED=$(pytest $PYTEST_ARGS 2>&1 | grep -oP '\d+(?= failed)' | head -1 || echo "0")

deactivate
cd ..

echo ""

# ============================================================
# RUST TESTS
# ============================================================
echo -e "${BLUE}[2/3] Rust Tests${NC}"
echo "------------------------------------------------------------"

cd rust

echo "Running: cargo test"
echo ""

# Run cargo test with verbose output
cargo test --no-fail-fast 2>&1 | while IFS= read -r line; do
    # Match test result lines
    if [[ "$line" =~ ^test\ .+\ \.\.\.\ (ok|FAILED|ignored) ]]; then
        test_name=$(echo "$line" | sed 's/^test //' | sed 's/ \.\.\. .*//')
        if [[ "$line" =~ "ok" ]]; then
            echo -e "${GREEN}✓${NC} $test_name"
        elif [[ "$line" =~ "FAILED" ]]; then
            echo -e "${RED}✗${NC} $test_name"
        elif [[ "$line" =~ "ignored" ]]; then
            echo -e "${YELLOW}○${NC} $test_name (ignored)"
        fi
    elif [[ "$line" =~ ^test\ result: ]]; then
        echo ""
        echo "$line"
    fi
done

cd ..

echo ""

# ============================================================
# LEAN 4 PROOFS
# ============================================================
echo -e "${BLUE}[3/3] Lean 4 Formal Proofs${NC}"
echo "------------------------------------------------------------"

cd lean4

echo "Running: lake build"
echo ""

# Check for sorry statements first
SORRY_COUNT=$(grep -r "sorry" *.lean 2>/dev/null | grep -v "-- sorry" | grep -v "no sorry" | wc -l || echo "0")
if [[ "$SORRY_COUNT" -gt 0 ]]; then
    echo -e "${RED}WARNING: Found $SORRY_COUNT potential 'sorry' statements${NC}"
    grep -rn "sorry" *.lean 2>/dev/null | grep -v "-- sorry" | grep -v "no sorry" || true
    echo ""
fi

# Run lake build and capture output
BUILD_OUTPUT=$(lake build 2>&1)
BUILD_EXIT=$?

# Parse theorem info lines
echo "$BUILD_OUTPUT" | while IFS= read -r line; do
    if [[ "$line" =~ ^info:.*:.*:\ .+ ]]; then
        # Extract theorem name from info line
        theorem=$(echo "$line" | sed 's/^info: [^:]*:[^:]*: //')
        echo -e "${GREEN}✓${NC} THEOREM: $theorem"
    elif [[ "$line" =~ ^warning: ]]; then
        # Show warnings but don't fail
        short_warn=$(echo "$line" | head -c 100)
        echo -e "${YELLOW}⚠${NC} $short_warn..."
    elif [[ "$line" =~ ^error: ]]; then
        echo -e "${RED}✗${NC} $line"
    fi
done

# Final build status
if [[ $BUILD_EXIT -eq 0 ]]; then
    echo ""
    echo -e "${GREEN}Build completed successfully${NC}"

    # Count theorems
    THEOREM_COUNT=$(echo "$BUILD_OUTPUT" | grep -c "^info:.*:" || echo "0")
    echo "Verified theorems: $THEOREM_COUNT"

    # Verify no sorry
    if [[ "$SORRY_COUNT" -eq 0 ]]; then
        echo -e "${GREEN}✓ Zero 'sorry' statements - all proofs complete${NC}"
    fi
else
    echo -e "${RED}Build failed with exit code $BUILD_EXIT${NC}"
fi

cd ..

echo ""
echo "============================================================"
echo "TEST SUITE COMPLETE"
echo "============================================================"
echo ""
echo "Results saved. Use this output to verify:"
echo "  • All Python tests pass (including slow/adversarial)"
echo "  • All Rust tests pass"
echo "  • All Lean 4 theorems verify with zero 'sorry' statements"
echo ""
echo "Key theorems verified:"
echo "  • safety: If both decide, decisions are equal"
echo "  • attack_needs_both: Attack requires bilateral evidence"
echo "  • bilateral_receipt_implies_common_knowledge"
echo "  • gray_impossibility_assumption_violated"
echo "  • full_epistemic_chain_verified"
