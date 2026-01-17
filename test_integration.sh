#!/bin/bash
# TreeCL Integration Test Script
# Tests various components through the REPL

set -e

echo "=== TreeCL Integration Tests ==="
echo ""

# Test 1: Basic evaluation
echo "Test 1: Integer literals"
echo '42' | cargo run --bin treecl -q 2>/dev/null | head -5
echo ""

# Test 2: List construction  
echo "Test 2: List literals"
echo '(1 2 3)' | cargo run --bin treecl -q 2>/dev/null | head -5
echo ""

# Run unit tests
echo "=== Unit Test Summary ==="
cargo test --lib 2>&1 | tail -5

echo ""
echo "=== All Tests Complete ==="
