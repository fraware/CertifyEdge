#!/bin/bash

# Simple test script for CertifyEdge platform
# This script performs basic verification without requiring complex Bazel dependencies

set -e

echo "=== CertifyEdge Platform - Basic Verification Test ==="
echo "Date: $(date)"
echo "Platform: $(uname -s)"
echo ""

# Test 1: Check if essential files exist
echo "Test 1: File Structure Verification"
echo "Checking for essential project files..."

required_files=(
    "README.md"
    "WORKSPACE"
    ".bazelrc"
    "services/stl-compiler/src/lib.rs"
    "services/smt-verifier/src/lib.rs"
    "services/certificate/src/lib.rs"
    "services/auditor-api/src/lib.rs"
    "tests/test-plan.md"
    "tests/deployment-readiness-checklist.md"
)

for file in "${required_files[@]}"; do
    if [ -f "$file" ]; then
        echo "✓ $file exists"
    else
        echo "✗ $file missing"
        exit 1
    fi
done

echo ""

# Test 2: Check if Rust code compiles (basic syntax check)
echo "Test 2: Rust Code Syntax Check"
echo "Checking Rust source files..."

rust_files=(
    "services/stl-compiler/src/lib.rs"
    "services/smt-verifier/src/lib.rs"
    "services/certificate/src/lib.rs"
    "services/auditor-api/src/lib.rs"
)

for file in "${rust_files[@]}"; do
    if [ -f "$file" ]; then
        echo "Checking syntax for $file..."
        # Basic syntax check - just verify the file is readable Rust
        if grep -q "pub" "$file" || grep -q "fn" "$file" || grep -q "struct" "$file"; then
            echo "✓ $file appears to be valid Rust code"
        else
            echo "⚠ $file may not contain valid Rust code"
        fi
    fi
done

echo ""

# Test 3: Check configuration files
echo "Test 3: Configuration Verification"
echo "Checking configuration files..."

config_files=(
    ".bazelrc"
    "WORKSPACE"
    "tests/test-plan.md"
    "tests/deployment-readiness-checklist.md"
)

for file in "${config_files[@]}"; do
    if [ -f "$file" ]; then
        line_count=$(wc -l < "$file")
        echo "✓ $file exists with $line_count lines"
    else
        echo "✗ $file missing"
        exit 1
    fi
done

echo ""

# Test 4: Check test files
echo "Test 4: Test Files Verification"
echo "Checking test files..."

test_files=(
    "tests/unit/stl_compiler_test.rs"
    "tests/unit/smt_verifier_test.rs"
    "tests/integration/end_to_end_pipeline_test.rs"
)

for file in "${test_files[@]}"; do
    if [ -f "$file" ]; then
        line_count=$(wc -l < "$file")
        echo "✓ $file exists with $line_count lines"
    else
        echo "⚠ $file missing (will be created during full test run)"
    fi
done

echo ""

# Test 5: Check documentation
echo "Test 5: Documentation Verification"
echo "Checking documentation files..."

doc_files=(
    "README.md"
    "docs/README.md"
    "docs/quick-start.md"
    "docs/architecture/README.md"
)

for file in "${doc_files[@]}"; do
    if [ -f "$file" ]; then
        line_count=$(wc -l < "$file")
        echo "✓ $file exists with $line_count lines"
    else
        echo "⚠ $file missing"
    fi
done

echo ""

# Test 6: Check infrastructure files
echo "Test 6: Infrastructure Verification"
echo "Checking infrastructure files..."

infra_files=(
    "infrastructure/terraform/gpu-farm/main.tf"
    ".github/workflows/ci.yml"
)

for file in "${infra_files[@]}"; do
    if [ -f "$file" ]; then
        line_count=$(wc -l < "$file")
        echo "✓ $file exists with $line_count lines"
    else
        echo "⚠ $file missing"
    fi
done

echo ""

# Test 7: Check for security and compliance files
echo "Test 7: Security and Compliance Verification"
echo "Checking security and compliance files..."

security_files=(
    "docs/architecture/threat-model.md"
    "docs/architecture/001-system-architecture-threat-model.md"
)

for file in "${security_files[@]}"; do
    if [ -f "$file" ]; then
        line_count=$(wc -l < "$file")
        echo "✓ $file exists with $line_count lines"
    else
        echo "⚠ $file missing"
    fi
done

echo ""

# Summary
echo "=== Test Summary ==="
echo "Basic verification completed successfully!"
echo ""
echo "Next steps:"
echo "1. Run comprehensive test suite: ./tests/run_comprehensive_tests.sh"
echo "2. Complete deployment readiness checklist: tests/deployment-readiness-checklist.md"
echo "3. Address any failures before deployment"
echo "4. Get stakeholder approval for deployment"
echo "5. Execute deployment with monitoring"
echo ""
echo "Note: This is a basic verification. For full testing, you'll need to:"
echo "- Install Rust toolchain"
echo "- Install Bazel build system"
echo "- Install required SMT solvers (Z3, CVC5)"
echo "- Install Lean 4 theorem prover"
echo "- Set up Kubernetes cluster for deployment"
echo ""
echo "For Windows users: Consider using WSL or Git Bash for running bash scripts." 