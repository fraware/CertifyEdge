#!/bin/bash

# CertifyEdge Comprehensive Test Runner
# This script runs all tests in the proper order before deployment

set -euo pipefail

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Test results tracking
TOTAL_TESTS=0
PASSED_TESTS=0
FAILED_TESTS=0
SKIPPED_TESTS=0

# Logging functions
log_info() {
    echo -e "${BLUE}[INFO]${NC} $1"
}

log_success() {
    echo -e "${GREEN}[SUCCESS]${NC} $1"
}

log_warning() {
    echo -e "${YELLOW}[WARNING]${NC} $1"
}

log_error() {
    echo -e "${RED}[ERROR]${NC} $1"
}

# Test execution function
run_test_suite() {
    local suite_name="$1"
    local test_command="$2"
    local timeout_seconds="${3:-300}"
    
    log_info "Running $suite_name tests..."
    
    TOTAL_TESTS=$((TOTAL_TESTS + 1))
    
    if timeout $timeout_seconds bash -c "$test_command"; then
        log_success "$suite_name tests passed"
        PASSED_TESTS=$((PASSED_TESTS + 1))
        return 0
    else
        log_error "$suite_name tests failed"
        FAILED_TESTS=$((FAILED_TESTS + 1))
        return 1
    fi
}

# Check prerequisites
check_prerequisites() {
    log_info "Checking prerequisites..."
    
    # Check if Bazel is available
    if ! command -v bazel &> /dev/null; then
        log_error "Bazel is not installed or not in PATH"
        exit 1
    fi
    
    # Check if Rust is available
    if ! command -v cargo &> /dev/null; then
        log_error "Rust/Cargo is not installed or not in PATH"
        exit 1
    fi
    
    # Check if Node.js is available
    if ! command -v node &> /dev/null; then
        log_error "Node.js is not installed or not in PATH"
        exit 1
    fi
    
    # Check if Lean 4 is available
    if ! command -v lean &> /dev/null; then
        log_warning "Lean 4 is not installed - some tests may be skipped"
    fi
    
    log_success "Prerequisites check completed"
}

# Phase 1: Security and Quality Gates
run_security_tests() {
    log_info "=== Phase 1: Security and Quality Gates ==="
    
    # Security scanning
    run_test_suite "Security Scanning" \
        "bazel test --config=ci //... --test_tag_filters=security" 600
    
    # Static analysis
    run_test_suite "Static Analysis" \
        "bazel build --config=ci //... --aspects @rules_clippy//clippy:defs.bzl%clippy_aspect" 300
    
    # Code coverage
    run_test_suite "Code Coverage" \
        "bazel coverage --config=ci //... --combined_report=lcov" 900
    
    # Mutation testing
    run_test_suite "Mutation Testing" \
        "bazel test --config=ci //... --test_tag_filters=mutagen" 600
    
    # Documentation validation
    run_test_suite "Documentation Validation" \
        "bazel test --config=ci //docs/... --test_tag_filters=linkchecker,vale" 300
}

# Phase 2: Functional Testing
run_functional_tests() {
    log_info "=== Phase 2: Functional Testing ==="
    
    # Unit tests
    run_test_suite "Unit Tests" \
        "bazel test --config=ci //... --test_tag_filters=unit" 1200
    
    # Integration tests
    run_test_suite "Integration Tests" \
        "bazel test --config=ci //... --test_tag_filters=integration" 1800
    
    # Property-based tests
    run_test_suite "Property-Based Tests" \
        "bazel test --config=ci //... --test_tag_filters=property" 900
    
    # Formal verification tests
    run_test_suite "Formal Verification Tests" \
        "bazel test --config=ci //... --test_tag_filters=formal" 600
    
    # Contract tests
    run_test_suite "Contract Tests" \
        "bazel test --config=ci //... --test_tag_filters=contract" 600
    
    # Differential tests
    run_test_suite "Differential Tests" \
        "bazel test --config=ci //... --test_tag_filters=differential" 900
}

# Phase 3: Performance Testing
run_performance_tests() {
    log_info "=== Phase 3: Performance Testing ==="
    
    # Performance benchmarks
    run_test_suite "Performance Benchmarks" \
        "bazel test --config=ci //... --test_tag_filters=benchmark" 600
    
    # Load testing
    run_test_suite "Load Testing" \
        "bazel test --config=ci //... --test_tag_filters=load" 900
    
    # Stress testing
    run_test_suite "Stress Testing" \
        "bazel test --config=ci //... --test_tag_filters=stress" 600
    
    # Performance regression detection
    run_test_suite "Performance Regression Detection" \
        "bazel test --config=ci //... --test_tag_filters=performance" 600
}

# Phase 4: Grid-in-Loop Testing
run_grid_in_loop_tests() {
    log_info "=== Phase 4: Grid-in-Loop Testing ==="
    
    # GridLAB-D tests
    run_test_suite "GridLAB-D Tests" \
        "bazel test --config=ci //tests/grid-in-loop/gridlab-d/..." 1800
    
    # OpenDSS tests
    run_test_suite "OpenDSS Tests" \
        "bazel test --config=ci //tests/grid-in-loop/opendss/..." 1800
    
    # PowerFactory tests
    run_test_suite "PowerFactory Tests" \
        "bazel test --config=ci //tests/grid-in-loop/powerfactory/..." 1800
    
    # Monte Carlo tests
    run_test_suite "Monte Carlo Tests" \
        "bazel test --config=ci //tests/grid-in-loop/monte-carlo/..." 2400
}

# Phase 5: End-to-End Testing
run_e2e_tests() {
    log_info "=== Phase 5: End-to-End Testing ==="
    
    # Complete pipeline tests
    run_test_suite "Complete Pipeline Tests" \
        "bazel test --config=ci //tests/e2e/pipeline/..." 1800
    
    # GPU farm tests
    run_test_suite "GPU Farm Tests" \
        "bazel test --config=ci //tests/e2e/gpu-farm/..." 1200
    
    # Certificate lifecycle tests
    run_test_suite "Certificate Lifecycle Tests" \
        "bazel test --config=ci //tests/e2e/certificate/..." 900
    
    # Audit trail tests
    run_test_suite "Audit Trail Tests" \
        "bazel test --config=ci //tests/e2e/audit/..." 600
}

# Phase 6: Security and Compliance
run_security_compliance_tests() {
    log_info "=== Phase 6: Security and Compliance ==="
    
    # OWASP threat dragon validation
    run_test_suite "OWASP Threat Dragon Validation" \
        "bazel test --config=ci //security/threat-dragon/..." 600
    
    # Internal security review
    run_test_suite "Internal Security Review" \
        "bazel test --config=ci //security/internal-review/..." 600
    
    # Compliance tests
    run_test_suite "Compliance Tests" \
        "bazel test --config=ci //tests/compliance/..." 900
    
    # Cryptographic tests
    run_test_suite "Cryptographic Tests" \
        "bazel test --config=ci //tests/security/crypto/..." 600
}

# Generate test report
generate_report() {
    log_info "=== Generating Test Report ==="
    
    local report_file="test_report_$(date +%Y%m%d_%H%M%S).md"
    
    cat > "$report_file" << EOF
# CertifyEdge Test Report
Generated: $(date)

## Test Summary
- Total Test Suites: $TOTAL_TESTS
- Passed: $PASSED_TESTS
- Failed: $FAILED_TESTS
- Skipped: $SKIPPED_TESTS
- Success Rate: $((PASSED_TESTS * 100 / TOTAL_TESTS))%

## Test Results by Phase

### Phase 1: Security and Quality Gates
- Security Scanning: $(if [ $FAILED_TESTS -eq 0 ]; then echo "✅ PASSED"; else echo "❌ FAILED"; fi)
- Static Analysis: $(if [ $FAILED_TESTS -eq 0 ]; then echo "✅ PASSED"; else echo "❌ FAILED"; fi)
- Code Coverage: $(if [ $FAILED_TESTS -eq 0 ]; then echo "✅ PASSED"; else echo "❌ FAILED"; fi)
- Mutation Testing: $(if [ $FAILED_TESTS -eq 0 ]; then echo "✅ PASSED"; else echo "❌ FAILED"; fi)
- Documentation Validation: $(if [ $FAILED_TESTS -eq 0 ]; then echo "✅ PASSED"; else echo "❌ FAILED"; fi)

### Phase 2: Functional Testing
- Unit Tests: $(if [ $FAILED_TESTS -eq 0 ]; then echo "✅ PASSED"; else echo "❌ FAILED"; fi)
- Integration Tests: $(if [ $FAILED_TESTS -eq 0 ]; then echo "✅ PASSED"; else echo "❌ FAILED"; fi)
- Property-Based Tests: $(if [ $FAILED_TESTS -eq 0 ]; then echo "✅ PASSED"; else echo "❌ FAILED"; fi)
- Formal Verification Tests: $(if [ $FAILED_TESTS -eq 0 ]; then echo "✅ PASSED"; else echo "❌ FAILED"; fi)
- Contract Tests: $(if [ $FAILED_TESTS -eq 0 ]; then echo "✅ PASSED"; else echo "❌ FAILED"; fi)
- Differential Tests: $(if [ $FAILED_TESTS -eq 0 ]; then echo "✅ PASSED"; else echo "❌ FAILED"; fi)

### Phase 3: Performance Testing
- Performance Benchmarks: $(if [ $FAILED_TESTS -eq 0 ]; then echo "✅ PASSED"; else echo "❌ FAILED"; fi)
- Load Testing: $(if [ $FAILED_TESTS -eq 0 ]; then echo "✅ PASSED"; else echo "❌ FAILED"; fi)
- Stress Testing: $(if [ $FAILED_TESTS -eq 0 ]; then echo "✅ PASSED"; else echo "❌ FAILED"; fi)
- Performance Regression Detection: $(if [ $FAILED_TESTS -eq 0 ]; then echo "✅ PASSED"; else echo "❌ FAILED"; fi)

### Phase 4: Grid-in-Loop Testing
- GridLAB-D Tests: $(if [ $FAILED_TESTS -eq 0 ]; then echo "✅ PASSED"; else echo "❌ FAILED"; fi)
- OpenDSS Tests: $(if [ $FAILED_TESTS -eq 0 ]; then echo "✅ PASSED"; else echo "❌ FAILED"; fi)
- PowerFactory Tests: $(if [ $FAILED_TESTS -eq 0 ]; then echo "✅ PASSED"; else echo "❌ FAILED"; fi)
- Monte Carlo Tests: $(if [ $FAILED_TESTS -eq 0 ]; then echo "✅ PASSED"; else echo "❌ FAILED"; fi)

### Phase 5: End-to-End Testing
- Complete Pipeline Tests: $(if [ $FAILED_TESTS -eq 0 ]; then echo "✅ PASSED"; else echo "❌ FAILED"; fi)
- GPU Farm Tests: $(if [ $FAILED_TESTS -eq 0 ]; then echo "✅ PASSED"; else echo "❌ FAILED"; fi)
- Certificate Lifecycle Tests: $(if [ $FAILED_TESTS -eq 0 ]; then echo "✅ PASSED"; else echo "❌ FAILED"; fi)
- Audit Trail Tests: $(if [ $FAILED_TESTS -eq 0 ]; then echo "✅ PASSED"; else echo "❌ FAILED"; fi)

### Phase 6: Security and Compliance
- OWASP Threat Dragon Validation: $(if [ $FAILED_TESTS -eq 0 ]; then echo "✅ PASSED"; else echo "❌ FAILED"; fi)
- Internal Security Review: $(if [ $FAILED_TESTS -eq 0 ]; then echo "✅ PASSED"; else echo "❌ FAILED"; fi)
- Compliance Tests: $(if [ $FAILED_TESTS -eq 0 ]; then echo "✅ PASSED"; else echo "❌ FAILED"; fi)
- Cryptographic Tests: $(if [ $FAILED_TESTS -eq 0 ]; then echo "✅ PASSED"; else echo "❌ FAILED"; fi)

## Deployment Readiness
$(if [ $FAILED_TESTS -eq 0 ]; then echo "✅ READY FOR DEPLOYMENT"; else echo "❌ NOT READY FOR DEPLOYMENT"; fi)

## Recommendations
$(if [ $FAILED_TESTS -gt 0 ]; then echo "- Fix failing tests before deployment"; else echo "- All tests passed - proceed with deployment"; fi)
$(if [ $PASSED_TESTS -lt $TOTAL_TESTS ]; then echo "- Review skipped tests"; else echo "- All test suites executed successfully"; fi)

## Next Steps
1. Review test results
2. Address any failures
3. Run deployment tests
4. Monitor production deployment
EOF

    log_success "Test report generated: $report_file"
}

# Main execution
main() {
    log_info "Starting CertifyEdge Comprehensive Test Suite"
    log_info "Timestamp: $(date)"
    
    # Check prerequisites
    check_prerequisites
    
    # Run all test phases
    run_security_tests
    run_functional_tests
    run_performance_tests
    run_grid_in_loop_tests
    run_e2e_tests
    run_security_compliance_tests
    
    # Generate final report
    generate_report
    
    # Final summary
    log_info "=== Test Execution Complete ==="
    log_info "Total Test Suites: $TOTAL_TESTS"
    log_info "Passed: $PASSED_TESTS"
    log_info "Failed: $FAILED_TESTS"
    log_info "Skipped: $SKIPPED_TESTS"
    
    if [ $FAILED_TESTS -eq 0 ]; then
        log_success "All tests passed! Ready for deployment."
        exit 0
    else
        log_error "$FAILED_TESTS test suite(s) failed. Please fix before deployment."
        exit 1
    fi
}

# Handle script interruption
trap 'log_error "Test execution interrupted"; exit 1' INT TERM

# Run main function
main "$@" 