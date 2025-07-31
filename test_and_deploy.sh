#!/bin/bash

# CertifyEdge Test and Deploy Script
# This script runs comprehensive tests and provides deployment guidance

set -euo pipefail

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

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

# Check if we're on Windows
if [[ "$OSTYPE" == "msys" || "$OSTYPE" == "cygwin" ]]; then
    log_warning "Running on Windows - some tests may need adjustment"
    # Use Windows-compatible commands
    TEST_RUNNER="tests/run_comprehensive_tests.sh"
else
    TEST_RUNNER="tests/run_comprehensive_tests.sh"
fi

# Main execution
main() {
    log_info "🚀 CertifyEdge Test and Deploy Script"
    log_info "Timestamp: $(date)"
    
    echo ""
    log_info "📋 Step 1: Running Comprehensive Test Suite"
    echo "This will take approximately 4-6 hours to complete all tests."
    echo ""
    
    # Check if test runner exists
    if [[ ! -f "$TEST_RUNNER" ]]; then
        log_error "Test runner not found: $TEST_RUNNER"
        exit 1
    fi
    
    # Run comprehensive tests
    if ./tests/run_comprehensive_tests.sh; then
        log_success "✅ All tests passed!"
    else
        log_error "❌ Some tests failed. Please review the test report and fix issues before deployment."
        echo ""
        log_info "📊 Test Report Location: test_report_$(date +%Y%m%d_%H%M%S).md"
        exit 1
    fi
    
    echo ""
    log_info "📋 Step 2: Deployment Readiness Check"
    echo ""
    
    # Check deployment readiness checklist
    if [[ -f "tests/deployment-readiness-checklist.md" ]]; then
        log_info "📋 Please complete the deployment readiness checklist:"
        echo "   File: tests/deployment-readiness-checklist.md"
        echo ""
        log_info "🔍 Key areas to verify:"
        echo "   - Security testing completed"
        echo "   - Code coverage ≥95%"
        echo "   - Performance benchmarks met"
        echo "   - Grid-in-loop tests successful"
        echo "   - End-to-end pipeline verified"
        echo "   - Infrastructure ready"
        echo "   - Compliance requirements satisfied"
        echo ""
    fi
    
    log_info "📋 Step 3: Deployment Commands"
    echo ""
    log_info "🚀 When ready to deploy, use these commands:"
    echo ""
    echo "   # Build all targets"
    echo "   bazel build --config=ci //... --build_tag_filters=release"
    echo ""
    echo "   # Deploy to Kubernetes"
    echo "   kubectl apply -f infrastructure/kubernetes/"
    echo ""
    echo "   # Verify deployment"
    echo "   kubectl get pods -A"
    echo "   kubectl get services -A"
    echo ""
    echo "   # Health check"
    echo "   curl -f https://your-deployment-url/health"
    echo ""
    
    log_info "📋 Step 4: Post-Deployment Verification"
    echo ""
    log_info "🔍 After deployment, verify:"
    echo "   - All services are running"
    echo "   - Health checks are passing"
    echo "   - Performance is within SLA"
    echo "   - Monitoring is working"
    echo "   - Alerts are configured"
    echo ""
    
    log_success "🎉 CertifyEdge is ready for deployment!"
    echo ""
    log_info "📚 Additional Resources:"
    echo "   - Test Documentation: tests/README.md"
    echo "   - Architecture Docs: docs/architecture/"
    echo "   - API Documentation: docs/api/"
    echo "   - Deployment Guide: docs/deployment/"
    echo ""
    
    log_info "⚠️  Important Notes:"
    echo "   - All tests must pass before deployment"
    echo "   - Complete the deployment readiness checklist"
    echo "   - Get stakeholder approval"
    echo "   - Have rollback plan ready"
    echo "   - Monitor deployment closely"
    echo ""
}

# Handle script interruption
trap 'log_error "Script interrupted"; exit 1' INT TERM

# Run main function
main "$@" 