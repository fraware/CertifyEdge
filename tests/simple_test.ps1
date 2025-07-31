# Simple test script for CertifyEdge platform

Write-Host "=== CertifyEdge Platform - Basic Verification Test ===" -ForegroundColor Green
Write-Host "Date: $(Get-Date)" -ForegroundColor Yellow
Write-Host ""

# Test 1: Check if essential files exist
Write-Host "Test 1: File Structure Verification" -ForegroundColor Cyan

$required_files = @("README.md", "WORKSPACE", ".bazelrc", "tests/test-plan.md", "tests/deployment-readiness-checklist.md")

foreach ($file in $required_files) {
    if (Test-Path $file) {
        Write-Host "✓ $file exists" -ForegroundColor Green
    } else {
        Write-Host "✗ $file missing" -ForegroundColor Red
    }
}

Write-Host ""

# Test 2: Check Rust services
Write-Host "Test 2: Rust Services Verification" -ForegroundColor Cyan

$rust_services = @("services/stl-compiler/src/lib.rs", "services/smt-verifier/src/lib.rs", "services/certificate/src/lib.rs", "services/auditor-api/src/lib.rs")

foreach ($file in $rust_services) {
    if (Test-Path $file) {
        $line_count = (Get-Content $file).Count
        Write-Host "✓ $file exists with $line_count lines" -ForegroundColor Green
    } else {
        Write-Host "⚠ $file missing" -ForegroundColor Yellow
    }
}

Write-Host ""

# Test 3: Check test files
Write-Host "Test 3: Test Files Verification" -ForegroundColor Cyan

$test_files = @("tests/unit/stl_compiler_test.rs", "tests/unit/smt_verifier_test.rs", "tests/integration/end_to_end_pipeline_test.rs")

foreach ($file in $test_files) {
    if (Test-Path $file) {
        $line_count = (Get-Content $file).Count
        Write-Host "✓ $file exists with $line_count lines" -ForegroundColor Green
    } else {
        Write-Host "⚠ $file missing (will be created during full test run)" -ForegroundColor Yellow
    }
}

Write-Host ""

# Test 4: Check documentation
Write-Host "Test 4: Documentation Verification" -ForegroundColor Cyan

$doc_files = @("README.md", "docs/README.md", "docs/quick-start.md")

foreach ($file in $doc_files) {
    if (Test-Path $file) {
        $line_count = (Get-Content $file).Count
        Write-Host "✓ $file exists with $line_count lines" -ForegroundColor Green
    } else {
        Write-Host "⚠ $file missing" -ForegroundColor Yellow
    }
}

Write-Host ""

# Summary
Write-Host "=== Test Summary ===" -ForegroundColor Green
Write-Host "Basic verification completed!" -ForegroundColor Green
Write-Host ""
Write-Host "Next steps:" -ForegroundColor Cyan
Write-Host "1. Complete deployment readiness checklist: tests/deployment-readiness-checklist.md" -ForegroundColor White
Write-Host "2. Address any failures before deployment" -ForegroundColor White
Write-Host "3. Get stakeholder approval for deployment" -ForegroundColor White
Write-Host "4. Execute deployment with monitoring" -ForegroundColor White
Write-Host ""
Write-Host "Note: For full testing, you'll need to install:" -ForegroundColor Yellow
Write-Host "- Rust toolchain" -ForegroundColor White
Write-Host "- Bazel build system" -ForegroundColor White
Write-Host "- SMT solvers (Z3, CVC5)" -ForegroundColor White
Write-Host "- Lean 4 theorem prover" -ForegroundColor White
Write-Host "- Kubernetes cluster" -ForegroundColor White 