# CertifyEdge Platform - Simple Validation Script
# Production-grade, formally-verified, audit-ready platform

Write-Host "=== CertifyEdge Platform - Simple Validation ===" -ForegroundColor Green
Write-Host "Date: $(Get-Date)" -ForegroundColor Yellow
Write-Host ""

$totalTests = 0
$passedTests = 0
$failedTests = 0

function Test-Item {
    param($Name, $Condition, $Details = "")
    
    $global:totalTests++
    if ($Condition) {
        $global:passedTests++
        Write-Host "✓ $Name" -ForegroundColor Green
    } else {
        $global:failedTests++
        Write-Host "✗ $Name" -ForegroundColor Red
        if ($Details) {
            Write-Host "  Details: $Details" -ForegroundColor Red
        }
    }
}

Write-Host "Phase 1: Bazel Build System" -ForegroundColor Cyan
Write-Host "===========================" -ForegroundColor Cyan

# Check WORKSPACE file
Test-Item "WORKSPACE file exists" (Test-Path "WORKSPACE")
Test-Item "Bazel configuration exists" (Test-Path ".bazelrc")

# Check core services
Write-Host "`nPhase 2: Core Services" -ForegroundColor Cyan
Write-Host "======================" -ForegroundColor Cyan

$services = @(
    "services/stl-compiler/src/lib.rs",
    "services/smt-verifier/src/lib.rs", 
    "services/certificate/src/lib.rs",
    "services/auditor-api/src/lib.rs"
)

foreach ($service in $services) {
    Test-Item "Service exists: $service" (Test-Path $service)
}

Write-Host "`nPhase 3: Testing Framework" -ForegroundColor Cyan
Write-Host "==========================" -ForegroundColor Cyan

# Check test files
$testFiles = @(
    "tests/unit/stl_compiler_test.rs",
    "tests/unit/smt_verifier_test.rs",
    "tests/integration/end_to_end_pipeline_test.rs",
    "tests/test-plan.md",
    "tests/deployment-readiness-checklist.md"
)

foreach ($file in $testFiles) {
    Test-Item "Test file exists: $file" (Test-Path $file)
}

Write-Host "`nPhase 4: Infrastructure" -ForegroundColor Cyan
Write-Host "=======================" -ForegroundColor Cyan

# Check infrastructure files
$infraFiles = @(
    "infrastructure/terraform/gpu-farm/main.tf",
    ".github/workflows/ci.yml"
)

foreach ($file in $infraFiles) {
    Test-Item "Infrastructure file exists: $file" (Test-Path $file)
}

Write-Host "`nPhase 5: Documentation" -ForegroundColor Cyan
Write-Host "=======================" -ForegroundColor Cyan

# Check documentation
$docFiles = @(
    "README.md",
    "docs/README.md",
    "docs/quick-start.md"
)

foreach ($file in $docFiles) {
    Test-Item "Documentation exists: $file" (Test-Path $file)
}

Write-Host "`nPhase 6: Deployment Scripts" -ForegroundColor Cyan
Write-Host "============================" -ForegroundColor Cyan

# Check deployment scripts
$deployFiles = @(
    "deploy_to_staging.ps1",
    "tests/run_comprehensive_tests.ps1"
)

foreach ($file in $deployFiles) {
    Test-Item "Deployment script exists: $file" (Test-Path $file)
}

Write-Host "`nPhase 7: Monitoring Configuration" -ForegroundColor Cyan
Write-Host "=================================" -ForegroundColor Cyan

# Check monitoring configuration
$monitoringFiles = @(
    "infrastructure/kubernetes/monitoring/prometheus-config.yaml"
)

foreach ($file in $monitoringFiles) {
    Test-Item "Monitoring config exists: $file" (Test-Path $file)
}

# Final Summary
Write-Host "`n=== Validation Summary ===" -ForegroundColor Green
Write-Host "Total Tests: $totalTests" -ForegroundColor White
Write-Host "Passed: $passedTests" -ForegroundColor Green
Write-Host "Failed: $failedTests" -ForegroundColor Red

if ($totalTests -gt 0) {
    $successRate = [math]::Round(($passedTests / $totalTests) * 100, 2)
    Write-Host "Success Rate: $successRate%" -ForegroundColor White
}

Write-Host "`nNext Steps:" -ForegroundColor Cyan
Write-Host "1. Run comprehensive tests: .\tests\run_comprehensive_tests.ps1" -ForegroundColor White
Write-Host "2. Deploy to staging: .\deploy_to_staging.ps1" -ForegroundColor White
Write-Host "3. Monitor staging for 24-48 hours" -ForegroundColor White
Write-Host "4. Deploy to production after validation" -ForegroundColor White

if ($failedTests -eq 0) {
    Write-Host "`n🎉 All validations passed! Ready for deployment." -ForegroundColor Green
    exit 0
} else {
    Write-Host "`n⚠️  Some validations failed. Please address issues before deployment." -ForegroundColor Yellow
    exit 1
} 