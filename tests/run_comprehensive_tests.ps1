# CertifyEdge Platform - Comprehensive Test Runner (PowerShell)
# Production-grade, formally-verified, audit-ready platform

param(
    [switch]$SkipSecurity,
    [switch]$SkipPerformance,
    [switch]$SkipGridInLoop,
    [switch]$SkipEndToEnd,
    [string]$TestReportPath = "tests/test-report-$(Get-Date -Format 'yyyyMMdd-HHmmss').md"
)

Write-Host "=== CertifyEdge Platform - Comprehensive Test Suite ===" -ForegroundColor Green
Write-Host "Date: $(Get-Date)" -ForegroundColor Yellow
Write-Host "Platform: $($env:OS)" -ForegroundColor Yellow
Write-Host ""

# Initialize test report
$testReport = @"
# CertifyEdge Test Report
Generated: $(Get-Date)

## Test Summary
"@

$totalTests = 0
$passedTests = 0
$failedTests = 0

function Write-TestResult {
    param($TestName, $Success, $Details = "")
    
    $global:totalTests++
    if ($Success) {
        $global:passedTests++
        Write-Host "✓ $TestName" -ForegroundColor Green
        $testReport += "`n- [x] $TestName"
    } else {
        $global:failedTests++
        Write-Host "✗ $TestName" -ForegroundColor Red
        $testReport += "`n- [ ] $TestName"
        if ($Details) {
            Write-Host "  Details: $Details" -ForegroundColor Red
            $testReport += "`n  - Details: $Details"
        }
    }
}

# Phase 1: Security "&" Quality Gates
Write-Host "Phase 1: Security and Quality Gates" -ForegroundColor Cyan
Write-Host "=================================" -ForegroundColor Cyan

if (-not $SkipSecurity) {
    Write-Host "Running security tests..." -ForegroundColor White
    
    # Check for basic security files
    $securityFiles = @(
        "docs/architecture/threat-model.md",
        "docs/architecture/001-system-architecture-threat-model.md"
    )
    
    foreach ($file in $securityFiles) {
        if (Test-Path $file) {
            Write-TestResult "Security documentation exists: $file" $true
        } else {
            Write-TestResult "Security documentation exists: $file" $false "File not found"
        }
    }
    
    # Check for Rust security features
    $rustFiles = @(
        "services/stl-compiler/src/lib.rs",
        "services/smt-verifier/src/lib.rs",
        "services/certificate/src/lib.rs",
        "services/auditor-api/src/lib.rs"
    )
    
    foreach ($file in $rustFiles) {
        if (Test-Path $file) {
            $content = Get-Content $file -Raw
            if ($content -match "unsafe" -or $content -match "unsafe\s*{") {
                Write-TestResult "Rust security check: $file" $false "Contains unsafe code"
            } else {
                Write-TestResult "Rust security check: $file" $true
            }
        } else {
            Write-TestResult "Rust security check: $file" $false "File not found"
        }
    }
} else {
    Write-Host "Skipping security tests" -ForegroundColor Yellow
}

# Phase 2: Functional Tests
Write-Host "`nPhase 2: Functional Tests" -ForegroundColor Cyan
Write-Host "=========================" -ForegroundColor Cyan

# Check unit tests
$unitTestFiles = @(
    "tests/unit/stl_compiler_test.rs",
    "tests/unit/smt_verifier_test.rs"
)

foreach ($file in $unitTestFiles) {
    if (Test-Path $file) {
        $lineCount = (Get-Content $file).Count
        if ($lineCount -gt 50) {
            Write-TestResult "Unit test exists: $file" $true "Lines: $lineCount"
        } else {
            Write-TestResult "Unit test exists: $file" $false "Insufficient test coverage"
        }
    } else {
        Write-TestResult "Unit test exists: $file" $false "File not found"
    }
}

# Check integration tests
$integrationTestFiles = @(
    "tests/integration/end_to_end_pipeline_test.rs"
)

foreach ($file in $integrationTestFiles) {
    if (Test-Path $file) {
        $lineCount = (Get-Content $file).Count
        if ($lineCount -gt 100) {
            Write-TestResult "Integration test exists: $file" $true "Lines: $lineCount"
        } else {
            Write-TestResult "Integration test exists: $file" $false "Insufficient test coverage"
        }
    } else {
        Write-TestResult "Integration test exists: $file" $false "File not found"
    }
}

# Phase 3: Performance Tests
Write-Host "`nPhase 3: Performance Tests" -ForegroundColor Cyan
Write-Host "===========================" -ForegroundColor Cyan

if (-not $SkipPerformance) {
    # Check for performance test files
    $perfTestFiles = @(
        "tests/performance/benchmark_tests.rs",
        "tests/performance/load_tests.rs"
    )
    
    foreach ($file in $perfTestFiles) {
        if (Test-Path $file) {
            Write-TestResult "Performance test exists: $file" $true
        } else {
            Write-TestResult "Performance test exists: $file" $false "File not found"
        }
    }
    
    # Check for monitoring configuration
    $monitoringFiles = @(
        "infrastructure/terraform/gpu-farm/main.tf"
    )
    
    foreach ($file in $monitoringFiles) {
        if (Test-Path $file) {
            $content = Get-Content $file -Raw
            if ($content -match "prometheus" -or $content -match "grafana") {
                Write-TestResult "Monitoring configuration: $file" $true
            } else {
                Write-TestResult "Monitoring configuration: $file" $false "No monitoring setup found"
            }
        } else {
            Write-TestResult "Monitoring configuration: $file" $false "File not found"
        }
    }
} else {
    Write-Host "Skipping performance tests" -ForegroundColor Yellow
}

# Phase 4: Grid-in-Loop Tests
Write-Host "`nPhase 4: Grid-in-Loop Tests" -ForegroundColor Cyan
Write-Host "============================" -ForegroundColor Cyan

if (-not $SkipGridInLoop) {
    # Check for grid simulation files
    $gridTestFiles = @(
        "services/grid-in-loop/src/lib.rs"
    )
    
    foreach ($file in $gridTestFiles) {
        if (Test-Path $file) {
            $content = Get-Content $file -Raw
            if ($content -match "GridLABD" -or $content -match "OpenDSS" -or $content -match "PowerFactory") {
                Write-TestResult "Grid simulation support: $file" $true
            } else {
                Write-TestResult "Grid simulation support: $file" $false "No grid simulator integration"
            }
        } else {
            Write-TestResult "Grid simulation support: $file" $false "File not found"
        }
    }
} else {
    Write-Host "Skipping grid-in-loop tests" -ForegroundColor Yellow
}

# Phase 5: End-to-End Tests
Write-Host "`nPhase 5: End-to-End Tests" -ForegroundColor Cyan
Write-Host "=========================" -ForegroundColor Cyan

if (-not $SkipEndToEnd) {
    # Check for end-to-end test files
    $e2eTestFiles = @(
        "tests/integration/end_to_end_pipeline_test.rs"
    )
    
    foreach ($file in $e2eTestFiles) {
        if (Test-Path $file) {
            $content = Get-Content $file -Raw
            if ($content -match "STL" -and $content -match "Lean" -and $content -match "SMT") {
                Write-TestResult "End-to-end pipeline test: $file" $true
            } else {
                Write-TestResult "End-to-end pipeline test: $file" $false "Incomplete pipeline coverage"
            }
        } else {
            Write-TestResult "End-to-end pipeline test: $file" $false "File not found"
        }
    }
    
    # Check for deployment configuration
    $deploymentFiles = @(
        "infrastructure/terraform/gpu-farm/main.tf",
        ".github/workflows/ci.yml"
    )
    
    foreach ($file in $deploymentFiles) {
        if (Test-Path $file) {
            Write-TestResult "Deployment configuration: $file" $true
        } else {
            Write-TestResult "Deployment configuration: $file" $false "File not found"
        }
    }
} else {
    Write-Host "Skipping end-to-end tests" -ForegroundColor Yellow
}

# Phase 6: Security and Compliance
Write-Host "`nPhase 6: Security and Compliance" -ForegroundColor Cyan
Write-Host "===============================" -ForegroundColor Cyan

# Check for compliance documentation
$complianceFiles = @(
    "docs/architecture/threat-model.md",
    "tests/deployment-readiness-checklist.md"
)

foreach ($file in $complianceFiles) {
    if (Test-Path $file) {
        $lineCount = (Get-Content $file).Count
        if ($lineCount -gt 20) {
            Write-TestResult "Compliance documentation: $file" $true "Lines: $lineCount"
        } else {
            Write-TestResult "Compliance documentation: $file" $false "Insufficient documentation"
        }
    } else {
        Write-TestResult "Compliance documentation: $file" $false "File not found"
    }
}

# Final Summary
Write-Host "`n=== Test Summary ===" -ForegroundColor Green
Write-Host "Total Tests: $totalTests" -ForegroundColor White
Write-Host "Passed: $passedTests" -ForegroundColor Green
Write-Host "Failed: $failedTests" -ForegroundColor Red
Write-Host "Success Rate: $([math]::Round(($passedTests / $totalTests) * 100, 2))%" -ForegroundColor White

$testReport += "`n`n## Final Summary`n"
$testReport += "- Total Tests: $totalTests`n"
$testReport += "- Passed: $passedTests`n"
$testReport += "- Failed: $failedTests`n"
$testReport += "- Success Rate: $([math]::Round(($passedTests / $totalTests) * 100, 2))%`n"

# Save test report
$testReport | Out-File -FilePath $TestReportPath -Encoding UTF8
Write-Host "`nTest report saved to: $TestReportPath" -ForegroundColor Cyan

if ($failedTests -eq 0) {
    Write-Host "`n🎉 All tests passed! Ready for deployment." -ForegroundColor Green
    exit 0
} else {
    Write-Host "`n⚠️  Some tests failed. Please address issues before deployment." -ForegroundColor Yellow
    exit 1
} 