# PCS + legacy substrate Bazel gate (Windows).
$ErrorActionPreference = "Stop"
$Root = Split-Path -Parent (Split-Path -Parent $MyInvocation.MyCommand.Path)
Set-Location $Root

if (-not (Get-Command bazel -ErrorAction SilentlyContinue)) {
    Write-Error "bazel not found; install Bazelisk: https://github.com/bazelbuild/bazelisk"
}

$targets = @("//tests/pipeline_integration:pipeline_integration")
$optional = @(
    "//tests/certifyedge-integration:cli",
    "//tests/certifyedge-integration:pcs_v01",
    "//tests/certifyedge-integration:runbook",
    "//scripts:pcs_runbook"
)
foreach ($t in $optional) {
    bazel query $t 2>$null | Out-Null
    if ($LASTEXITCODE -eq 0) { $targets += $t }
}

$cargoHome = if ($env:CARGO_HOME) { $env:CARGO_HOME } else { Join-Path $Root ".cargo-home" }
New-Item -ItemType Directory -Force -Path $cargoHome | Out-Null
$configSrc = Join-Path $Root ".cargo\config.toml"
$configDst = Join-Path $cargoHome "config.toml"
if (Test-Path $configSrc) { Copy-Item $configSrc $configDst -Force }
else { "[http]`ncheck-revoke = false" | Set-Content $configDst -Encoding utf8 }
$env:CARGO_HOME = $cargoHome

$bazelExtra = @()
if (Test-Path "$Root\.bazelrc.windows") { $bazelExtra += "--bazelrc=.bazelrc.windows" }

Write-Host "bazel test --config=ci $($targets -join ' ')"
& bazel @bazelExtra test --config=ci --action_env=CARGO_HOME @targets
if ($LASTEXITCODE -ne 0) {
    Write-Host ""
    Write-Host "Bazel failed (often PKIX / certificate on Windows)." -ForegroundColor Yellow
    Write-Host "Try: .\scripts\test-substrate.ps1  (Cargo tests)" -ForegroundColor Yellow
    exit 32
}
