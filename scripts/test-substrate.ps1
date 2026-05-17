# Substrate Cargo tests (Windows).
$ErrorActionPreference = "Stop"
$Root = Split-Path -Parent (Split-Path -Parent $MyInvocation.MyCommand.Path)
Set-Location $Root

$packages = @("smt-verifier", "stl-compiler", "integration_tests")
$meta = cargo metadata --no-deps --format-version 1 2>$null
if ($meta -match '"name":"substrate-unit"') {
    $packages += "substrate-unit"
}
Write-Host "cargo test -p $($packages -join ' -p ')"
& cargo test -p $packages @args
