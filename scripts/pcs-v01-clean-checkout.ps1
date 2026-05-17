# PCS v0.1 clean-checkout from CertifyEdge (see scripts/pcs-v01-clean-checkout.sh).
param(
    [switch]$ThroughCertified,
    [switch]$LabtrustOnly,
    [switch]$SkipScientificMemory
)

$ErrorActionPreference = "Stop"
$Root = (Resolve-Path (Join-Path $PSScriptRoot "..")).Path
$Parent = Split-Path -Parent $Root
$LabtrustGym = if ($env:LABTRUST_GYM_ROOT) { $env:LABTRUST_GYM_ROOT } else { Join-Path $Parent "LabTrust-Gym" }
$Spec = Join-Path $Root "templates\hospital_lab\qc_release.stl"

Write-Host "==> build certifyedge"
Push-Location $Root
cargo build -p certifyedge -q
Pop-Location

$env:CERTIFYEDGE_ROOT = $Root
$env:CERTIFYEDGE_BIN = Join-Path $Root "scripts\certifyedge.sh"
$env:CERTIFYEDGE_SPEC = $Spec
if (-not $env:PCS_DETERMINISTIC) { $env:PCS_DETERMINISTIC = "1" }

$CxDir = if ($env:PCS_CLEAN_CHECKOUT_CX) { $env:PCS_CLEAN_CHECKOUT_CX } else { Join-Path $Root "target\pcs-v01-clean-checkout" }
New-Item -ItemType Directory -Force -Path $CxDir | Out-Null

function Invoke-Certifyedge([string[]]$Args) {
    $bash = Get-Command bash -ErrorAction SilentlyContinue
    if ($bash) {
        & bash $env:CERTIFYEDGE_BIN @Args
    } else {
        $bin = Join-Path $Root "target\debug\certifyedge.exe"
        if (-not (Test-Path $bin)) { $bin = Join-Path $Root "target\debug\certifyedge" }
        & $bin @Args
    }
}

Write-Host "==> CertifyEdge: invalid trace checks"
Invoke-Certifyedge @("check-trace", "--spec", $Spec, "--trace", (Join-Path $Root "tests\labtrust\valid_trace.json")) | Out-Null

@(
    @{ Label = "missing_qc"; Reason = "release_before_qc"; File = "invalid_missing_qc_trace.json" },
    @{ Label = "unauthorized"; Reason = "unauthorized_release"; File = "invalid_unauthorized_trace.json" }
) | ForEach-Object {
    $cx = Join-Path $CxDir "counterexample_$($_.Label).json"
    try {
        Invoke-Certifyedge @(
            "check-trace", "--spec", $Spec,
            "--trace", (Join-Path $Root "tests\labtrust\$($_.File)"),
            "--counterexample-out", $cx
        )
        throw "expected check-trace to fail for $($_.File)"
    } catch {
        if ($_.Exception.Message -notmatch "expected check-trace") { throw }
    }
    $doc = Get-Content $cx | ConvertFrom-Json
    if ($doc.reason -ne $_.Reason) {
        throw "counterexample reason $($doc.reason) != $($_.Reason)"
    }
    Write-Host "OK counterexample $cx reason=$($doc.reason)"
}

if ($ThroughCertified) {
    $chainSh = Join-Path $Root "scripts\pcs-v01-clean-checkout.sh"
    if (-not (Get-Command bash -ErrorAction SilentlyContinue)) {
        throw "Git Bash required for --ThroughCertified (PF-free chain). Install Git for Windows or run from LabTrust-Gym."
    }
    & bash $chainSh --through-certified
    exit $LASTEXITCODE
}

$chainSh = Join-Path $LabtrustGym "examples\pcs_qc_release\scripts\run_pcs_v01_clean_chain.sh"
if (-not (Test-Path $chainSh)) {
    throw "LabTrust-Gym chain script not found: $chainSh"
}
$bashArgs = @($chainSh)
if ($LabtrustOnly) { $bashArgs += "--labtrust-only" }
if ($SkipScientificMemory) { $bashArgs += "--skip-scientific-memory" }
& bash @bashArgs
