param([switch]$SkipLakeUpdate)

$ErrorActionPreference = "Stop"
Write-Host "== Generation cardinality endpoint Lean audit =="
Set-Location (Join-Path $PSScriptRoot "..")

Write-Host "`n== Lean toolchain =="
Get-Content .\lean-toolchain
lake --version

Write-Host "`n== Dependency pins =="
Get-Content .\lakefile.toml

if (-not $SkipLakeUpdate) {
  Write-Host "`n== Lake update =="
  lake update
  if ($LASTEXITCODE -ne 0) { throw "lake update failed." }
}

Write-Host "`n== ProofWidgets release fallback =="
$proofwidgetsTar = ".lake\packages\proofwidgets\.lake\ProofWidgets4.tar.gz"
$proofwidgetsBuild = ".lake\packages\proofwidgets\.lake\build"
if ((Test-Path ".lake\packages\proofwidgets") -and -not (Test-Path $proofwidgetsTar)) {
  New-Item -ItemType Directory -Force -Path (Split-Path $proofwidgetsTar) | Out-Null
  Invoke-WebRequest -Uri "https://github.com/leanprover-community/ProofWidgets4/releases/download/v0.0.87/ProofWidgets4.tar.gz" -OutFile $proofwidgetsTar -UseBasicParsing
  New-Item -ItemType Directory -Force -Path $proofwidgetsBuild | Out-Null
  tar -xzf $proofwidgetsTar -C $proofwidgetsBuild
  Write-Host "Installed local ProofWidgets release payload."
} elseif (Test-Path $proofwidgetsTar) {
  Write-Host "Local ProofWidgets release payload already present."
} else {
  Write-Host "ProofWidgets package has not been materialized yet; Lake may fetch it during build."
}

Write-Host "`n== Project-level declaration scan =="
$scanRoots = @("GenerationCardinality", "SM6", "SM5", "SM4", "SM3", "SM2", "SM1", "MaleyLean", "Checks\Axiom")
$bad = @()
foreach ($root in $scanRoots) {
  if (Test-Path $root) {
    $leanFiles = Get-ChildItem -Path $root -Recurse -Filter "*.lean" -File
    if ($leanFiles.Count -gt 0) {
      $bad += $leanFiles | Select-String -Pattern '^\s*(axiom|unsafe|sorry|admit)\b' -ErrorAction SilentlyContinue
    }
  }
}
if ($bad.Count -gt 0) {
  $bad | Format-Table -AutoSize
  throw "Found live project-level axiom/sorry/admit/unsafe declaration."
}
Write-Host "No live project-level axiom/sorry/admit/unsafe declaration found."

Write-Host "`n== Build GenerationCardinality =="
lake build GenerationCardinality
if ($LASTEXITCODE -ne 0) {
  if ((Test-Path ".lake\packages\proofwidgets") -and -not (Test-Path $proofwidgetsTar)) {
    Write-Host "Build failed after ProofWidgets materialized; installing local release payload and retrying."
    New-Item -ItemType Directory -Force -Path (Split-Path $proofwidgetsTar) | Out-Null
    Invoke-WebRequest -Uri "https://github.com/leanprover-community/ProofWidgets4/releases/download/v0.0.87/ProofWidgets4.tar.gz" -OutFile $proofwidgetsTar -UseBasicParsing
    New-Item -ItemType Directory -Force -Path $proofwidgetsBuild | Out-Null
    tar -xzf $proofwidgetsTar -C $proofwidgetsBuild
    lake build GenerationCardinality
  }
  if ($LASTEXITCODE -ne 0) { throw "lake build GenerationCardinality failed." }
}

Write-Host "`n== Focused axiom check =="
lake env lean Checks\Axiom\GenerationCardinalityAxiomCheck.lean
if ($LASTEXITCODE -ne 0) { throw "Focused axiom check failed." }

Write-Host "`n== Audit complete =="
