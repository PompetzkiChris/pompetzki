# Registry gate, then the released pmp proof judge only after GATE.
# A registry refusal is not a proof verdict. REG0.canon is not read.
# Not executed in the Linux run.
param([Parameter(Mandatory = $true)][string]$Path)
$ErrorActionPreference = "Stop"
$Dir = Split-Path -Parent $MyInvocation.MyCommand.Path
if (-not $env:POMPETZKI) { throw "set POMPETZKI" }
if (-not $env:JUDGE_V3) { throw "set JUDGE_V3 to the released judge-v3.pmp" }
$File = (Resolve-Path -LiteralPath $Path).Path
$gate = Join-Path $Dir "reggate.pmp"
$out = & $env:POMPETZKI $gate $File 2>&1 | Out-String
Write-Output $out
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
if (($out -split "`n")[0].Trim() -ne "GATE") { throw "reggate exited 0 without GATE" }
if ($env:GATE_PROOF_LOG) { Add-Content -LiteralPath $env:GATE_PROOF_LOG -Value $File }
& $env:POMPETZKI $env:JUDGE_V3 $File
exit $LASTEXITCODE
