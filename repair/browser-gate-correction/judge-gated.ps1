# Credited correction of Grok's gate wrapper; default proof source is judge-v5.
param(
  [Parameter(Mandatory=$true)][string]$Path,
  [string]$Interpreter,
  [string]$JudgeSource
)
$ErrorActionPreference = 'Stop'
$Dir = Split-Path -Parent $MyInvocation.MyCommand.Path
if (-not $Interpreter) { $Interpreter = $env:POMPETZKI }
if (-not $Interpreter) { $Interpreter = 'pompetzki.exe' }
if (-not $JudgeSource) { $JudgeSource = $env:JUDGE_V5 }
if (-not $JudgeSource) { $JudgeSource = Join-Path $Dir '../../judge/judge-v5.pmp' }
$File = (Resolve-Path -LiteralPath $Path).Path
$Judge = (Resolve-Path -LiteralPath $JudgeSource).Path
$Gate = Join-Path $Dir 'reggate.pmp'
$Text = & $Interpreter $Gate $File 2>&1 | Out-String
$GateExit = $LASTEXITCODE
Write-Output $Text
if ($GateExit -ne 0) { exit $GateExit }
if (($Text -split "`n")[0].Trim() -ne 'GATE') { throw 'gate exited 0 without GATE' }
if ($env:GATE_PROOF_LOG) { Add-Content -LiteralPath $env:GATE_PROOF_LOG -Value $File }
& $Interpreter $Judge $File
exit $LASTEXITCODE
