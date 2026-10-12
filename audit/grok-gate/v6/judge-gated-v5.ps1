# v6 registry gate, then authenticated judge-v5.
# judge-v3 is not invoked. A registry refusal does not start the proof judge.
param([Parameter(Mandatory = $true)][string]$Path)
$ErrorActionPreference = "Stop"
$Dir = Split-Path -Parent $MyInvocation.MyCommand.Path
$Root = (Resolve-Path (Join-Path $Dir "..\..\..")).Path
if (-not $env:POMPETZKI) { throw "set POMPETZKI" }
if ($env:JUDGE_V5) { $Judge = $env:JUDGE_V5 } else { $Judge = Join-Path $Root "judge\judge-v5.pmp" }
$File = (Resolve-Path -LiteralPath $Path).Path
$gate = Join-Path $Dir "reggate.pmp"
$out = & $env:POMPETZKI $gate $File 2>&1 | Out-String
Write-Output $out
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
if (($out -split "`n")[0].Trim() -ne "GATE") { throw "reggate exited 0 without GATE" }
& $env:POMPETZKI $Judge $File
exit $LASTEXITCODE
