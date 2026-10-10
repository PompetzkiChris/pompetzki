$ErrorActionPreference = 'Stop'
$recoveryBookRoot = Split-Path -Parent $PSScriptRoot
$racketExe = 'C:\Program Files\Racket\racket.exe'
function Run-Receipt {
    param([string]$Name,[string[]]$ToolArguments)
    $receiptPath = Join-Path $recoveryBookRoot ('runs\' + $Name + '.txt')
    if (Test-Path -LiteralPath $receiptPath) { throw "Receipt already exists: $receiptPath" }
    & $racketExe @ToolArguments *> $receiptPath
    $toolExitCode = $LASTEXITCODE
    Get-Content -LiteralPath $receiptPath
    if ($toolExitCode -ne 0) { throw "$Name failed with exit $toolExitCode" }
}
Run-Receipt 'DECIDE' @((Join-Path $PSScriptRoot 'decide.rkt'),(Join-Path $recoveryBookRoot 'inventory.tsv'),(Join-Path $recoveryBookRoot 'chainverify.tsv'),(Join-Path $recoveryBookRoot 'MERGE-PLAN.tsv'),(Join-Path $recoveryBookRoot 'spot\run-recovery\SPOTCHECK.tsv'))
Run-Receipt 'MERGE' @((Join-Path $PSScriptRoot 'book-merge.rkt'),(Join-Path $recoveryBookRoot 'MERGE-PLAN.tsv'),(Join-Path $recoveryBookRoot 'inventory.tsv'),$recoveryBookRoot,'2026-10-10 GPT recovery')
Run-Receipt 'MASTER-VERIFY' @((Join-Path $PSScriptRoot 'master-verify.rkt'),$recoveryBookRoot)
Run-Receipt 'INDEPENDENT-VERIFY' @((Join-Path $PSScriptRoot 'master-verify-indep.rkt'),$recoveryBookRoot)
