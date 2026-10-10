param(
    [string]$SourcePath = (Join-Path $PSScriptRoot 'abschluss-verify-r2.rkt'),
    [Parameter(Mandatory=$true)][string]$OutputDirectory
)
$ErrorActionPreference = 'Stop'
if(Test-Path -LiteralPath $OutputDirectory){throw "Output directory already exists: $OutputDirectory"}
New-Item -ItemType Directory -Path $OutputDirectory | Out-Null
$raco = (Get-Command raco.exe -ErrorAction Stop).Source
$racket = (Get-Command racket.exe -ErrorAction Stop).Source
$source = (Get-Item -LiteralPath $SourcePath).FullName
$exe = Join-Path $OutputDirectory 'abschluss-verify.exe'
& $racket --version | Set-Content -LiteralPath (Join-Path $OutputDirectory 'RACKET-VERSION.txt')
& $raco exe -o $exe $source 1>(Join-Path $OutputDirectory 'compile.stdout.txt') 2>(Join-Path $OutputDirectory 'compile.stderr.txt')
if($LASTEXITCODE -ne 0){throw "raco exe returned $LASTEXITCODE"}
$dist = Join-Path $OutputDirectory 'dist'
& $raco distribute $dist $exe 1>(Join-Path $OutputDirectory 'distribute.stdout.txt') 2>(Join-Path $OutputDirectory 'distribute.stderr.txt')
if($LASTEXITCODE -ne 0){throw "raco distribute returned $LASTEXITCODE"}
[ordered]@{
    source=$source
    source_sha256=(Get-FileHash -Algorithm SHA256 -LiteralPath $source).Hash.ToLower()
    raco=$raco
    commands=@(@('exe','-o',$exe,$source),@('distribute',$dist,$exe))
    exit_code=0
    distributed_binary_sha256=(Get-FileHash -Algorithm SHA256 -LiteralPath (Join-Path $dist 'abschluss-verify.exe')).Hash.ToLower()
    ended_utc=[DateTimeOffset]::UtcNow.ToString('o')
}|ConvertTo-Json -Depth 5|Set-Content -LiteralPath (Join-Path $OutputDirectory 'BUILD.json')
