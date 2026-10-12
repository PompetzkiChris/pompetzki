param([Parameter(Mandatory=$true)][string]$InstallRoot, [int]$WaitForPid = 0, [switch]$DryRun)
$ErrorActionPreference = 'Stop'
function Get-TaskSHA256([string]$LiteralPath) {
    $taskStream = [IO.File]::OpenRead($LiteralPath)
    $taskAlgorithm = [Security.Cryptography.SHA256]::Create()
    try { return [BitConverter]::ToString($taskAlgorithm.ComputeHash($taskStream)).Replace('-','').ToLowerInvariant() }
    finally { $taskStream.Dispose(); $taskAlgorithm.Dispose() }
}
$taskRoot = [IO.Path]::GetFullPath($InstallRoot).TrimEnd([IO.Path]::DirectorySeparatorChar)
$taskItem = Get-Item -LiteralPath $taskRoot -Force
if (-not $taskItem.PSIsContainer -or ($taskItem.Attributes -band [IO.FileAttributes]::ReparsePoint)) { throw 'Installation root must be a local directory without a reparse link.' }
$taskParent = $taskItem
while ($null -ne $taskParent) {
    if ($taskParent.Attributes -band [IO.FileAttributes]::ReparsePoint) { throw 'Uninstall through a reparse parent is refused.' }
    $taskParent = $taskParent.Parent
}
if ((Get-Content -LiteralPath (Join-Path $taskRoot 'VERSION') -Raw).Trim() -ne '1.3.1') { throw 'VERSION 1.3.1 is required.' }
$taskReceipt = Get-Content -LiteralPath (Join-Path $taskRoot 'INSTALLATION.json') -Raw | ConvertFrom-Json
$taskManifestPath = Join-Path $taskRoot 'MANIFEST.sha256'
$taskManifestHash = Get-TaskSHA256 $taskManifestPath
if ($taskReceipt.version -ne '1.3.1' -or $taskReceipt.manifest_sha256 -ne $taskManifestHash) { throw 'Installation receipt and manifest differ.' }
$taskDeclared = @{}
foreach ($taskLine in Get-Content -LiteralPath $taskManifestPath) {
    if ($taskLine -match '^([0-9a-fA-F]{64})  (.+)$') { $taskDeclared[$Matches[2].ToLowerInvariant()] = $Matches[1].ToLowerInvariant() }
    elseif ($taskLine.Trim()) { throw 'Malformed manifest line.' }
}
$taskDeclared['manifest.sha256'] = $taskManifestHash
$taskFiles = @()
foreach ($taskEntry in $taskReceipt.files) {
    $taskName = [string]$taskEntry.path
    if ([IO.Path]::IsPathRooted($taskName) -or $taskName -match '(^|[\\/])\.{1,2}([\\/]|$)' -or $taskName -match ':') { throw 'Unsafe file in installation receipt.' }
    $taskPath = [IO.Path]::GetFullPath((Join-Path $taskRoot $taskName))
    if (-not $taskPath.StartsWith($taskRoot + [IO.Path]::DirectorySeparatorChar, [StringComparison]::OrdinalIgnoreCase)) { throw 'Installed file leaves the installation root.' }
    $taskExpected = $taskDeclared[$taskName.ToLowerInvariant()]
    if (-not $taskExpected -or $taskExpected -ne $taskEntry.sha256) { throw 'Receipt contains a file outside the installed manifest.' }
    $taskFiles += [pscustomobject]@{Path=$taskPath;Sha256=$taskExpected}
}
if ($DryRun) { $taskFiles | ConvertTo-Json -Depth 4; exit 0 }
if ($WaitForPid -gt 0) { Wait-Process -Id $WaitForPid -ErrorAction SilentlyContinue }
$taskRemoved = @(); $taskPreserved = @()
foreach ($taskFile in $taskFiles) {
    if (Test-Path -LiteralPath $taskFile.Path -PathType Leaf) {
        $taskCurrent = Get-Item -LiteralPath $taskFile.Path -Force
        $taskLinkedParent = $false
        $taskAncestor = $taskCurrent.Directory
        while ($null -ne $taskAncestor -and $taskAncestor.FullName.StartsWith($taskRoot, [StringComparison]::OrdinalIgnoreCase)) {
            if ($taskAncestor.Attributes -band [IO.FileAttributes]::ReparsePoint) { $taskLinkedParent = $true; break }
            $taskAncestor = $taskAncestor.Parent
        }
        if ($taskLinkedParent -or ($taskCurrent.Attributes -band [IO.FileAttributes]::ReparsePoint) -or
            (Get-TaskSHA256 $taskFile.Path) -ne $taskFile.Sha256) {
            $taskPreserved += $taskFile.Path
        } else {
            Remove-Item -LiteralPath $taskFile.Path -Force
            $taskRemoved += $taskFile.Path
        }
    }
}
# Remove the generated installation receipt only after its declared files were checked.
Remove-Item -LiteralPath (Join-Path $taskRoot 'INSTALLATION.json') -Force
if ($taskReceipt.shortcut -and (Test-Path -LiteralPath $taskReceipt.shortcut -PathType Leaf)) {
    $taskExpectedShortcut = Join-Path $env:APPDATA 'Microsoft\Windows\Start Menu\Programs\Abschluss 1.3.1.lnk'
    $taskShell = New-Object -ComObject WScript.Shell
    $taskLink = $taskShell.CreateShortcut($taskReceipt.shortcut)
    if ([IO.Path]::GetFullPath($taskReceipt.shortcut) -eq $taskExpectedShortcut -and
        (Get-TaskSHA256 $taskReceipt.shortcut) -eq $taskReceipt.shortcut_sha256 -and
        [IO.Path]::GetFullPath($taskLink.TargetPath) -eq (Join-Path $taskRoot 'Abschluss Start.exe')) { Remove-Item -LiteralPath $taskReceipt.shortcut -Force }
}
# No directory is removed recursively. Additional and modified files remain.
$taskDirectories = @($taskFiles | ForEach-Object { [IO.Path]::GetDirectoryName($_.Path) } | Sort-Object -Unique | Sort-Object Length -Descending)
foreach ($taskDirectory in $taskDirectories) {
    if ($taskDirectory -ne $taskRoot -and (Test-Path -LiteralPath $taskDirectory -PathType Container) -and
        -not ((Get-Item -LiteralPath $taskDirectory -Force).Attributes -band [IO.FileAttributes]::ReparsePoint) -and
        -not (Get-ChildItem -LiteralPath $taskDirectory -Force | Select-Object -First 1)) { Remove-Item -LiteralPath $taskDirectory }
}
if (-not (Get-ChildItem -LiteralPath $taskRoot -Force | Select-Object -First 1)) { Remove-Item -LiteralPath $taskRoot }
[pscustomobject]@{Removed=$taskRemoved;Preserved=$taskPreserved} | ConvertTo-Json -Depth 4
