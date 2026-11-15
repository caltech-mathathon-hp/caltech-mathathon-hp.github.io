[CmdletBinding()]
param([string]$Lake = 'lake', [switch]$SourcesOnly)

Set-StrictMode -Version Latest
$ErrorActionPreference = 'Stop'
$projectRoot = [IO.Path]::GetFullPath((Join-Path $PSScriptRoot '..'))
# Reuse the namespace-aware parser and run its self-test before trusting it.
. (Join-Path $PSScriptRoot 'UpdateCubicNPAudit.ps1') -SelfTest -Lake $Lake
$manifest = Get-Content -LiteralPath (Join-Path $PSScriptRoot 'source-manifest.json') -Raw | ConvertFrom-Json
$actualPaths = @(
    'ProteinFolding.lean'
    Get-ChildItem -LiteralPath (Join-Path $projectRoot 'ProteinFolding') -Recurse -File -Filter '*.lean' |
        ForEach-Object { [IO.Path]::GetRelativePath($projectRoot, $_.FullName).Replace('\', '/') }
) | Sort-Object
$expectedPaths = @($manifest.files | Where-Object { $_.path.EndsWith('.lean') } | ForEach-Object { $_.path }) | Sort-Object
if (Compare-Object $actualPaths $expectedPaths) { throw 'Source file set differs from the manifest.' }
$forbidden = '\b(?:sorry|admit|axiom|opaque|native_decide|unsafe|extern|implemented_by|csimp|proof_wanted)\b'
foreach ($entry in $manifest.files) {
    $path = Join-Path $projectRoot $entry.path
    $hash = (Get-FileHash -LiteralPath $path -Algorithm SHA256).Hash.ToLowerInvariant()
    if ($hash -cne $entry.sha256) { throw "Source hash mismatch: $($entry.path)" }
    if (-not $entry.path.EndsWith('.lean')) { continue }
    $code = Remove-LeanCommentsAndStrings -Text ([IO.File]::ReadAllText($path))
    if ($code -match $forbidden) { throw "Forbidden Lean construct '$($Matches[0])' in $($entry.path)" }
    $imports = @([regex]::Matches($code, '(?m)^import\s+(\S+)') | ForEach-Object { $_.Groups[1].Value })
    if (($imports -join "`n") -cne ($entry.imports -join "`n")) { throw "Import list mismatch: $($entry.path)" }
    foreach ($module in $imports) {
        if ($module.StartsWith('ProteinFolding.')) {
            $dependency = $module.Replace('.', '/') + '.lean'
            if ($dependency -notin $expectedPaths) { throw "Missing source dependency: $dependency" }
        }
    }
}
foreach ($entry in $manifest.frozenFiles) {
    if ((Get-FileHash -LiteralPath (Join-Path $projectRoot $entry.path) -Algorithm SHA256).Hash.ToLowerInvariant() -cne $entry.sha256) {
        throw "Frozen definition changed: $($entry.path)"
    }
}
Write-Output "Source integrity: $($actualPaths.Count) Lean files; all imports present; frozen hashes match; forbidden-token scan passed."
if ($SourcesOnly) { return }

Push-Location -LiteralPath $projectRoot
try {
    $auditFile = Join-Path $PSScriptRoot 'CubicHardness.lean'
    $expected = @([regex]::Matches([IO.File]::ReadAllText($auditFile), '(?m)^#print axioms\s+(\S+)') |
        ForEach-Object { $_.Groups[1].Value })
    $output = (@(& $Lake env lean checks/CubicHardness.lean 2>&1 | ForEach-Object { "$_" }) -join "`n") + "`n"
    $exitCode = $LASTEXITCODE
    [IO.File]::WriteAllText((Join-Path $PSScriptRoot 'local-main-axioms.txt'), $output, [Text.UTF8Encoding]::new($false))
    if ($exitCode -ne 0) { throw 'Main Lean audit failed. See checks/local-main-axioms.txt.' }
    $reports = @([regex]::Matches($output, "(?ms)^'([^\r\n]+)' depends on axioms:\s*\[([^\]]*)\]"))
    $empty = @([regex]::Matches($output, "(?m)^'([^\r\n]+)' does not depend on any axioms"))
    $reportedNames = @($reports + $empty | ForEach-Object { $_.Groups[1].Value })
    if (($reportedNames.Count -ne $expected.Count) -or (Compare-Object $expected $reportedNames)) {
        throw 'Missing or unexpected main axiom reports.'
    }
    foreach ($report in $reports) {
        foreach ($name in ($report.Groups[2].Value -split ',')) {
            if ($name.Trim() -and $name.Trim() -notin @('propext', 'Classical.choice', 'Quot.sound')) {
                throw "Unexpected main theorem axiom: $name"
            }
        }
    }
    Write-Output "Main audit passed: $($expected.Count) declarations; only permitted axioms."
    & (Join-Path $PSScriptRoot 'UpdateCubicNPAudit.ps1') -Apply -RunAudit -Lake $Lake -AuditName CubicSourceAudit -LogStem local-source
} finally {
    Pop-Location
}
