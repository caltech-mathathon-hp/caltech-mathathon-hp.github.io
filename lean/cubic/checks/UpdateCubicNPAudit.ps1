[CmdletBinding()]
param(
    [switch]$Apply,
    [switch]$BuiltOnly,
    [switch]$RunAudit,
    [switch]$SelfTest,
    [switch]$ListChanges,
    [string[]]$ExcludeModule = @(),
    [string]$Lake = 'lake',
    [ValidatePattern('^[A-Za-z0-9_-]+$')][string]$AuditName = 'CubicNPMembership',
    [ValidatePattern('^[A-Za-z0-9_-]+$')][string]$LogStem = 'cubic-np-membership'
)

# Examples:
#   .\checks\UpdateCubicNPAudit.ps1 -SelfTest
#   .\checks\UpdateCubicNPAudit.ps1 -BuiltOnly -Apply -RunAudit
#   .\checks\UpdateCubicNPAudit.ps1 -Apply -RunAudit
# The default is a dry run. -BuiltOnly records and omits source modules whose
# .olean is missing or older than the source; it never imports the root aggregate.
Set-StrictMode -Version Latest
$ErrorActionPreference = 'Stop'

function Remove-LeanCommentsAndStrings {
    param([Parameter(Mandatory)][AllowEmptyString()][string]$Text)
    $result = [Text.StringBuilder]::new()
    $depth = 0
    $inString = $false
    $escaped = $false
    for ($i = 0; $i -lt $Text.Length; $i++) {
        $ch = $Text[$i]
        $next = if ($i + 1 -lt $Text.Length) { $Text[$i + 1] } else { [char]0 }
        if ($depth -gt 0) {
            if ($ch -eq '/' -and $next -eq '-') {
                $depth++
                [void]$result.Append('  ')
                $i++
            } elseif ($ch -eq '-' -and $next -eq '/') {
                $depth--
                [void]$result.Append('  ')
                $i++
            } else {
                [void]$result.Append($(if ($ch -eq "`n" -or $ch -eq "`r") { $ch } else { ' ' }))
            }
            continue
        }
        if ($inString) {
            if ($escaped) { $escaped = $false }
            elseif ($ch -eq '\') { $escaped = $true }
            elseif ($ch -eq '"') { $inString = $false }
            [void]$result.Append($(if ($ch -eq "`n" -or $ch -eq "`r") { $ch } else { ' ' }))
            continue
        }
        if ($ch -eq '-' -and $next -eq '-') {
            while ($i -lt $Text.Length -and $Text[$i] -ne "`n") {
                [void]$result.Append($(if ($Text[$i] -eq "`r") { "`r" } else { ' ' }))
                $i++
            }
            if ($i -lt $Text.Length) { [void]$result.Append("`n") }
        } elseif ($ch -eq '/' -and $next -eq '-') {
            $depth = 1
            [void]$result.Append('  ')
            $i++
        } elseif ($ch -eq '"') {
            $inString = $true
            [void]$result.Append(' ')
        } else {
            [void]$result.Append($ch)
        }
    }
    if ($depth -ne 0) { throw 'Unterminated Lean block comment.' }
    if ($inString) { throw 'Unterminated Lean string literal.' }
    return $result.ToString()
}

function Get-LeanNamedDeclarations {
    param([Parameter(Mandatory)][string]$Text, [string]$SourceName = '<memory>')
    $clean = Remove-LeanCommentsAndStrings -Text $Text
    $scopes = [Collections.Generic.List[object]]::new()
    $declarations = [Collections.Generic.List[object]]::new()
    $skipped = [Collections.Generic.List[string]]::new()
    $issues = [Collections.Generic.List[string]]::new()
    $currentNamespace = ''
    $lineNumber = 0
    foreach ($rawLine in ($clean -split '\r?\n')) {
        $lineNumber++
        $line = $rawLine.Trim()
        while ($line -match '^@\[[^\]]*\]\s*') {
            $line = $line.Substring($Matches[0].Length).TrimStart()
        }
        if ($line -match '^namespace\s+(?<name>\S+)\s*$') {
            $name = $Matches['name']
            $before = $currentNamespace
            if ($name.StartsWith('_root_.', [StringComparison]::Ordinal)) {
                $currentNamespace = $name.Substring(7)
            } elseif ($currentNamespace.Length -eq 0) { $currentNamespace = $name }
            else { $currentNamespace += '.' + $name }
            $scopes.Add([pscustomobject]@{ Kind = 'namespace'; Name = $name; Before = $before; Line = $lineNumber })
            continue
        }
        if ($line -match '^(?:noncomputable\s+)?section(?:\s+(?<name>\S+))?\s*$') {
            $name = if ($Matches.ContainsKey('name')) { $Matches['name'] } else { '' }
            $scopes.Add([pscustomobject]@{ Kind = 'section'; Name = $name; Before = $currentNamespace; Line = $lineNumber })
            continue
        }
        if ($line -eq 'mutual') {
            $scopes.Add([pscustomobject]@{ Kind = 'mutual'; Name = ''; Before = $currentNamespace; Line = $lineNumber })
            continue
        }
        if ($line -match '^end(?:\s+(?<name>\S+))?\s*$') {
            if ($scopes.Count -eq 0) { $issues.Add("${SourceName}:${lineNumber}: unmatched end."); continue }
            $scope = $scopes[$scopes.Count - 1]
            $scopes.RemoveAt($scopes.Count - 1)
            $name = if ($Matches.ContainsKey('name')) { $Matches['name'] } else { '' }
            if ($name.Length -gt 0 -and $name -ne $scope.Name) {
                $issues.Add("${SourceName}:${lineNumber}: end $name does not match $($scope.Kind) $($scope.Name) at line $($scope.Line).")
            }
            $currentNamespace = $scope.Before
            continue
        }
        if ($line -cmatch '^(?<modifiers>(?:(?:noncomputable|unsafe|partial|private|protected|local|scoped)\s+)*)(?<kind>def|theorem|lemma|instance|inductive|structure|abbrev|axiom|opaque|constant)\b(?<rest>.*)$') {
            $modifiers = $Matches['modifiers']
            $kind = $Matches['kind']
            $rest = $Matches['rest'].TrimStart()
            if ($modifiers -match '\bprivate\b') { $skipped.Add("${SourceName}:${lineNumber}: private $kind"); continue }
            if ($kind -in @('axiom', 'opaque', 'constant') -or $modifiers -match '\b(?:unsafe|partial)\b') {
                $issues.Add("${SourceName}:${lineNumber}: forbidden declaration '$modifiers$kind'.")
                continue
            }
            if ($rest -notmatch '^(?<name>(?:«[^»]+»|[^\s:()\[\]{}]+))') {
                if ($kind -eq 'instance') { $skipped.Add("${SourceName}:${lineNumber}: anonymous instance"); continue }
                $issues.Add("${SourceName}:${lineNumber}: unnamed $kind.")
                continue
            }
            $name = $Matches['name']
            $qualified = if ($name.StartsWith('_root_.', [StringComparison]::Ordinal)) { $name.Substring(7) }
                elseif ($currentNamespace.Length -eq 0) { $name } else { $currentNamespace + '.' + $name }
            $declarations.Add([pscustomobject]@{ Name = $qualified; Kind = $kind; Source = $SourceName; Line = $lineNumber })
        }
    }
    foreach ($scope in $scopes) { $issues.Add("${SourceName}:$($scope.Line): unclosed $($scope.Kind) $($scope.Name).") }
    return [pscustomobject]@{ Declarations = @($declarations.ToArray()); Skipped = @($skipped.ToArray()); Issues = @($issues.ToArray()) }
}

if ($SelfTest) {
    if ($Apply -or $RunAudit) { throw '-SelfTest cannot be combined with -Apply or -RunAudit.' }
    $fixture = @'
/- namespace Fake
 /- private def invisible := 0 -/
 end Fake -/
namespace ProteinFolding.Test
section
@[simp] theorem top' : True := by trivial
section Scoped
namespace Nested
@[simp, aesop safe] def read := "end Nested"
end Nested
end Scoped
end
noncomputable section
protected theorem after : True := by trivial
instance namedInstance : Decidable True := inferInstance
end
private def hidden := 0
instance : Decidable False := inferInstance
-- namespace Ignored
end ProteinFolding.Test
'@
    $parsed = Get-LeanNamedDeclarations -Text $fixture -SourceName '<self-test>'
    $expected = @('ProteinFolding.Test.top''', 'ProteinFolding.Test.Nested.read',
        'ProteinFolding.Test.after', 'ProteinFolding.Test.namedInstance')
    if (($parsed.Declarations.Name -join "`n") -cne ($expected -join "`n")) { throw 'Namespace/section/attribute/prime-name self-test failed.' }
    if ($parsed.Issues.Count -ne 0 -or $parsed.Skipped.Count -ne 2) { throw 'Private/anonymous-declaration self-test failed.' }
    $forbidden = Get-LeanNamedDeclarations -Text 'axiom bad : False' -SourceName '<forbidden>'
    if ($forbidden.Issues.Count -ne 1) { throw 'Forbidden-declaration self-test failed.' }
    $continuation = Get-LeanNamedDeclarations -Text "namespace Test`nnoncomputable def getSizes : EncodedFunction`n    Instance.sizes := value`nend Test" -SourceName '<continuation>'
    if ($continuation.Declarations.Count -ne 1 -or $continuation.Declarations[0].Name -cne 'Test.getSizes') {
        throw 'Case-sensitive declaration keyword self-test failed.'
    }
    [pscustomobject]@{ SelfTest = 'passed'; Declarations = $parsed.Declarations.Count; ExpectedSkips = $parsed.Skipped.Count }
    return
}

if ($RunAudit -and -not $Apply) { throw '-RunAudit requires -Apply so the generated audit is exactly the audited file.' }
$projectRoot = [IO.Path]::GetFullPath((Join-Path $PSScriptRoot '..'))
$auditRelative = 'checks/' + $AuditName + '.lean'
$auditPath = Join-Path $PSScriptRoot ($AuditName + '.lean')
$logPath = Join-Path $PSScriptRoot ($LogStem + '-axioms.txt')
$summaryPath = Join-Path $PSScriptRoot ($LogStem + '-summary.json')
$files = @(Get-ChildItem -LiteralPath (Join-Path $projectRoot 'ProteinFolding') -Filter '*.lean' -File -Recurse) |
    Sort-Object FullName -Unique
$seen = [Collections.Generic.Dictionary[string, object]]::new([StringComparer]::Ordinal)
$included = [Collections.Generic.List[object]]::new()
$skippedModules = [Collections.Generic.List[string]]::new()
$skippedDeclarations = [Collections.Generic.List[string]]::new()
$issues = [Collections.Generic.List[string]]::new()
foreach ($file in $files) {
    $relative = [IO.Path]::GetRelativePath($projectRoot, $file.FullName).Replace('\', '/')
    $module = $relative.Substring(0, $relative.Length - 5).Replace('/', '.')
    if ($module -in $ExcludeModule) { $skippedModules.Add("$module (explicit exclusion)"); continue }
    if ($BuiltOnly) {
        $olean = Join-Path $projectRoot ('.lake\build\lib\lean\' + [IO.Path]::ChangeExtension($relative, '.olean'))
        if (-not (Test-Path -LiteralPath $olean -PathType Leaf)) { $skippedModules.Add("$module (no .olean)"); continue }
        if ((Get-Item -LiteralPath $olean).LastWriteTimeUtc -lt $file.LastWriteTimeUtc) { $skippedModules.Add("$module (source newer than .olean)"); continue }
    }
    $text = [IO.File]::ReadAllText($file.FullName)
    $clean = Remove-LeanCommentsAndStrings -Text $text
    if ($clean -match '\b(?:sorry|admit|native_decide|unsafe|extern|implemented_by|csimp)\b') { $issues.Add("${relative}: forbidden proof or execution construct '$($Matches[0])'.") }
    $parsed = Get-LeanNamedDeclarations -Text $text -SourceName $relative
    foreach ($issue in $parsed.Issues) { $issues.Add($issue) }
    foreach ($skip in $parsed.Skipped) { $skippedDeclarations.Add($skip) }
    foreach ($declaration in $parsed.Declarations) {
        if ($seen.ContainsKey($declaration.Name)) {
            $prior = $seen[$declaration.Name]
            $issues.Add("Duplicate $($declaration.Name): $($prior.Source):$($prior.Line) and $($declaration.Source):$($declaration.Line).")
        } else { $seen.Add($declaration.Name, $declaration) }
    }
    $included.Add([pscustomobject]@{ Module = $module; Source = $relative;
        SHA256 = (Get-FileHash -LiteralPath $file.FullName -Algorithm SHA256).Hash.ToLowerInvariant(); Declarations = $parsed.Declarations })
}
if ($issues.Count -gt 0) { throw ($issues -join "`n") }

$lines = [Collections.Generic.List[string]]::new()
$lines.Add('-- Generated by checks/UpdateCubicNPAudit.ps1; do not edit by hand.')
$lines.Add('-- Scope: named public source declarations in every shipped project module, including Square dependencies.')
$lines.Add('-- Anonymous instances and compiler-generated declarations are not assigned synthetic audit names.')
$lines.Add('-- All source files are read only. The root aggregate is not imported.')
foreach ($skip in $skippedModules) { $lines.Add('-- Skipped module: ' + $skip) }
foreach ($item in $included) { $lines.Add('import ' + $item.Module) }
foreach ($item in $included) {
    $lines.Add('')
    $lines.Add('-- Source: ' + $item.Source)
    $lines.Add('-- SHA256: ' + $item.SHA256)
    foreach ($declaration in $item.Declarations) {
        $lines.Add('#check ' + $declaration.Name)
        $lines.Add('#print axioms ' + $declaration.Name)
    }
}
$generated = ($lines -join "`n") + "`n"
$existing = if (Test-Path -LiteralPath $auditPath) { [IO.File]::ReadAllText($auditPath) } else { '' }
$changed = $generated -cne $existing
if ($ListChanges) { foreach ($line in $lines) { Write-Output $line } }
if ($Apply -and $changed) { [IO.File]::WriteAllText($auditPath, $generated, [Text.UTF8Encoding]::new($false)) }
$summary = [ordered]@{
    Mode = $(if ($Apply) { 'apply' } else { 'dry-run' }); BuiltOnly = [bool]$BuiltOnly
    FilesScanned = $files.Count; FilesIncluded = $included.Count; Declarations = $seen.Count
    SkippedModules = @($skippedModules.ToArray()); SkippedDeclarations = @($skippedDeclarations.ToArray())
    Changed = $changed; Written = [bool]($Apply -and $changed); AuditPath = $auditRelative
    AuditExitCode = $null; AxiomReports = $null; UnexpectedAxioms = @()
}
if ($RunAudit) {
    Push-Location -LiteralPath $projectRoot
    try {
        $outputLines = @(& $lake env lean $auditRelative 2>&1 | ForEach-Object { "$_" })
        $auditExitCode = $LASTEXITCODE
    } finally { Pop-Location }
    $output = ($outputLines -join "`n") + "`n"
    [IO.File]::WriteAllText($logPath, $output, [Text.UTF8Encoding]::new($false))
    $unexpected = [Collections.Generic.HashSet[string]]::new([StringComparer]::Ordinal)
    # Names may contain Lean primes, so the quoted name is greedy to its last
    # quote on the line rather than stopping at the first apostrophe.
    $reports = [regex]::Matches($output, "(?ms)^'([^\r\n]+)' depends on axioms:\s*\[([^\]]*)\]")
    foreach ($report in $reports) {
        foreach ($name in ($report.Groups[2].Value -split ',')) {
            $name = $name.Trim()
            if ($name.Length -gt 0 -and $name -notin @('propext', 'Classical.choice', 'Quot.sound')) { [void]$unexpected.Add($name) }
        }
    }
    $withoutAxioms = [regex]::Matches($output, "(?m)^'([^\r\n]+)' does not depend on any axioms").Count
    $summary.AuditExitCode = $auditExitCode
    $summary.AxiomReports = $reports.Count + $withoutAxioms
    $summary.UnexpectedAxioms = @($unexpected | Sort-Object)
    if ($auditExitCode -ne 0 -or $unexpected.Count -gt 0 -or $summary.AxiomReports -ne $seen.Count) {
        [IO.File]::WriteAllText($summaryPath, (($summary | ConvertTo-Json -Depth 6) + "`n"), [Text.UTF8Encoding]::new($false))
        throw "Audit failed: exit=$auditExitCode, reports=$($summary.AxiomReports)/$($seen.Count), unexpected=$($summary.UnexpectedAxioms -join ', '). See $logPath."
    }
}
if ($Apply) { [IO.File]::WriteAllText($summaryPath, (($summary | ConvertTo-Json -Depth 6) + "`n"), [Text.UTF8Encoding]::new($false)) }
[pscustomobject]$summary
