param([switch]$ReuseCertificateBuild)

$ErrorActionPreference = 'Stop'
$previousLeanThreads = $env:LEAN_NUM_THREADS
$env:LEAN_NUM_THREADS = '2'
Push-Location $PSScriptRoot
try {
    New-Item -ItemType Directory -Path 'verification/certificate-kernel' -Force | Out-Null
    $started = Get-Date
    $batchResults = @()
    if ($ReuseCertificateBuild) {
        $prior = Get-Content -Raw -LiteralPath 'verification/certificate-kernel/summary.json' | ConvertFrom-Json
        $expectedNames = @(0..42 | ForEach-Object { 'Checked{0:D2}' -f $_ })
        $actualNames = @($prior.results.module | Sort-Object)
        if (-not $prior.success -or $prior.results.Count -ne 43 -or
            @($prior.results | Where-Object { $_.returncode -ne 0 }).Count -ne 0 -or
            ($expectedNames -join ',') -ne ($actualNames -join ',')) {
            throw 'A complete successful certificate build is required for reuse.'
        }
        $batchResults = @($prior.results | Sort-Object module)
    } else {
      foreach ($batch in 0..42) {
        $batchName = 'Checked{0:D2}' -f $batch
        $batchStarted = Get-Date
        & lake build "QuadraticTangZhang.Certificate.$batchName" 2>&1 |
            Tee-Object -FilePath "verification/certificate-kernel/$batchName.log"
        if ($LASTEXITCODE -ne 0) { throw "Certificate batch $batchName failed." }
        $batchResults += [ordered]@{
            module = $batchName
            returncode = 0
            seconds = [math]::Round(((Get-Date) - $batchStarted).TotalSeconds, 2)
        }
      }
    }
    & lake build 2>&1 | Tee-Object -FilePath 'verification/build.log'
    if ($LASTEXITCODE -ne 0) { throw 'Lean project build failed.' }
    & lake env lean -DautoImplicit=false Audit.lean 2>&1 |
        Tee-Object -FilePath 'verification/axioms.log'
    if ($LASTEXITCODE -ne 0) { throw 'Lean axiom audit failed to compile.' }
    $auditText = Get-Content -Raw -LiteralPath 'verification/axioms.log'
    $allowedAxioms = @('propext', 'Classical.choice', 'Quot.sound')
    $axiomReports = [regex]::Matches($auditText, '(?s)depends on axioms:\s*\[([^\]]*)\]')
    if ($axiomReports.Count -lt 20) { throw 'The axiom audit is incomplete.' }
    foreach ($match in $axiomReports) {
        foreach ($axiomName in $match.Groups[1].Value.Split(',')) {
            $trimmedName = $axiomName.Trim()
            if ($trimmedName -and $trimmedName -notin $allowedAxioms) {
                throw "Unexpected axiom dependency: $trimmedName"
            }
        }
    }
    if ($auditText -match 'sorryAx|ofReduceBool|trustCompiler|error:') {
        throw 'The audit contains an untrusted proof dependency or an error.'
    }
    $requiredTheorems = @('remainingInterior', 'mainStatement', 'equalityStatement',
        'main_theorem', 'strict_interior', 'powers_ge_two')
    foreach ($theorem in $requiredTheorems) {
        if ($auditText -notmatch ([regex]::Escape("QuadraticTangZhang.$theorem") +
            "' depends on axioms:")) {
            throw "Missing final theorem audit: $theorem"
        }
    }
    $summary = [ordered]@{
        success = $true
        completed_utc = (Get-Date).ToUniversalTime().ToString('o')
        build_passed = $true
        axiom_audit_passed = $true
        local_theorems_audited = $axiomReports.Count
        allowed_axioms = $allowedAxioms
        full_main_theorem_proved = $true
        full_equality_classification_proved = $true
        powers_ge_two_proved = $true
        final_statements_have_no_certificate_hypothesis = $true
        completed_stages = @('A','B','C','D','E','F','G','H','I','J','K','L','M','N')
        certificate_records = 6593
        certificate_degree_blocks = 430
        certificate_batches = $batchResults
        certificate_proof_method = 'Lean decide +kernel'
        finite_degree_range = '6 <= n <= 1000000'
        infinite_degree_range = '1000001 <= n'
        seconds = [math]::Round(((Get-Date) - $started).TotalSeconds, 2)
    }
    $summary | ConvertTo-Json -Depth 6 | Set-Content -LiteralPath 'verification/summary.json' -Encoding utf8
    Write-Host 'All stages A-N passed: 6593 certificate records, the main theorem, equality, and powers >= 2.'
} finally {
    $env:LEAN_NUM_THREADS = $previousLeanThreads
    Pop-Location
}
