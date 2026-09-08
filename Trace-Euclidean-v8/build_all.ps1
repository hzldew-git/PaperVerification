param(
    [string]$PythonExe = 'D:\AI-Workspace\Environments\Python\math-research\Scripts\python.exe',
    [string]$WolframScriptExe = 'C:\Program Files\Wolfram Research\WolframScript\wolframscript.exe',
    [string]$LatexmkExe = 'C:\Software\texlive\2025\bin\windows\latexmk.exe',
    [string]$ManuscriptPath = ''
)

$ErrorActionPreference = 'Stop'
$packageRoot = Split-Path -Parent $MyInvocation.MyCommand.Path
$snapshotDirectory = Join-Path $packageRoot 'source_snapshot'
$snapshotPath = Join-Path $snapshotDirectory 'Trace-Euclidean-v8.tex'
New-Item -ItemType Directory -Path $snapshotDirectory -Force | Out-Null

if ($ManuscriptPath) {
    $resolvedManuscript = (Resolve-Path -LiteralPath $ManuscriptPath).Path
    if (-not (Test-Path -LiteralPath $resolvedManuscript -PathType Leaf)) {
        throw "Manuscript file not found: $resolvedManuscript"
    }
    Copy-Item -LiteralPath $resolvedManuscript -Destination $snapshotPath -Force
}

$manuscriptOutputDirectory = Join-Path $packageRoot 'output\manuscript'
New-Item -ItemType Directory -Path $manuscriptOutputDirectory -Force | Out-Null
Push-Location $snapshotDirectory
try {
    & $LatexmkExe -norc -xelatex -interaction=nonstopmode -halt-on-error -synctex=1 "-outdir=$manuscriptOutputDirectory" 'Trace-Euclidean-v8.tex'
    if ($LASTEXITCODE -ne 0) {
        throw 'Manuscript snapshot compilation failed.'
    }
}
finally {
    Pop-Location
}

$manuscriptAux = Join-Path $manuscriptOutputDirectory 'Trace-Euclidean-v8.aux'
& $PythonExe (Join-Path $packageRoot 'tools\prepare_inputs.py') --aux $manuscriptAux
if ($LASTEXITCODE -ne 0) {
    throw 'Manuscript input extraction failed.'
}

& $WolframScriptExe -file (Join-Path $packageRoot 'run_verification.wls')
$verificationExitCode = $LASTEXITCODE
if ($verificationExitCode -eq 1) {
    throw 'An exact, certified, coverage, or integrity check failed.'
}
if ($verificationExitCode -notin 0, 2) {
    throw "Unexpected WolframScript exit code: $verificationExitCode"
}

& $PythonExe (Join-Path $packageRoot 'tools\build_report.py')
if ($LASTEXITCODE -ne 0) {
    throw 'LaTeX result-fragment generation failed.'
}

$docsDirectory = Join-Path $packageRoot 'docs'
$outputDirectory = Join-Path $packageRoot 'output\pdf'
New-Item -ItemType Directory -Path $outputDirectory -Force | Out-Null
Push-Location $docsDirectory
try {
    & $LatexmkExe -norc -xelatex -interaction=nonstopmode -halt-on-error -synctex=1 "-outdir=$outputDirectory" 'verification_manual_v8.tex'
    if ($LASTEXITCODE -ne 0) {
        throw 'XeLaTeX compilation failed.'
    }
}
finally {
    Pop-Location
}

& $PythonExe (Join-Path $packageRoot 'tools\check_delivery.py')
if ($LASTEXITCODE -ne 0) {
    throw 'Delivery integrity check failed.'
}

$repositoryRoot = Split-Path -Parent $packageRoot
$policyCheck = Join-Path $repositoryRoot 'tools\check_no_manuscripts.py'
if (Test-Path -LiteralPath $policyCheck -PathType Leaf) {
    & $PythonExe $policyCheck --root $repositoryRoot
    if ($LASTEXITCODE -ne 0) {
        throw 'Repository manuscript-exclusion check failed.'
    }
}

if ($verificationExitCode -eq 2) {
    Write-Output 'BUILD COMPLETE: the manual was generated with manuscript WARN records.'
}
else {
    Write-Output 'BUILD COMPLETE: all recorded checks passed.'
}
