param(
    [string]$LatexmkExe = 'C:\Software\texlive\2025\bin\windows\latexmk.exe'
)

$ErrorActionPreference = 'Stop'
$packageRoot = Split-Path -Parent (Split-Path -Parent $MyInvocation.MyCommand.Path)
$docsDirectory = Join-Path $packageRoot 'docs'
$outputDirectory = Join-Path $packageRoot 'output\pdf'
$sourceDateEpoch = '1789084800'

New-Item -ItemType Directory -Path $outputDirectory -Force | Out-Null

$savedSourceDateEpoch = $env:SOURCE_DATE_EPOCH
$savedForceSourceDate = $env:FORCE_SOURCE_DATE
$savedTimezone = $env:TZ

try {
    # Fix PDF creation metadata so rebuilding in another checkout is byte-for-byte stable.
    $env:SOURCE_DATE_EPOCH = $sourceDateEpoch
    $env:FORCE_SOURCE_DATE = '1'
    $env:TZ = 'UTC'

    foreach ($suffix in @('aux', 'fdb_latexmk', 'fls', 'out', 'xdv', 'synctex.gz')) {
        $path = Join-Path $outputDirectory "verification_manual_v9.$suffix"
        if (Test-Path -LiteralPath $path -PathType Leaf) {
            Remove-Item -LiteralPath $path -Force
        }
    }

    Push-Location $docsDirectory
    try {
        & $LatexmkExe -norc -g -xelatex -interaction=nonstopmode -halt-on-error `
            -synctex=1 "-outdir=$outputDirectory" 'verification_manual_v9.tex'
        if ($LASTEXITCODE -ne 0) {
            throw 'Verification-manual XeLaTeX build failed.'
        }
    }
    finally {
        Pop-Location
    }
}
finally {
    if ($null -eq $savedSourceDateEpoch) {
        Remove-Item Env:SOURCE_DATE_EPOCH -ErrorAction SilentlyContinue
    }
    else {
        $env:SOURCE_DATE_EPOCH = $savedSourceDateEpoch
    }
    if ($null -eq $savedForceSourceDate) {
        Remove-Item Env:FORCE_SOURCE_DATE -ErrorAction SilentlyContinue
    }
    else {
        $env:FORCE_SOURCE_DATE = $savedForceSourceDate
    }
    if ($null -eq $savedTimezone) {
        Remove-Item Env:TZ -ErrorAction SilentlyContinue
    }
    else {
        $env:TZ = $savedTimezone
    }
}
