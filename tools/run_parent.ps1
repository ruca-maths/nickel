# Keeps the parent orchestrator running. Restarts it 5 minutes after an abnormal exit.
# To stop: create a file named STOP at the repository root (this wrapper stops too).
# ASCII only on purpose: Windows PowerShell 5.1 reads BOM-less UTF-8 scripts as the ANSI code page.
$ErrorActionPreference = "Continue"
Set-Location (Join-Path $PSScriptRoot "..")
$env:PYTHONIOENCODING = "utf-8"
[Console]::OutputEncoding = [System.Text.Encoding]::UTF8  # show the orchestrator's UTF-8 output correctly
$env:Path = "$HOME\.local\bin;$env:Path"
$py = if ($env:RESEARCH_PYTHON) { $env:RESEARCH_PYTHON } else { "python" }
New-Item -ItemType Directory -Force state\logs | Out-Null
while (-not (Test-Path STOP)) {
    # the orchestrator writes state\logs\orchestrator.log itself (UTF-8)
    & $py -u core/orchestrator.py --forever
    if ($LASTEXITCODE -eq 3) { Write-Host "Another orchestrator is running in this clone. Exiting."; break }
    if (Test-Path STOP) { break }
    Write-Host "Orchestrator exited (rc=$LASTEXITCODE). Restarting in 5 minutes."
    Start-Sleep -Seconds 300
}
if (Test-Path STOP) { Write-Host ("Stopped because STOP exists: " + (Get-Content STOP -Raw)) }
