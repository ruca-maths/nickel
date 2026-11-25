# 親機オーケストレータの常駐用ラッパー。異常終了したら 5 分後に起動し直す。
# 止めるときはリポジトリ直下に STOP ファイルを作る（このラッパーも止まる）。
$ErrorActionPreference = "Continue"
Set-Location (Join-Path $PSScriptRoot "..")
$env:PYTHONIOENCODING = "utf-8"
$env:Path = "$HOME\.local\bin;$env:Path"
$py = if ($env:RESEARCH_PYTHON) { $env:RESEARCH_PYTHON } else { "python" }
New-Item -ItemType Directory -Force state\logs | Out-Null
while (-not (Test-Path STOP)) {
    & $py -u core/orchestrator.py --forever 2>&1 | Tee-Object -FilePath state\logs\orchestrator.log -Append
    if ($LASTEXITCODE -eq 3) { Write-Host "二重起動のため終了します"; break }
    if (Test-Path STOP) { break }
    Write-Host "オーケストレータが終了しました（rc=$LASTEXITCODE）。5 分後に再起動します"
    Start-Sleep -Seconds 300
}
Write-Host "STOP ファイルがあるので停止しました: $(Get-Content STOP -Raw)"
