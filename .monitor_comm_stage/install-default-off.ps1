$monitorRoot = 'C:\Users\goldang\Downloads\notmeter\newmonitor_packet\leesangjin_monitor'
$stageRoot = 'D:\Ion\macro\.monitor_comm_stage'
foreach ($name in @('effect_manager.py','effect_drafts.py','tcp_state_server.py')) {
    Copy-Item -LiteralPath (Join-Path $stageRoot $name) -Destination (Join-Path $monitorRoot $name) -Force -ErrorAction Stop
}
Copy-Item -LiteralPath (Join-Path $stageRoot 'catalog.py') -Destination (Join-Path $monitorRoot 'packetcore\catalog.py') -Force -ErrorAction Stop
$settingsRoot = Join-Path $env:LOCALAPPDATA 'LeeSangJinMonitor'
$settingsFiles = @()
$defaultSettings = Join-Path $settingsRoot 'effect_names.json'
if (Test-Path -LiteralPath $defaultSettings) { $settingsFiles += Get-Item -LiteralPath $defaultSettings }
$presetRoot = Join-Path $settingsRoot 'presets'
if (Test-Path -LiteralPath $presetRoot) { $settingsFiles += Get-ChildItem -LiteralPath $presetRoot -Filter '*.json' -File }
foreach ($settingsFile in $settingsFiles) {
    $config = Get-Content -LiteralPath $settingsFile.FullName -Raw -Encoding UTF8 | ConvertFrom-Json -AsHashtable
    if ($config.version -ne 1 -or $null -eq $config.preview) { continue }
    Copy-Item -LiteralPath $settingsFile.FullName -Destination ($settingsFile.FullName + '.before-tcp-default-off.bak') -Force
    foreach ($effectConfig in $config.preview.Values) { $effectConfig['tcp_enabled'] = $false }
    $config | ConvertTo-Json -Depth 30 | Set-Content -LiteralPath $settingsFile.FullName -Encoding utf8
}
Write-Output 'Installed changes and reset existing effect transmission selections.'
