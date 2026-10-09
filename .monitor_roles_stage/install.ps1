$monitorRoot = 'C:\Users\goldang\Downloads\notmeter\newmonitor_packet\leesangjin_monitor'
$stageRoot = 'D:\Ion\macro\.monitor_roles_stage'
foreach ($name in @('effect_manager.py','effect_drafts.py','tcp_state_server.py','settings_window.py')) {
    Copy-Item -LiteralPath (Join-Path $monitorRoot $name) -Destination (Join-Path $monitorRoot ($name + '.before-role-messages.bak')) -Force -ErrorAction Stop
    Copy-Item -LiteralPath (Join-Path $stageRoot $name) -Destination (Join-Path $monitorRoot $name) -Force -ErrorAction Stop
}
Copy-Item -LiteralPath (Join-Path $monitorRoot 'packetcore\catalog.py') -Destination (Join-Path $monitorRoot 'packetcore\catalog.py.before-role-messages.bak') -Force -ErrorAction Stop
Copy-Item -LiteralPath (Join-Path $stageRoot 'catalog.py') -Destination (Join-Path $monitorRoot 'packetcore\catalog.py') -Force -ErrorAction Stop
Write-Output 'Installed color fix and separate role messages.'
Get-CimInstance Win32_Process | Where-Object { $_.Name -match 'python|LeeSangJinMonitor' } | Select-Object ProcessId,Name,ExecutablePath,CommandLine | Format-List
