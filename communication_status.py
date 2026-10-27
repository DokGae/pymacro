"""Plain-language presentation; never changes condition evaluation."""
COLORS={'ok':'#22863a','waiting':'#a66a00','offline':'#c62828'}


def connection_presentation(client,source,available=None):
    data,status=client.snapshot(source)
    if data is not None:
        if available is False:return 'waiting','연결됨 · 데이터를 받고 있지만 선택한 항목을 확인할 수 없습니다.'
        return 'ok','정상 · 모니터 데이터를 계속 받고 있습니다.'
    if client.transport_connected():
        if status.startswith('다른 프로그램'):
            return 'waiting','연결됨 · 프로그램 ID가 다릅니다. 모니터와 같은 ID를 선택하세요.'
        return 'waiting','연결됨 · 모니터 데이터가 도착하기를 기다립니다.'
    return 'offline','연결 안 됨 · 모니터 실행 여부와 통신 포트를 확인하세요.'


def show_connection(label,client,source,available=None):
    level,text=connection_presentation(client,source,available)
    label.setText(text);label.setStyleSheet(f'color:{COLORS[level]};font-weight:bold;')


def missing_item_message(key,registered=False):
    if key.startswith(('내.스킬.','내.스티그마.')):
        return ('스킬 레벨을 아직 확인하지 못했습니다. 게임 접속 후 스킬 목록 수신을 기다리세요.' if registered else
                '이 스킬의 레벨이 전송되지 않습니다. 모니터 스킬관리에서 ‘레벨 전송’을 체크하세요.')
    return ('이 항목의 전송이 꺼져 있거나 게임 정보를 아직 감지하지 못했습니다. 모니터에서 해당 항목을 확인하세요.' if registered else
            '이 이름의 항목이 없습니다. 모니터의 전송 체크와 항목 이름을 확인하세요.')
