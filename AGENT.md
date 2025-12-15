### Modal/Non-modal policy
- 새로 만드는 대화상자/모달은 기본적으로 `NonModal` + `WindowStaysOnTopHint=False`로 설정한다. 메인 GUI, 이미지 뷰어 등 다른 창과 동시 사용 가능해야 한다.
- 기존/신규 모달에서 부모 창을 막지 않도록 `setModal(False)` + `setWindowModality(QtCore.Qt.WindowModality.NonModal)`를 우선 적용한다.
- 특별히 항상 위에 떠야 하는 케이스가 아니면 `WindowStaysOnTopHint`를 끄고, 필요 시에도 최소한으로만 켠다.
