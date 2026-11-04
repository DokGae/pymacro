"""Small-number preprocessing and conservative cross-checks."""
import re
import cv2

def strict_number(text):
    text = text.strip().replace('．','.')
    match = re.fullmatch(r'(\d+(?:\.\d+)?)\s*[mM]?',text)
    return match.group(1) if match else ''

def views(frame):
    # Keep the selected bounds: enlargement cannot recover clipped characters.
    scale = max(1.,48/frame.shape[0])
    frame = cv2.resize(frame,None,fx=scale,fy=scale,interpolation=cv2.INTER_CUBIC)
    gray = cv2.cvtColor(frame,cv2.COLOR_BGR2GRAY)
    if gray.mean()<127: gray=255-gray
    gray = cv2.copyMakeBorder(gray,5,5,5,5,cv2.BORDER_CONSTANT,value=255)
    _, binary=cv2.threshold(gray,0,255,cv2.THRESH_BINARY|cv2.THRESH_OTSU)
    return [cv2.cvtColor(v,cv2.COLOR_GRAY2BGR) for v in (gray,binary)]

class NumberVerifier:
    def __init__(self):
        self.pending=''; self.count=0
    def update(self,reads,threshold):
        candidates=[strict_number(text) if score>=threshold else '' for text,score in reads]
        value=candidates[0] if len(candidates)==2 and candidates[0] and candidates[0]==candidates[1] else ''
        if not value:
            self.pending=''; self.count=0
            return '', '두 영상 불일치 또는 신뢰도 부족'
        self.count=self.count+1 if value==self.pending else 1
        self.pending=value
        return (value,'확인됨') if self.count>=2 else ('','다음 프레임 확인 중')
