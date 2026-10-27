import time
import unittest
from external_state import StateClient
from communication_status import connection_presentation,missing_item_message


class CommunicationStatusTests(unittest.TestCase):
    def test_red_offline_yellow_transport_green_fresh(self):
        c=StateClient()
        self.assertEqual(connection_presentation(c,'monitor')[0],'offline')
        c._socket=object()
        self.assertEqual(connection_presentation(c,'monitor')[0],'waiting')
        c._data=dict(source='monitor',values={'level':0});c._received_at=time.monotonic()
        self.assertEqual(connection_presentation(c,'monitor',True)[0],'ok')
        self.assertEqual(connection_presentation(c,'monitor',False)[0],'waiting')
        self.assertEqual(connection_presentation(c,'wrong')[0],'waiting')
        c._received_at=0
        self.assertEqual(connection_presentation(c,'monitor')[0],'waiting')
        c._socket=None
        self.assertEqual(connection_presentation(c,'monitor')[0],'offline')

    def test_messages_do_not_claim_unknown_is_false(self):
        self.assertIn('레벨 전송',missing_item_message('내.스킬.절단의맹타'))
        self.assertIn('목록 수신',missing_item_message('내.스킬.절단의맹타',True))
        c=StateClient();c._data=dict(source='monitor',values={'false':False,'zero':0},unavailable_keys=['wait']);c._received_at=time.monotonic()
        self.assertEqual(c.lookup('monitor','false')[:2],(True,False))
        self.assertEqual(c.lookup('monitor','zero')[:2],(True,0))
        self.assertFalse(c.lookup('monitor','wait')[0]);self.assertFalse(c.lookup('monitor','missing')[0])


if __name__=='__main__':unittest.main()
