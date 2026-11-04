import unittest
from ocr_accuracy import strict_number, NumberVerifier
class AccuracyTests(unittest.TestCase):
    def test_full_number_only(self):
        for text in ('abc12','1.2.3','12 34','OO'):
            self.assertEqual(strict_number(text),'')
        self.assertEqual(strict_number('12.3m'),'12.3')
    def test_disagreement_and_change(self):
        v=NumberVerifier()
        self.assertEqual(v.update([('8',.99),('3',.99)],.7)[0],'')
        self.assertEqual(v.update([('8',.99)]*2,.7)[0],'')
        self.assertEqual(v.update([('8',.99)]*2,.7)[0],'8')
        self.assertEqual(v.update([('2',.99)]*2,.7)[0],'')
        self.assertEqual(v.update([('',.1)]*2,.7)[0],'')
        self.assertEqual(v.update([('8',.99)]*2,.7)[0],'')
