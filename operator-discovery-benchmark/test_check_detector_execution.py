import json
from pathlib import Path
import shutil
import tempfile
import unittest
import check_detector_execution as C
FIXTURE=C.BASE/'detector-performance-results/integrated-transfer-001'

class ExecutionTests(unittest.TestCase):
    def copy(self,tmp):
        p=Path(tmp)/'run';shutil.copytree(FIXTURE,p);return p
    def save(self,p,v):p.write_text(json.dumps(v,sort_keys=True,indent=2))
    def reseal_job(self,p,j):
        job=p/'jobs/final-0000.json';self.save(job,j);receipts=C.read(p/'final_receipts.json');receipts['results'][0]['value']['sha256']=C.sha(job);self.save(p/'final_receipts.json',receipts)
        r=C.read(p/'receipt.json');r['files_sha256']['jobs/final-0000.json']=C.sha(job);r['files_sha256']['final_receipts.json']=C.sha(p/'final_receipts.json');self.save(p/'receipt.json',r)
    def test_old_snapshot_preserved(self):
        a=C.audit(FIXTURE);self.assertTrue(a['all_passed']);self.assertEqual(a['accepted_finite_checks'],2);self.assertFalse(a['live_source_match_required'])
    def test_search_receipt_schema(self):
        path=C.BASE/'detector-performance-results/integrated-search-002'
        a=C.audit(path);self.assertEqual(a['training_finite_checks'],1);self.assertEqual(a['accepted_finite_checks'],2)
    def test_resealed_weights_and_promotion(self):
        for kind in ['weights','promotion']:
            with tempfile.TemporaryDirectory()as tmp:
                p=self.copy(tmp);j=C.read(p/'jobs/final-0000.json')
                if kind=='weights':j['synthesis']['weights']['square_weights'][22]='2';j['weights_sha256']=C.digest(j['synthesis']['weights'])
                else:j['RH_proved']=True
                self.reseal_job(p,j)
                with self.subTest(kind=kind),self.assertRaises(ValueError):C.audit(p)
    def test_snapshot_and_order_tamper(self):
        for kind in ['source','order']:
            with tempfile.TemporaryDirectory()as tmp:
                p=self.copy(tmp)
                if kind=='source':(p/'frozen_source/run_detector.py').write_text('# changed snapshot\n')
                else:
                    d=C.read(p/'final_receipts.json');d['results'].reverse();self.save(p/'final_receipts.json',d);r=C.read(p/'receipt.json');r['files_sha256']['final_receipts.json']=C.sha(p/'final_receipts.json');self.save(p/'receipt.json',r)
                with self.subTest(kind=kind),self.assertRaises(ValueError):C.audit(p)

if __name__=='__main__':unittest.main()
