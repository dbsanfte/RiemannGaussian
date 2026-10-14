import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import run_mobius_centered_storage_074 as R


class StudyIntegrationTests(unittest.TestCase):
    def test_new_grammar_candidate_is_independently_admitted_and_evaluated(self):
        data=R.SEARCH.B.make_data(R.SPEC['source'],list(range(1,97)))
        with tempfile.TemporaryDirectory() as directory:
            out=Path(directory)
            discovery=dict(data,rows=data['rows'][:32])
            adaptation=dict(data,rows=data['rows'][:64])
            for name,value in (('learning_discovery.json',discovery),
                               ('learning_adaptation.json',adaptation),('final_data.json',data)):
                R.write(out/name,value)
            spec=dict(R.SPEC,adaptive_rounds=2,final_children=[65,96])
            with patch.multiple(R,OUT=out,SPEC=spec):
                task=('centered_high','9/8')
                fitted=R.fit_task(task)
                frozen=(out/fitted['file']).read_bytes()
                final=R.final_task(task)
                self.assertEqual(frozen,(out/fitted['file']).read_bytes())
                certificate=json.loads(frozen)
                self.assertTrue(all(a['grammar']['verified'] for a in certificate['admissions']))
                self.assertTrue(all(a['candidate']['verified'] for a in certificate['admissions']))
                result=json.loads((out/final['file']).read_text())
                self.assertEqual(result['learned']['scales_checked'],32)
                self.assertFalse(result['uniform_recurrence_proved'])
                self.assertFalse(result['RH_proved'])


if __name__=='__main__':unittest.main()
