"""Synthetic search and signed-Haar semantics; no selected-source observations."""
from copy import deepcopy
from pathlib import Path
import json
import time
import unittest
import numpy as np

import centered_mobius_search_041 as P


def state(values):
    J=np.array(values,dtype=float)
    return dict(J=J,a=np.r_[0.,np.diff(J)],r='1/3',q=2)


class HaarSearch(unittest.TestCase):
    def test_exact_coordinate_aliases_and_arbitrary_source_rational(self):
        g=P.dictionary('123/257')
        self.assertEqual(g['raw_program_count'],288)
        self.assertEqual(g['canonical_program_count'],216)
        self.assertEqual(len(g['exact_aliases']),72)
        self.assertEqual(len({P.canonical_key(p) for p in g['programs']}),216)
        self.assertTrue(any(p['lambda'].get('exponent')=='-123/257' for p in g['programs']))

    def test_complete_haar_identity_and_nonzero_signed_cross(self):
        s=state([0]+[(-1)**n*(n%7)+n/3 for n in range(1,160)])
        d=P.prefix_squares(s['a'])
        for m in (2,3,5,7):
            obs=P.block(s,m,8,d)
            self.assertAlmostEqual(obs['identity_residual'],0,places=12)
            self.assertGreater(obs['within_cell_variance'],0)
            self.assertNotEqual(obs['gram'][0][1],0)
            p=dict(id='toy',m=m,**{'lambda':dict(kind='rational',value='3/2')},rho='1/2',delta='1/4',C='1')
            J=s['J'][8:16];A=s['J'][8*m:16*m].reshape(8,m).mean(axis=1);I=A-1.5*J
            direct=(3*np.dot(J,I)+1.25*np.dot(I,I)-(m/2-2.25)*np.dot(J,J))/64-obs['D']
            self.assertAlmostEqual(P.evaluate(p,[obs],'1/3')[0]['defect'],direct,places=9)

    def test_positive_prefix_control_rejects_whole_dictionary(self):
        s=state(range(2*7*max(P.TRAIN_SCALES)))
        found=P.search(P.training_evidence(s))
        self.assertEqual(found['coverage']['training_passes'],0)
        self.assertEqual(found['coverage']['training_refuted'],216)
        self.assertEqual(len(found['candidates']),1)
        self.assertFalse(found['uniform_covariance_bound_proved'])

    def test_only_training_partition_can_select(self):
        s=state([0]+[(-1)**n for n in range(1,2*7*max(P.TRAIN_SCALES))])
        evidence=P.training_evidence(s)
        original=P.search(evidence)
        altered=deepcopy(evidence);altered['blocks'].append(deepcopy(altered['blocks'][0]))
        with self.assertRaises(ValueError):P.search(altered)
        altered=deepcopy(evidence);altered['blocks'][0]['X']=123456
        with self.assertRaises(ValueError):P.search(altered)
        self.assertTrue(all(p['id'] in {r['id'] for r in original['training_assessments']} for p in original['candidates']))
        self.assertFalse(original['selection_uses_other_scales'])
        self.assertFalse(original['constants_fitted'])

    def test_missing_child_or_forcing_boundary_rejected(self):
        s=state(range(31));d=P.prefix_squares(s['a'])
        with self.assertRaises(ValueError):P.block(s,2,8,d)
        with self.assertRaises(ValueError):P.block(s,True,4,d)
        bad=s['a'].copy();bad[0]=1
        with self.assertRaises(ValueError):P.prefix_squares(bad)


if __name__=='__main__':
    start=time.monotonic()
    result=unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(HaarSearch))
    record=dict(returncode=0 if result.wasSuccessful() else 1,tests=result.testsRun,
                failures=len(result.failures),errors=len(result.errors),elapsed_seconds=time.monotonic()-start,
                exposure='synthetic signed/positive integer prefixes and exact rational program syntax only')
    path=Path(__file__).with_name('centered_mobius_search_041_development.json')
    receipt=json.loads(path.read_text()) if path.exists() else dict(schema='owned-development-v1',invocations=[])
    receipt['invocations'].append(record);path.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(record));raise SystemExit(record['returncode'])
