import copy
import hashlib
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import potential_candidate_discovery as D
import potential_candidate_language as L
import run_potential_candidate_discovery as W


def evidence(record, constant='1', failures=0):
    return dict(id=record['id'],status='available',initial=dict(X=1,E='1',V='0',W='1'),
                constants={str(q):constant for q in D.LEVELS},
                validation_scores=[dict(passed=False)]*failures)


class WorkflowTests(unittest.TestCase):
    def meter(self):
        return L.Meter(1000000)

    def test_balanced_structural_initial_batch_is_response_free_and_typed(self):
        meter=self.meter(); batch=D.generate_initial(meter)
        self.assertEqual(batch['records'][0]['program'],dict(states=[]))
        self.assertFalse(batch['response_values_used'])
        for family in D.FAMILIES:
            self.assertEqual(sum(r['family']==family for r in batch['records']),8)
        for r in batch['records']:
            L.validate_candidate(r['program'],meter)
        self.assertTrue(any(a['reason']=='duplicate_syntax' for a in batch['attempts']))

    def test_root_and_moving_prime_banks_reach_real_program_payloads(self):
        batch=D.generate_initial(self.meter())
        for order in (2,3,6):
            self.assertTrue(any(r['origin'].get('order')==order for r in batch['records']))
        banks=[r['program']['states'][0]['tree'] for r in batch['records'] if r['family']=='prime_bank']
        self.assertTrue(banks)
        self.assertTrue(all(t[0]=='sum' and t[1]=='p' for t in banks))
        self.assertTrue(any(t[4][2][0]=='add' for t in banks))

    def test_mutations_change_structure_and_preserve_parents(self):
        meter=self.meter(); initial=D.generate_initial(meter)['records']
        parents=D.choose(initial,[evidence(r) for r in initial],meter)
        original=copy.deepcopy(parents)
        batch=D.generate_mutations(parents,initial,meter)
        self.assertEqual(parents,original)
        self.assertGreater(len(batch['records']),0); self.assertLessEqual(len(batch['records']),32)
        self.assertEqual({r['origin']['kind'] for r in batch['records']},
                         {'floor_remap','moving_shift','coprime_guard','root_mixture','source_product','parent_mixture'})
        old={D.canonical(r['program']) for r in initial}
        for r in batch['records']:
            self.assertNotIn(D.canonical(r['program']),old)
            L.validate_candidate(r['program'],meter)

    def test_initial_cost_and_failures_affect_selection_but_baseline_does_not_take_a_structural_slot(self):
        meter=self.meter(); records=D.generate_initial(meter)['records']
        rows=[evidence(r,'0' if r['id']==0 else '1') for r in records]
        chosen=D.choose(records,rows,meter)
        self.assertNotIn(0,[r['id'] for r in chosen])
        self.assertEqual({r['family'] for r in chosen},set(D.FAMILIES))
        first=chosen[0]['id']; next(e for e in rows if e['id']==first)['validation_scores']=[dict(passed=False)]
        self.assertNotEqual(D.choose(records,rows,meter)[0]['id'],first)
        self.assertEqual(D.choose(records,rows,meter),W._independent_choose(records,rows,meter))

    def test_exact_fitted_constants_do_not_refit_during_validation(self):
        meter=self.meter(); cases=[dict(X=1,innovation='1/2'),dict(X=8,innovation='7/3')]
        constants=D.fit_constants(cases,meter); fixed=copy.deepcopy(constants)
        larger=[dict(X=16,innovation='100')]
        scores=D.assess(larger,constants,meter)
        self.assertEqual(constants,fixed)
        self.assertTrue(all(not s['passed'] for s in scores))
        self.assertEqual(constants,W._independent_constants(cases,meter))
        self.assertEqual(scores,W._independent_scores(larger,constants,meter))

    def test_empty_or_negative_training_innovations_keep_nonnegative_constants(self):
        constants=D.fit_constants([dict(X=1,innovation='-1')],self.meter())
        self.assertEqual(set(constants.values()),{'0'})

    def test_train_file_exists_before_any_validation_and_constants_are_unchanged(self):
        record=dict(id=0,program=dict(states=[])); events=[]
        with tempfile.TemporaryDirectory() as temporary:
            path=Path(temporary)
            def fake(r,values,scales,meter,include_initial=False):
                events.append(tuple(scales))
                if tuple(scales)==D.VALIDATION:
                    self.assertTrue((path/'tiny_training.json').exists())
                result=dict(id=r['id'],status='available',cases=[dict(X=X,innovation='1') for X in scales])
                if include_initial: result['initial']=dict(X=1,E='1',V='0',W='1')
                return result
            with patch.object(W,'evaluate_one',side_effect=fake):
                rows=W.discovery_round(path,'tiny',[record],[],self.meter(),self.meter())
            self.assertEqual(events,[D.TRAIN,D.VALIDATION])
            self.assertEqual(rows[0]['constants'],W.read(path/'tiny_training.json')[0]['constants'])

    def test_no_hash_creation_during_generation_selection_or_proof_queue(self):
        meter=self.meter()
        with patch.object(hashlib,'sha256',side_effect=AssertionError('unnecessary hash')):
            records=D.generate_initial(meter)['records']
            selected=D.choose(records,[evidence(r) for r in records],meter)
            D.generate_mutations(selected,records,meter)
            for r in selected:
                queue=D.obligation(r)
                self.assertTrue(all(queue[k] is False for k in D.FLAGS))
                self.assertEqual(queue['program'],r['program'])

    def test_complete_work_allocation_and_no_synthetic_reset(self):
        self.assertEqual(sum(W.ALLOCATIONS.values()),450000000)
        stdout='\n'.join('SYNTHETIC_WORK module='+name+' operations=100' for name in W.TESTS[:2])
        self.assertEqual(W.synthetic_receipt(stdout)['total'],W.DEVELOPMENT_OPERATIONS+W.ROOT_RESERVE+200)
        with self.assertRaises(OverflowError):
            W.synthetic_receipt(stdout.replace('=100','=25000000'))

    def test_artifacts_are_write_once(self):
        with tempfile.TemporaryDirectory() as temporary:
            path=Path(temporary)/'batch.json'
            W.write(path,dict(candidate=1))
            with self.assertRaises(FileExistsError):
                W.write(path,dict(candidate=2))


if __name__=='__main__':
    unittest.main()
