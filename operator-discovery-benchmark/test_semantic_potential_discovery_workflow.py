import atexit
from copy import deepcopy
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import potential_candidate_language as L
import semantic_potential_discovery as D
import run_semantic_potential_discovery as W

WORK=L.Meter(5000000)
METERS=[WORK]
atexit.register(lambda: print('SYNTHETIC_WORK module=test_semantic_potential_discovery_workflow operations='+str(sum(m.operations for m in METERS))))


def evidence(record,constant='1',failures=0):
    return dict(id=record['id'],status='available',initial=dict(X=1,E='1',V='0',W='1'),
                constants={str(q):constant for q in D.LEVELS},
                validation_scores=[dict(passed=False)]*failures,
                diagnostics=dict(status='available',cases=[],scores=[]))


class WorkflowTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.batch=D.generate_initial(WORK)
        cls.records=cls.batch['records']
        cls.evidence=[evidence(r) for r in cls.records]
        cls.parents=D.choose(cls.records,cls.evidence,WORK)
        cls.mutations=D.generate_mutations(cls.parents,cls.records,WORK)

    def test_real_generated_structures_are_typed_and_keep_fractional_roots(self):
        self.assertEqual(len(self.records),41)
        self.assertEqual({r['family'] for r in self.records[1:]},set(D.FAMILIES))
        self.assertEqual({r['origin'].get('order') for r in self.records if 'order' in r['origin']},{2,3,6})
        self.assertFalse(self.batch['response_values_used'])
        for r in self.records+self.mutations['records']:
            L.validate_candidate(r['program'],WORK)
            self.assertLessEqual(len(r['exposure']['diagnostic_scales']),2)
            self.assertTrue(all(x<=D.DISCOVERY_MAX for x in r['exposure']['diagnostic_scales']))
            self.assertFalse(r['exposure']['response_values_used'])

    def test_mutations_rewrite_payloads_without_editing_parents(self):
        self.assertLessEqual(len(self.mutations['records']),24)
        self.assertEqual({r['origin']['kind'] for r in self.mutations['records']},
                         {'factor_in_summand','signed_pair','gcd_conditioned_mix','quotient_commutator'})
        originals=[r['program'] for r in self.records]
        self.assertTrue(all(r['program'] not in originals for r in self.mutations['records']))
        self.assertTrue(all(r in self.records for r in self.parents))
        factor_records=[r for r in self.mutations['records'] if r['origin']['kind']=='factor_in_summand']
        self.assertTrue(any(r['origin']['existing_sum_rewritten'] for r in factor_records))

    def test_mechanism_slots_and_independent_selection_avoid_calibration_monopoly(self):
        chosen=D.choose(self.records,self.evidence,WORK)
        self.assertEqual(chosen,W._independent_choose(self.records,self.evidence,WORK))
        self.assertNotIn(0,[r['id'] for r in chosen])
        self.assertLessEqual(sum(r['semantics']['mechanism'] in D.CALIBRATION for r in chosen),2)
        self.assertTrue(any(r['semantics']['mechanism']=='coupled_sum' for r in chosen))
        self.assertTrue(any(r['semantics']['mechanism']=='coupled_bank' for r in chosen))
        changed=deepcopy(self.evidence)
        for e in changed:
            e['diagnostics']['scores']=[dict(passed=False)]*100
        self.assertEqual(chosen,D.choose(self.records,changed,WORK))

    def test_squarefree_masks_do_not_consume_all_slots_even_with_smaller_finite_constants(self):
        rows=deepcopy(self.evidence)
        by_id={r['id']:r for r in self.records}
        for e in rows:
            if by_id[e['id']]['semantics']['mechanism'] in D.CALIBRATION:
                e['constants']={str(q):'0' for q in D.LEVELS}
        chosen=D.choose(self.records,rows,WORK)
        self.assertGreater(len(chosen),2)
        self.assertLessEqual(sum(r['semantics']['mechanism'] in D.CALIBRATION for r in chosen),2)
        self.assertEqual(chosen,W._independent_choose(self.records,rows,WORK))

    def test_masked_mixed_core_keeps_its_structural_slot(self):
        t=D.variable('t')
        tree=D.product(['x',t],D.add(D.prefix(t),D.prefix(D.floor_div(t,D.integer(2)))))
        row=D.record(100,0,'source_mixture',tree,dict(kind='synthetic_masked_mix'),WORK)
        self.assertEqual(row['semantics']['mechanism'],'mask')
        self.assertEqual(D.selection_mechanism(row),'coupled_sum')
        rows=self.records+[row]; values=self.evidence+[evidence(row,'0')]
        self.assertEqual(D.choose(rows,values,WORK),W._independent_choose(rows,values,WORK))

    def test_gcd_value_does_not_inherit_radical_mask_identity(self):
        X,t=D.variable('X'),D.variable('t')
        modulus=D.root(X,2)
        numeric=D.state_program(['embed',['gcd',t,modulus]])
        masked=D.state_program(['guard',['eq',['gcd',t,modulus],D.integer(1)],D.prefix(t)])
        a=D.selectors(numeric,WORK)[0]; b=D.selectors(masked,WORK)[0]
        self.assertEqual(a['kind'],'gcd_modulus'); self.assertEqual(b['kind'],'coprime_radical')
        self.assertEqual(D.selector_value(a,16,WORK),4)
        self.assertEqual(D.selector_value(b,16,WORK),2)
        self.assertEqual(D.selector_value(b,64,WORK),2)

    def test_max_and_prime_domains_use_effective_transitions(self):
        X=D.variable('X')
        modulus=dict(kind='residue_modulus',tree=['max',D.integer(2),D.root(X,6)])
        self.assertEqual(D.selector_value(modulus,64,WORK),2)
        self.assertEqual(D.selector_value(modulus,728,WORK),2)
        self.assertEqual(D.selector_value(modulus,729,WORK),3)
        primes=dict(kind='prime_bank',tree=D.root(X,3),lower=D.integer(2))
        self.assertEqual(D.selector_value(primes,64,WORK),[2,3])
        self.assertEqual(D.selector_value(primes,124,WORK),[2,3])
        self.assertEqual(D.selector_value(primes,125,WORK),[2,3,5])
        mu_bank=dict(kind='mobius_bank',tree=D.root(X,6),lower=D.integer(1))
        self.assertEqual(D.selector_value(mu_bank,4095,WORK),[1,2,3])
        self.assertEqual(D.selector_value(mu_bank,4096,WORK),[1,2,3])

    def test_unaffordable_and_raw_selector_coverage_remains_explicit(self):
        X,t=D.variable('X'),D.variable('t')
        candidate=D.state_program(['sum','d',D.integer(1),D.root(X,6),['x',D.variable('d')]])
        plan=D.exposure_plan(candidate,WORK)
        self.assertTrue(any(r['next_transition_status']=='unexposed_beyond_discovery_cap' for r in plan['selectors']))
        raw=D.exposure_plan(D.state_program(['x',D.root(t,6)]),WORK)
        self.assertTrue(all(r['next_transition_status']=='raw_range_only' for r in raw['selectors']))
        oversized=D.state_program(['sum','d',D.integer(1),['imul',X,D.integer(5000)],['q','1']])
        capped=D.exposure_plan(oversized,WORK)
        self.assertEqual(capped['selectors'][0]['next_transition_status'],'unexposed_selector_domain_cap')
        with self.assertRaises(D.SelectorDomainCap): D._floor_root(2,1000000000,1,WORK)
        exhausted=L.Meter(1); METERS.append(exhausted)
        with self.assertRaises(OverflowError): D.exposure_plan(candidate,exhausted)
        shifted=D.state_program(D.prefix(['max',D.integer(0),['isub',t,D.root(X,3)]]))
        shift_plan=D.exposure_plan(shifted,WORK)
        self.assertTrue(any(r['descriptor']['kind']=='scale_root_range' for r in shift_plan['selectors']))
        nested=D.state_program(D.prefix(D.root(D.floor_div(t,D.integer(2)),3)))
        nested_plan=D.exposure_plan(nested,WORK)
        self.assertEqual(nested_plan['selectors'][0]['next_transition_status'],'unsupported_selector')

    def test_skipped_nonmonotone_transition_is_not_claimed_exposed(self):
        X,t=D.variable('X'),D.variable('t')
        modulus=['iadd',D.integer(2),['imod',X,D.integer(2)]]
        tree=['guard',['eq',['imod',t,modulus],D.integer(0)],D.prefix(t)]
        plan=D.exposure_plan(D.state_program(tree),WORK)
        row=plan['selectors'][0]
        self.assertEqual(row['next_transition'],1025)
        self.assertEqual(row['transition_value'],3)
        self.assertEqual(row['next_transition_status'],'unexposed_diagnostic_quota_or_skipped_regime')

    def test_training_is_saved_before_validation_and_diagnostic_responses(self):
        record=dict(id=0,program=dict(states=[]),exposure=dict(diagnostic_scales=[900]))
        events=[]
        with tempfile.TemporaryDirectory() as temp:
            path=Path(temp)
            def fake(r,values,scales,meter,include_initial=False):
                if tuple(scales)!=D.TRAIN: self.assertTrue((path/'tiny_training.json').exists())
                events.append(tuple(scales))
                out=dict(id=r['id'],status='available',cases=[dict(X=x,innovation='1') for x in scales])
                if include_initial: out['initial']=dict(X=1,E='1',V='0',W='1')
                return out
            with patch.object(W,'evaluate_one',side_effect=fake):
                rows=W.discovery_round(path,'tiny',[record],[],WORK,WORK)
            self.assertEqual(events,[D.TRAIN,D.VALIDATION,(900,)])
            self.assertEqual(rows[0]['constants'],W.read(path/'tiny_training.json')[0]['constants'])
            self.assertEqual(len(rows[0]['diagnostics']['scores']),len(D.LEVELS))

    def test_complete_reservation_receipts_and_write_once_results(self):
        self.assertEqual(sum(W.ALLOCATIONS.values()),450000000)
        stdout='\n'.join('SYNTHETIC_WORK module='+name+' operations=100' for name in W.TESTS)
        self.assertEqual(W.synthetic_receipt(stdout)['total'],W.DEVELOPMENT_OPERATIONS+W.ROOT_RESERVE+100*len(W.TESTS))
        with tempfile.TemporaryDirectory() as temp:
            path=Path(temp)/'record.json'; W.write(path,dict(x=1))
            with self.assertRaises(FileExistsError): W.write(path,dict(x=2))

    def test_all_quantified_obligations_retain_the_target_and_false_theorem_flags(self):
        for r in self.parents:
            item=D.obligation(r)
            self.assertEqual(item['program'],r['program'])
            self.assertIn('independent of dyadic',item['claim'])
            self.assertTrue(all(item[k] is False for k in D.FLAGS))
            self.assertTrue(item['analytic_tasks'])


if __name__=='__main__': unittest.main()
