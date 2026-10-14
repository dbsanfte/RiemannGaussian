import copy
import unittest
from fractions import Fraction as Q

import mobius_residual_pairing_076 as P
import check_mobius_residual_pairing_076 as C
import check_mobius_count_control_076 as ROOT_CHECK


class ResidualPairing(unittest.TestCase):
    def test_stencil_conservation_boundaries_and_symbolic_cancellation(self):
        components=[dict(parent=80,weight={'1':'1','x':'1/3'}),
                    dict(parent=80,weight={'x':'-1/3'}),
                    dict(parent=40,weight={'1':'-2'}),dict(parent=3,weight={'y':'7'})]
        coefficient=P.materialize(P.stencil_intervals(components))
        self.assertEqual(C.verify_stencil(components,coefficient)['status'],'VERIFIED_IDENTITY')
        self.assertTrue(all('x' not in row and 'y' not in row for row in coefficient.values()))
        for n in range(17,21):self.assertEqual(coefficient[n],{'1':'-1'})
        changed=copy.deepcopy(coefficient);del changed[20]
        self.assertEqual(C.verify_stencil(components,changed)['status'],'INVALID')

    def test_fold_discovers_prime_pair_cancellation_without_mu(self):
        coefficient={1:{'x':'3/7'},7:{'x':'3/7'},49:{'x':'2'}}
        result=P.search_pairings(coefficient,{'x':['-2','3']},primes=(2,3,7),depth=1,width=2)
        self.assertEqual(result['prime_schedule'],[7])
        self.assertEqual(result['l1_upper'],'0')
        self.assertEqual(C.verify_fold(coefficient,result['coefficients'],7)['status'],'VERIFIED_IDENTITY')
        self.assertFalse(result['mobius_values_used_for_selection'])
        self.assertFalse(result['uniform_bound_proved'])

    def test_prime_folds_commute_keep_coprime_domain_and_unit(self):
        coefficient={n:{'1':str((n%5)+1)} for n in range(1,61)}
        left=P.fold(P.fold(coefficient,2),3,(2,))
        right=P.fold(P.fold(coefficient,3),2,(3,))
        self.assertEqual(left,right)
        self.assertTrue(all(n%2 and n%3 for n in left))
        self.assertIn(1,left)
        self.assertEqual(C.verify_fold(P.fold(coefficient,2),left,3,(2,))['status'],'VERIFIED_IDENTITY')

    def test_actual_mobius_value_preserved_after_two_folds(self):
        prefix,_=P.C.S.arithmetic(80,P.C.S.Meter())
        coefficient=P.materialize(P.stencil_intervals([dict(parent=320,weight={'1':'1'}),dict(parent=106,weight={'1':'2/3'})]))
        mu=[0]+[prefix[n]-prefix[n-1] for n in range(1,81)]
        def evaluate(c):return sum((Q(w['1'])*mu[n] for n,w in c.items()),Q(0))
        after=P.fold(P.fold(coefficient,2),5,(2,))
        self.assertEqual(evaluate(after),evaluate(coefficient))
        intervals={'1':['1','1']}
        self.assertLessEqual(abs(evaluate(after)),P.coefficient_bound(after,intervals))

    def test_square_energy_is_not_assumed_to_decrease(self):
        before={1:{'1':'1'},2:{'1':'-1'}}
        after=P.fold(before,2)
        self.assertEqual(after,{1:{'1':'2'}})
        self.assertGreater(sum(Q(v['1'])**2 for v in after.values()),sum(Q(v['1'])**2 for v in before.values()))
        self.assertEqual(P.coefficient_bound(after,{'1':['1','1']}),2)

    def test_fractional_compiler_counts_units_and_independent_roots(self):
        program=dict(spec=dict(grid=80,theta=['1/2','2/3','7/8'],multipliers=[2]),
                     atoms=[dict(column=0,gamma='1001/1000'),dict(column=1,gamma='1/3'),dict(column=2,gamma='0')],
                     operator=['2/3','-1/7','1/2'])
        row=dict(u=160,counts=[3,0,1])
        compiled=P.residual_components(program,row,[{40:1,32:2},{}])
        self.assertFalse(compiled['source_admission_supplied'])
        for token,d in compiled['token_definitions'].items():
            if d['kind']=='constant':continue
            lo,hi=ROOT_CHECK.count_enclosure(d['count'],Q(d['gamma']),20,ROOT_CHECK.Meter())
            self.assertEqual(compiled['token_intervals'][token],[str(1/hi),str(1/lo)])
        coefficient=P.materialize(P.stencil_intervals(compiled['components']))
        self.assertEqual(C.verify_stencil(compiled['components'],coefficient)['status'],'VERIFIED_IDENTITY')
        for n in range(33,41):self.assertEqual(coefficient[n],{'1':'-1'})
        wrong=copy.deepcopy(row);wrong['counts'][0]=4
        with self.assertRaises(ValueError):P.residual_components(program,wrong,[{40:1,32:2},{}])

    def test_complete_constructor_search_independent_certificate_and_tamper(self):
        components=[dict(parent=240,weight={'1':'1'}),dict(parent=80,weight={'a':'-1/2'})]
        intervals={'1':['1','1'],'a':['1/3','2/5']}
        coefficient=P.materialize(P.stencil_intervals(components))
        result=P.search_pairings(coefficient,intervals,depth=3,width=3)
        checked=P.certify_search(components,intervals,result)
        self.assertEqual(checked['status'],'VERIFIED_FINITE_CONSTRUCTION',checked)
        self.assertEqual(Q(checked['bound']['bound']),P.coefficient_bound(result['coefficients'],intervals))
        self.assertLessEqual(Q(result['l1_upper']),Q(result['initial_l1_upper']))
        changed=copy.deepcopy(result);changed['l1_upper']='0'
        self.assertEqual(P.certify_search(components,intervals,changed)['status'],'INVALID')

    def test_input_and_prospective_resource_gates(self):
        with self.assertRaises(ValueError):P.fold({1:{'1':'1'}},4)
        with self.assertRaises(ValueError):P.fold({1:{'1':'1'}},2,(2,))
        with self.assertRaises(ValueError):P.fold({2:{'1':'1'}},3,(2,))
        with self.assertRaises(ValueError):P.materialize([dict(left=0,right=P.MAX_TERMS+1,weight={'1':'1'})])
        with self.assertRaises(ValueError):P.coefficient_bound({1:{'missing':'1'}},{})
        with self.assertRaises(ValueError):P.search_pairings({1:{'1':'1'}},{'1':['1','1']},depth=9)

    def test_feedback_preserves_refuted_constant_and_other_arithmetic_leaves(self):
        program=dict(q='129/128',base_u=4096,innovation_C='1/100',atoms=[dict(column=0,gamma='1/3')])
        leaves=[dict(lemma='innovation',status='FINITE_COUNTEREXAMPLE',first_witness={'u':5000}),
                dict(lemma='correlation',status='UNIFORM_PROOF_REQUIRED')]
        result=P.feedback_jobs([dict(id='x',program=program)],
            [dict(id='x',status='REFUTED',last_domain='adaptation',unpaid_leaves=leaves)])
        job=result['jobs'][0]
        self.assertTrue(job['fixed_false_C_is_not_a_proof_target'])
        self.assertEqual(job['unpaid_leaves'],leaves)
        self.assertEqual(job['target']['finite_test_C'],'1/100')
        self.assertFalse(result['new_scientific_pairing_search_run'])
        self.assertFalse(job['uniform_bound_proved'])
        with self.assertRaises(ValueError):P.feedback_jobs([], [dict(id='missing')])


if __name__=='__main__':unittest.main()
