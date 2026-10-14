"""Small exact synthetic calibrations; no prior suite or numeric source archive."""
from copy import deepcopy
from fractions import Fraction as Q
from unittest.mock import patch
import time
import unittest

import core_signed_primitive_search as PRODUCER
import check_core_signed_primitive_search as CHECK
from potential_candidate_language import Meter

START=time.monotonic()
WORK=Meter(50000000,deadline=START+180,max_cells=2000000)
H={k:dict(bound=dict(B_power='0',log_degree='0')) for k in range(13)}
SIGMA=Q(9,20)
GOAL=dict(B_power='0',log_degree='0')


def tearDownModule():
    print('SYNTHETIC_WORK module=test_check_core_signed_primitive_search operations='+str(WORK.operations)+
          ' elapsed_seconds='+str(time.monotonic()-START),flush=True)


def synthesis(source,goal=None,heights=None):
    return PRODUCER.synthesize(source,SIGMA,H if heights is None else heights,GOAL if goal is None else goal,WORK)


def generic_driver():
    """Isolate wrapper composition using a synthetic ancestry trust boundary."""
    transition=CHECK.ALG.transition(1,2,True,WORK)
    library=[]
    for k in range(13):
        moment=dict(best=dict(integral_height_power='1',epsilon_coefficient='1'))
        library.append(dict(zeta_power=k,moment=moment,height=CHECK.MOM.height_bound(moment,'10','1/1000')))
    binding=dict(target_id='synthetic',inherited_bound=dict(power='12/5'),whole_signed_bound_proved=False,RH_proved=False)
    parent=dict(schema='core-work-moment-proof-feedback-v1',cutoff_work_targets=[dict(p=1,m=2,sigma='9/20',theta='2/3',
        selected_program=0,programs=[dict(transition=transition)])],work_moment_proof_search=dict(binding=binding,
        spec=dict(epsilon='1/1000'),moment_library=library),
        prefix_projection_search=dict(proof_search=dict(common_window=dict(H=dict(U_power='10')))),
        next_search_tasks=[dict(target_id='actual_signed_core',priority=0,status='open'),
                           dict(target_id='retained_alternative',priority=1,status='open')],
        source_fixture=dict(unit=1,transport='-e',drifts=['complete opposite drift'],original_channels=list(range(144))),
        whole_signed_bound_proved=False,RH_proved=False)
    with patch.object(PRODUCER,'source_binding',return_value=binding):result=PRODUCER.search(parent,WORK)
    return parent,binding,result


class IndependentSignedPrimitiveTests(unittest.TestCase):
    def test_prime_bank_meter_compatibility_preserves_rational_size_guard(self):
        from prime_bank_candidates import Meter as PrimeMeter
        meter=PrimeMeter(cap=200000,seconds=10)
        source={('a','c','x'):Q(1)}
        result=PRODUCER.synthesize(source,SIGMA,H,GOAL,meter)
        before=meter.operations
        self.assertTrue(CHECK.verify_synthesis(source,SIGMA,H,GOAL,result,meter)['verified'])
        self.assertGreater(meter.operations,before)
        self.assertFalse(hasattr(meter,'number'))
        for coefficient in (1<<4096,Q(1,1<<4096)):
            with self.assertRaises(ValueError):
                CHECK.verify_synthesis({('a','c','x'):coefficient},SIGMA,H,GOAL,result,meter)
        self.assertEqual(CHECK._check_number(Q(1,2),meter),Q(1,2))
        self.assertEqual(CHECK._check_number(1<<4095,meter),1<<4095)
        # Preserve a stricter configured limit on the original test meter.
        strict=Meter(1000,max_bits=8)
        with self.assertRaises(ValueError):CHECK._check_number(256,strict)
        WORK.charge(meter.operations+strict.operations)

    def test_calibration_discovers_quadratic_primitive_and_constant_bound(self):
        source={('a','c','x'):Q(1)};result=synthesis(source)
        self.assertTrue(CHECK.verify_synthesis(source,SIGMA,H,GOAL,result,WORK)['verified'])
        self.assertEqual(result['basis'],[[dict(monomial=['c','c'],coefficient='1')]])
        self.assertEqual(result['certificate']['potential'],[dict(monomial=['c','c'],coefficient='1/2')])
        self.assertEqual(result['certificate']['residual'],[dict(monomial=['a','a','x','x'],coefficient='-1/2')])
        self.assertEqual(result['baseline'],dict(B_power='0',log_degree='1'))
        self.assertEqual(result['certificate']['bound'],GOAL)

    def test_exact_finite_telescoping_and_complete_unit_floor_identity(self):
        mu=[0,1,-1,-1,0,-1,1];c=Q(1);work=Q(0);residual=Q(0)
        for q in range(2,len(mu)):
            work+=mu[q]*c/q;residual-=Q(mu[q]**2,2*q*q);c+=Q(mu[q],q)
            self.assertEqual(work,(c*c-1)/2+residual)
            self.assertLessEqual(abs(c),2)
            # The source reciprocal bound uses ALL divisor rows and unit.
            self.assertEqual(q*c,1+sum(Q(mu[d])*(Q(q,d)-q//d) for d in range(1,q+1)))
        self.assertLessEqual(sum(Q(1,n*n) for n in range(2,20)),Q(3,4))

    def test_three_specializations_keep_complex_conjugates_and_mu_zero_D(self):
        potential={('A','Dbar'):Q(1),('Abar','D'):Q(1)}
        delta=CHECK.delta(potential,WORK)
        expected={('Dbar','b','x'):Q(1),('D','bbar','x'):Q(1),
                  ('A','bbar'):Q(1),('Abar','b'):Q(1),('b','bbar','x'):Q(2)}
        self.assertEqual(delta,expected);self.assertEqual(delta,PRODUCER.delta(potential,WORK))
        zero=CHECK.MOM._substitute(delta,dict(x={():Q(0)}),WORK)
        self.assertEqual(zero,{('A','bbar'):Q(1),('Abar','b'):Q(1)})
        for n in (3,4,7):
            poly={('c',)*n:Q(1)}
            self.assertEqual(CHECK.delta(poly,WORK),PRODUCER.delta(poly,WORK))
            self.assertTrue(all(key.count('x')<=2 for key in CHECK.delta(poly,WORK)))

    def test_Hermitian_basis_inferred_only_from_reversible_source_events(self):
        source={('A','bbar','x'):Q(1),('Abar','b','x'):Q(1),('a','c','x'):Q(2)}
        basis=CHECK.primitive_basis(source,WORK)
        self.assertEqual(basis,PRODUCER.primitive_basis(source,WORK))
        self.assertIn({('A','Abar'):Q(1)},basis);self.assertIn({('c','c'):Q(1)},basis)
        source[('a','b','x')]=Q(1)
        self.assertEqual(CHECK.primitive_basis(source,WORK),basis)  # Extra event cannot be stored.
        with self.assertRaises(ValueError):CHECK.delta({('a','c'):Q(1)},WORK)

    def test_initialized_unit_zeta_cost_is_paid_at_common_height(self):
        heights=deepcopy(H);heights[2]['bound']=dict(B_power='7',log_degree='1')
        poly={('c','c','z','zbar'):Q(1)}
        init=CHECK.initialized(poly,WORK)
        self.assertEqual(init,{('c','c','z','zbar'):Q(1),('z','zbar'):Q(-1)})
        self.assertEqual(CHECK.bound(init,SIGMA,heights,True),dict(B_power='7',log_degree='1'))
        self.assertEqual(CHECK.term_cost(('a','c','x'),SIGMA,H),dict(B_power='0',log_degree='1'))
        self.assertEqual(CHECK.term_cost(('a','a','x','x'),SIGMA,H),GOAL)
        self.assertEqual(CHECK.term_cost(('A','Abar'),SIGMA,H,True),dict(B_power='11/10',log_degree='0'))

    def test_generic_complex_and_deterministic_head_synthesis_certificates(self):
        potentials=[{('c',)*n:Q(1) for n in (2,3)},
            {('D','Dbar'):Q(1)}, {('A','Abar','c'):Q(1)},
            {('A','Dbar'):Q(1),('Abar','D'):Q(1)}]
        for potential in potentials:
            source=CHECK.delta(potential,WORK);result=synthesis(source,dict(B_power='2',log_degree='0'))
            self.assertTrue(CHECK.verify_synthesis(source,SIGMA,H,dict(B_power='2',log_degree='0'),result,WORK)['verified'])
            self.assertTrue(result['unconstrained_signed_elimination']['status']=='feasible')

    def test_left_null_dual_audits_every_allowed_column(self):
        source={('A','a','x'):Q(1),('Abar','a','x'):Q(1),('a','c','x'):Q(1)};result=synthesis(source)
        self.assertTrue(CHECK.verify_synthesis(source,SIGMA,H,GOAL,result,WORK)['verified'])
        failed=next(t for t in result['trials'] if t['status']=='infeasible')
        self.assertNotEqual(Q(failed['contradiction']),0)
        for mutate in (lambda t:t.update(contradiction='0'),lambda t:t['dual'].pop(),
            lambda t:t.update(allowed_basis=[]),lambda t:t.update(constrained_rows=0)):
            bad=deepcopy(result);trial=next(t for t in bad['trials'] if t['status']=='infeasible');mutate(trial)
            with self.assertRaises(ValueError):CHECK.verify_synthesis(source,SIGMA,H,GOAL,bad,WORK)
        # Explicit nonzero column: a displayed row alone cannot certify a dual.
        columns=[{('a','x'):Q(2)}];basis=[{('c',):Q(1)}]
        item=dict(status='infeasible',dual=[dict(monomial=['a','x'],coefficient='1')],contradiction='1')
        with self.assertRaises(ValueError):CHECK._linear_certificate({('a','x'):Q(1)},basis,columns,[('a','x')],[0],item,WORK)

    def test_complete_thresholds_and_endpoint_cost_cannot_be_assumed_free(self):
        source={('A','a','x'):Q(1),('Abar','a','x'):Q(1)};result=synthesis(source)
        self.assertFalse(result['requested_bound_proved'])
        for mutate in (lambda r:r['trials'].pop(),lambda r:r.update(selected_trial=0),
            lambda r:r['basis_endpoint_costs'].__setitem__(0,GOAL),lambda r:r.update(requested_bound_proved=True),
            lambda r:r.update(arithmetic_bound_refuted=True),lambda r:r.update(uniform_domain='dyadic endpoints only')):
            bad=deepcopy(result);mutate(bad)
            with self.assertRaises(ValueError):CHECK.verify_synthesis(source,SIGMA,H,GOAL,bad,WORK)

    def test_primal_solution_residual_boundary_and_zero_event_tampers(self):
        source={('a','c','x'):Q(1)};result=synthesis(source)
        changes=[lambda r:r['trials'][r['selected_trial']]['solution'][0].update(coefficient='1'),
            lambda r:r['trials'][r['selected_trial']]['solution'][0].update(basis_id=999),
            lambda r:r['certificate'].update(residual=[]),lambda r:r['certificate'].update(boundary=[]),
            lambda r:r['certificate'].update(target_bound_assumed=True),
            lambda r:r['certificate'].update(every_event_and_zero_mu_history_retained=False)]
        for change in changes:
            bad=deepcopy(result);change(bad)
            with self.assertRaises((ValueError,IndexError)):CHECK.verify_synthesis(source,SIGMA,H,GOAL,bad,WORK)

    def test_source_normal_form_keeps_signed_even_and_conjugate_crosses(self):
        transition=CHECK.ALG.transition(1,2,True,WORK)
        self.assertEqual(CHECK.joined_source(transition,WORK),PRODUCER.joined_source(transition,WORK))
        normalized=CHECK.canonical({('E','Ebar'):Q(1),('v',):Q(2)},WORK)
        self.assertEqual(normalized,PRODUCER.canonical({('E','Ebar'):Q(1),('v',):Q(2)},WORK))
        self.assertTrue(all('E' not in key and 'Ebar' not in key and 'v' not in key for key in normalized))
        bad=deepcopy(transition)
        index=next(i for i,row in enumerate(bad['work_sectors'][1]) if
            CHECK.ALG._conjugate({tuple(row['monomial']):Q(row['coefficient'])})!={tuple(row['monomial']):Q(row['coefficient'])})
        bad['work_sectors'][1].pop(index)
        with self.assertRaises(ValueError):CHECK.joined_source(bad,WORK)

    def test_sigma_height_premises_and_unknown_moment_fail_closed(self):
        for sigma in (-1,0,1,2):
            with self.assertRaises(ValueError):CHECK.term_cost(('c',),sigma,H)
        for field,value in [('B_power','-1'),('log_degree','-1')]:
            heights=deepcopy(H);heights[0]['bound'][field]=value
            with self.assertRaises(ValueError):CHECK.term_cost(('c',),SIGMA,heights)
        with self.assertRaises(ValueError):CHECK.term_cost(('z',)*20,SIGMA,H)
        with self.assertRaises(ValueError):CHECK.verify_synthesis({('a','x','x','x'):Q(1)},SIGMA,H,GOAL,{},WORK)
        with self.assertRaises(ValueError):CHECK.verify_synthesis({('A','a','x'):Q(1)},SIGMA,H,GOAL,{},WORK)

    def test_wrapper_detects_original_energy_restatement_and_library_changes(self):
        parent,binding,result=generic_driver()
        with patch.object(CHECK,'source_binding',return_value=binding):
            self.assertTrue(CHECK.verify_search(parent,result,WORK)['verified'])
            bad=deepcopy(result);bad['common_window']['H']['U_power']='1'
            with self.assertRaises(ValueError):CHECK.verify_search(parent,bad,WORK)
            bad=deepcopy(result);bad['inherited_height_library'].pop()
            with self.assertRaises(ValueError):CHECK.verify_search(parent,bad,WORK)
            bad=deepcopy(result);bad['exact_primitive_is_original_energy_restatement']=not bad['exact_primitive_is_original_energy_restatement']
            with self.assertRaises(ValueError):CHECK.verify_search(parent,bad,WORK)
            altered=deepcopy(parent);altered['work_moment_proof_search']['moment_library'][0]['height']['compact_head_retained']=False
            with self.assertRaises(ValueError):CHECK.verify_search(altered,result,WORK)

    def test_feedback_retains_source_units_drifts_channels_and_priority_zero(self):
        parent,binding,result=generic_driver();artifact='synthetic/search.json'
        out=PRODUCER.feedback(parent,result,artifact)
        with patch.object(CHECK,'source_binding',return_value=binding):
            self.assertTrue(CHECK.verify_feedback(parent,result,out,artifact,WORK)['verified'])
            for mutate in (lambda p:p['source_fixture'].update(unit=0),lambda p:p['source_fixture']['drifts'].pop(),
                lambda p:p['source_fixture']['original_channels'].pop(),lambda p:p['next_search_tasks'].pop(0),
                lambda p:p['next_search_tasks'][1].update(arithmetic_bound_refuted=True),lambda p:p.update(RH_proved=True)):
                bad=deepcopy(out);mutate(bad)
                with self.assertRaises(ValueError):CHECK.verify_feedback(parent,result,bad,artifact,WORK)


if __name__=='__main__':unittest.main()
