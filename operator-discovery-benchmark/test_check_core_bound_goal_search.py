"""Generic algebraic calibration and conditional-proof tamper rejection."""
from copy import deepcopy
from fractions import Fraction as Q
from math import comb
import resource
import time
import unittest

import core_bound_goal_search as PRODUCER
import check_core_bound_goal_search as CHECK
from potential_candidate_language import Meter

START=time.monotonic()
WORK=Meter(50000000,deadline=START+180,max_cells=2000000)
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))

MODES=[dict(name='B',coefficient='beta',p=2,q=0,positive_shift='1/3'),
       dict(name='U',coefficient='-beta',p=1,q=1,positive_shift='1/3'),
       dict(name='V',coefficient='-beta',p=1,q=0,positive_shift=None),
       dict(name='power',coefficient='-R_u',p=0,q=1,positive_shift='1/3')]


def fixture(alpha=Q(1,6),gamma=Q(1,3)):
    # Build inverse coefficients independently using their closed binomial law.
    cases=[]
    for mode in MODES:
        p,q=mode['p'],mode['q'];terms=[]
        for total in range(64):
            for a in range(total+1):
                b=total-a
                if alpha*a+gamma*b>=1:continue
                ca=comb(p+a-1,a) if p else int(a==0)
                cb=comb(q+b-1,b) if q else int(b==0)
                if ca*cb:terms.append(dict(a=a,b=b,coefficient=str(ca*cb)))
                WORK.charge(15)
        cases.append(dict(mode=deepcopy(mode),program=dict(alpha=str(alpha),gamma=str(gamma),p=p,q=q,terms=terms)))
    source=dict(id=0,alpha=str(alpha),gamma=str(gamma),cases=cases,
        component_count=sum(len(c['program']['terms']) for c in cases),
        exact_join=dict(transport_error_coefficient='-1',all_moment_drifts=[0,1],all_centering_compensations=[0,1]),
        full_signed_bound_proved=False,RH_proved=False)
    return dict(selected_source_representation=source,
        generated_bound_obligations=[dict(parent_obligation_id=i,status='open',transport_program=dict(id=i)) for i in range(144)],
        proof_frontier=[dict(id='old_complete_signed_core',status='open'),dict(id='old_moment_conditions',status='open')],
        whole_signed_bound_proved=False,RH_proved=False)


def polynomial_value(poly,variables):
    total=Q(0)
    for term in poly:
        c=Q(term['coefficient'])
        for x,p in zip(variables,term['powers']):c*=x**p;WORK.charge(10)
        total+=c
    return total


class IndependentBoundGoalTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.parent=fixture();cls.spec=deepcopy(PRODUCER.DEFAULT_SPEC);cls.spec['diagnostic_denominator_max']=4
        cls.result=PRODUCER.search(cls.parent,cls.spec,WORK)

    def reject(self,mutate):
        v=deepcopy(self.result);mutate(v)
        with self.assertRaises((ValueError,KeyError,TypeError)):
            CHECK.verify_search(self.parent,v,WORK)

    def test_quadratic_interval_audit_catches_an_interior_negative_gap(self):
        self.assertTrue(CHECK.nonnegative_on_interval([0,1,-1],Q(0),Q(1),WORK))
        self.assertFalse(CHECK.nonnegative_on_interval([Q(1,8),-1,1],Q(0),Q(1),WORK))
        self.assertTrue(CHECK.nonnegative_on_interval([Q(1,4),-1,1],Q(0),Q(1),WORK))
        self.assertFalse(CHECK.nonnegative_on_interval([0,0,-1],Q(-1),Q(1),WORK))
        with self.assertRaises(ValueError):CHECK.nonnegative_on_interval([0,0,0,1],0,1,WORK)

    def test_generic_symbolic_minimax_families_and_C_scaling(self):
        for theta in (Q(1,5),Q(1,2),Q(2,3),Q(7,8)):
            for rule in ('ordinary','euler_remainder'):
                family=CHECK._family(theta,rule,WORK)
                self.assertEqual(family,PRODUCER.synthesize_family(str(theta),rule,WORK))
                den=list(map(Q,family['denominator']))
                for rho in (Q(0),theta/3,theta*Q(7,8)):
                    d=CHECK._value(den,rho,WORK)
                    r=CHECK._value(list(map(Q,family['power_numerator'])),rho,WORK)/d
                    t=CHECK._value(list(map(Q,family['parameter_numerator'])),rho,WORK)/d
                    cp=CHECK._value(list(map(Q,family['C_power_numerator'])),rho,WORK)/d
                    expected_r=theta/(1+theta-rho) if rule=='ordinary' else (theta+rho*(1-theta))/(2-rho)
                    expected_t=expected_r if rule=='ordinary' else 1/(2-rho)
                    self.assertEqual((r,t,cp),(expected_r,expected_t,(1-r)/(1-rho)))
                    self.assertLess(r,theta);self.assertGreater(r,rho)

    def test_factor_search_discovers_a_different_generic_tail(self):
        expression=[dict(coefficient='1',factors=[]),dict(coefficient='2',factors=['O','F']),
            dict(coefficient='-1',factors=['O','G'])]
        factor=CHECK._factor_search(2,WORK,basis=['F','G','delta'],
            moments=[{'z':'1'},{'z':'2'},{'one':'1'}],expression=expression)
        chosen=factor['candidates'][factor['selected']]
        self.assertEqual(chosen['coefficients'],[2,-1,0]);self.assertEqual(chosen['harmonic_moment'],{})
        self.assertGreater(len(factor['candidates']),50)
        self.assertTrue(any(not c['zero_moment'] for c in factor['candidates']))
        self.assertEqual(self.result['factor_search']['candidates'][self.result['factor_search']['selected']]['coefficients'],[-1,1,0])

    def test_factor_candidate_omission_moment_or_extraction_tamper_rejected(self):
        self.reject(lambda r:r['factor_search']['candidates'].pop())
        self.reject(lambda r:r['factor_search'].update(selected=0))
        self.reject(lambda r:r['factor_search']['harmonic_moment_map'][0].update(c='2'))
        self.reject(lambda r:r['factor_search'].update(extracted_anchor='0'))
        self.reject(lambda r:r['factor_search']['supplied_residual_expression'][1].update(coefficient='1'))

    def test_complete_source_join_matches_original_rational_substitution(self):
        audit=CHECK.verify_search(self.parent,self.result,WORK)
        self.assertEqual(audit['inherited_bindings'],144);self.assertEqual(audit['targets'],4)
        values=[Q(2,3),Q(-3,5),Q(7,4),Q(5,7),Q(-2,9),Q(1,3),Q(11,6),Q(13,8)]
        A,B,K,E,S,C,O,Ru=values;R=E-C*O;original=Q(0)
        for case in self.parent['selected_source_representation']['cases']:
            mode=case['mode'];scalar={'beta':Q(9,2),'-beta':Q(-9,2),'-R_u':-Ru}[mode['coefficient']]
            for term in case['program']['terms']:
                original+=scalar*Q(term['coefficient'])*A**mode['p']*B**mode['q']*R**term['a']*S**term['b']*(K if mode['positive_shift'] else 1)
                WORK.charge(50)
        collected=polynomial_value(self.result['complete_signed_join']['collected_terms'],values)
        self.assertEqual(original,collected)
        self.assertEqual(original-Q(7,3),collected-Q(7,3))
        self.assertEqual(self.result['complete_signed_join']['transport_error']['coefficient'],'-1')

    def test_missing_source_unit_signed_companion_or_transport_rejected(self):
        self.reject(lambda r:r['complete_signed_join']['collected_terms'].pop())
        self.reject(lambda r:r['complete_signed_join']['source_expansions'][0]['terms'].pop())
        self.reject(lambda r:r['complete_signed_join']['transport_error'].update(coefficient='0'))
        self.reject(lambda r:r['complete_signed_join'].update(all_compensations_retained=False))
        parent=deepcopy(self.parent);parent['selected_source_representation']['cases'][0]['program']['terms'].pop(0)
        with self.assertRaises(ValueError):CHECK.verify_search(parent,self.result,WORK)

    def test_finite_zero_moment_cancels_all_and_only_required_jet_orders(self):
        # T=delta-2*delta_2 has harmonic moment zero. Its j-fold finite
        # convolution has all support 2^k, including terms beyond n=1.
        for j in range(1,9):
            weighted=[Q((-1)**k*comb(j,k)) for k in range(j+1)]
            for degree in range(j):
                self.assertEqual(sum((c*k**degree for k,c in enumerate(weighted)),Q(0)),0)
                WORK.charge(30*(j+1))
            self.assertNotEqual(sum((c*k**j for k,c in enumerate(weighted)),Q(0)),0)
            self.assertEqual(weighted[0],1)  # Truncation to d<=1 loses cancellation.
        cert=self.result['moment_cancellation_certificates'][2]
        self.assertEqual(cert['zero_moment_degrees'],[0,1,2])
        self.assertIsNone(cert['bounded_polynomial']);self.assertFalse(cert['remainder_bound_proved'])

    def test_wrong_annihilation_order_or_missing_small_argument_tail_rejected(self):
        self.reject(lambda r:r['moment_cancellation_certificates'][1]['zero_moment_degrees'].append(2))
        self.reject(lambda r:r['moment_cancellation_certificates'][1]['main_term_expansions'][1]['terms'][1].update(coefficient='1'))
        self.reject(lambda r:r['moment_cancellation_certificates'][1].update(include_d_greater_than_n=False))
        self.reject(lambda r:r['moment_cancellation_certificates'][1].update(remainder_bound_proved=True))
        self.reject(lambda r:r['generated_bound_targets'][0]['remainder_branches'][2].update(complete_remainder_for_all_positive_arguments=False))

    def test_backwards_region_and_full_divisor_U_cost_hand_calibration(self):
        families=[CHECK._family(Q(2,3),rule,WORK) for rule in ('ordinary','euler_remainder')]
        ordinary=CHECK._region(families[0],Q(1,24),2,'0',WORK)
        euler=CHECK._region(families[1],Q(1,24),2,'0',WORK)
        self.assertEqual([ordinary[k] for k in ('b_coefficient','rho_coefficient','rhs')],['1','10','2'])
        self.assertEqual([euler[k] for k in ('b_coefficient','rho_coefficient','rhs')],['1','13','4'])
        j2=CHECK._substitution(euler,2,WORK);j3=CHECK._substitution(euler,3,WORK);j4=CHECK._substitution(euler,4,WORK)
        self.assertEqual((j2['threshold'],j3['threshold']),('2/11','1/10'))
        self.assertTrue(j2['has_strictly_feasible_exponent']);self.assertFalse(j4['has_strictly_feasible_exponent'])
        self.assertFalse(CHECK._substitution(ordinary,2,WORK)['has_strictly_feasible_exponent'])
        self.assertEqual(j2['substitution'],dict(b_constant='2',b_rho_coefficient='-2'))
        self.assertEqual(euler['relation'],'<')
        self.assertIn('no constant payment',euler['equality_scope'])

    def test_declared_cutoff_1_over_24_keeps_degree_23_and_unlicensed_boundary(self):
        parent=fixture(Q(1,24),Q(1,2));result=PRODUCER.search(parent,self.spec,WORK)
        audit=CHECK.verify_search(parent,result,WORK)
        self.assertEqual(audit['targets'],22)
        m2=result['generated_bound_targets'][0];m3=result['generated_bound_targets'][1]
        self.assertEqual(m2['m'],2);self.assertEqual(m3['m'],3)
        self.assertEqual([r['current_generic_bound']['energy_N_power'] for r in m2['routes']],['2/7','7/27'])
        self.assertTrue(m2['routes'][1]['conditional_auxiliary_route_has_feasible_exponents'])
        self.assertEqual(m3['generic_prefix_rule']['rho'],'2/3')
        self.assertTrue(all(r['current_generic_bound']['status']=='unlicensed' for r in m3['routes']))
        self.assertFalse(result['generated_bound_targets'][2]['routes'][1]['conditional_auxiliary_route_has_feasible_exponents'])
        self.assertEqual(result['statistics']['new_component_bounds_proved'],0)
        self.assertEqual(result['statistics']['targets_redirected_to_joint_control'],20)
        self.assertEqual(result['next_search_tasks'][1]['search_kind'],'search_complete_remainder_bounds')
        self.assertEqual(result['next_search_tasks'][3]['search_kind'],'search_joint_weighted_remainder_control')

    def test_symbolic_dual_gap_cutoff_power_and_Euler_compensation_tamper(self):
        self.reject(lambda r:r['symbolic_bound_families'][0]['dual_weight_numerators'][0].__setitem__(0,'0'))
        self.reject(lambda r:r['symbolic_bound_families'][1]['gap_polynomials'][2].__setitem__(0,'0'))
        self.reject(lambda r:r['symbolic_bound_families'][1]['C_power_numerator'].__setitem__(0,'1'))
        self.reject(lambda r:r['symbolic_bound_families'][1].update(retained_euler_compensation=None))
        self.reject(lambda r:r['symbolic_bound_families'][0].update(all_small_prefixes_included=False))

    def test_moment_boundary_diagnostic_coverage_and_wrong_energy_cost_rejected(self):
        self.reject(lambda r:r['diagnostic_minimax'][0]['points'].pop())
        self.reject(lambda r:r['diagnostic_minimax'][0]['points'][0].update(rho='2/3'))
        self.reject(lambda r:r['generated_bound_targets'][0]['routes'][0]['current_generic_bound'].update(energy_N_power='-1'))
        self.reject(lambda r:r['generated_bound_targets'][1]['routes'][0]['current_generic_bound'].update(status='proved exponent'))
        self.reject(lambda r:r['generated_bound_targets'][0]['routes'][1]['missing_prefix_bound_region'].update(finite_factor_U_cost='0'))

    def test_complete_head_gates_mass_cost_and_remainder_conditions_rejected(self):
        self.reject(lambda r:r['generated_bound_targets'][0]['routes'][1]['proved_head_branches'].pop())
        self.reject(lambda r:r['generated_bound_targets'][0]['routes'][1]['proved_head_branches'][1].update(b='0'))
        self.reject(lambda r:r['generated_bound_targets'][0]['remainder_branches'][2]['mass_bound'].update(constant='1'))
        self.reject(lambda r:r['generated_bound_targets'][0]['routes'][1]['remainder_branch_regions'][0].update(kappa_coefficient='0'))
        self.reject(lambda r:r['generated_bound_targets'][0]['routes'][1].update(conditional_auxiliary_route_has_feasible_exponents=True))

    def test_conditional_estimate_cannot_be_promoted_to_component_or_core_proof(self):
        self.reject(lambda r:r['generated_bound_targets'][0]['remainder_branches'][2].update(status='proved'))
        self.reject(lambda r:r['generated_bound_targets'][0].update(component_bound_proved=True))
        self.reject(lambda r:r['generated_bound_targets'][0].update(original_moment_drift_retained=False))
        self.reject(lambda r:r.update(whole_signed_bound_proved=True))
        self.reject(lambda r:r['statistics'].update(new_component_bounds_proved=1))

    def test_graph_cycles_open_dependencies_and_missing_complement_rejected(self):
        with self.assertRaises(ValueError):CHECK._audit_graph([dict(id='a',status='proved',depends_on=['b']),
            dict(id='b',status='proved',depends_on=['a'])],WORK)
        with self.assertRaises(ValueError):CHECK._audit_graph([dict(id='a',status='proved',depends_on=['b']),
            dict(id='b',status='open',depends_on=[])],WORK)
        self.reject(lambda r:r['proof_dependencies'][0]['depends_on'].append('actual_signed_core'))
        self.reject(lambda r:r['proof_dependencies'][-2]['depends_on'].remove('complete_signed_complement'))
        self.assertTrue(any(n['id']=='complete_signed_complement' and n['status']=='open' for n in self.result['proof_dependencies']))

    def test_missing_target_inherited_bindings_and_cap_cannot_drop_source(self):
        self.reject(lambda r:r['generated_bound_targets'].pop())
        self.reject(lambda r:r['inherited_bound_obligations'].pop())
        self.reject(lambda r:r['inherited_selected_source']['exact_join']['all_moment_drifts'].clear())
        self.reject(lambda r:r['spec'].update(maximum_residual_degree=2))
        self.reject(lambda r:r.update(actual_source_observations=1))
        self.reject(lambda r:r['next_search_tasks'][1].update(search_kind='search_complete_remainder_bounds'))

    def test_feedback_retains_all_conditional_targets_and_original_frontier(self):
        feedback=PRODUCER.feedback(self.result,'input.json','complete.json')
        self.assertTrue(CHECK.verify_feedback(self.result,feedback,'input.json','complete.json',WORK)['verified'])
        for field in ('auxiliary_bound_targets','retained_original_proof_frontier','generated_bound_obligations'):
            v=deepcopy(feedback);v[field].pop()
            with self.assertRaises(ValueError):CHECK.verify_feedback(self.result,v,'input.json','complete.json',WORK)
        v=deepcopy(feedback);v['RH_proved']=True
        with self.assertRaises(ValueError):CHECK.verify_feedback(self.result,v,'input.json','complete.json',WORK)


def tearDownModule():
    print('SYNTHETIC_WORK module=test_check_core_bound_goal_search operations='+str(WORK.operations)+
        ' elapsed_seconds='+format(time.monotonic()-START,'.6f'))
