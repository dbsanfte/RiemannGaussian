"""Independent synthetic source algebra, norm costs and adversarial proofs."""
from copy import deepcopy
from fractions import Fraction as Q
from math import comb
import time
import unittest

import core_work_moment_proof_search as PRODUCER
import check_core_work_moment_proof_search as CHECK
from potential_candidate_language import Meter
START=time.monotonic()
WORK=Meter(1000000000,deadline=START+600,max_cells=6000000)


def tearDownModule():
    print('SYNTHETIC_WORK module=test_check_core_work_moment_proof_search operations='+str(WORK.operations)+
          ' elapsed_seconds='+str(time.monotonic()-START),flush=True)


def symbolic_cutoff_parent():
    """Complete hand finite-source ancestry, with no arithmetic evaluations."""
    import check_core_cutoff_work_search as OLD_CHECK
    import core_cutoff_work_search as OLD_PRODUCER
    import check_core_weighted_height_search as W
    modes = [dict(name='B', coefficient='beta', p=2, q=0, positive_shift='1/3'),
        dict(name='U', coefficient='-beta', p=1, q=1, positive_shift='1/3'),
        dict(name='V', coefficient='-beta', p=1, q=0, positive_shift=None),
        dict(name='power', coefficient='-R_u', p=0, q=1, positive_shift='1/3')]
    alpha, gamma = Q(1, 24), Q(1, 2); cases = []
    for mode in modes:
        p, q = mode['p'], mode['q']; terms = []
        for total in range(48):
            for a in range(total+1):
                b = total-a; WORK.charge(5)
                if a*alpha+b*gamma >= 1: continue
                coefficient = (comb(p+a-1, a) if p else int(a == 0))*(comb(q+b-1, b) if q else int(b == 0))
                if coefficient: terms.append(dict(a=a, b=b, coefficient=str(coefficient)))
        cases.append(dict(mode=mode, program=dict(alpha=str(alpha), gamma=str(gamma), p=p, q=q, terms=terms)))
    source = dict(id=0, alpha=str(alpha), gamma=str(gamma), cases=cases,
        component_count=sum(len(c['program']['terms']) for c in cases), full_signed_bound_proved=False, RH_proved=False)
    bindings = [dict(parent_obligation_id='original_'+str(i), inherited_binding=dict(transport_program=dict(id=i, mesh_power='1/2')),
        whole_signed_bound_proved=False, RH_proved=False) for i in range(144)]
    parent = dict(schema='core-weighted-height-feedback-v1', status='open', selected_source_representation=source,
        generated_bound_obligations=bindings, retained_original_proof_frontier=[dict(id='full_core', status='open')],
        next_search_tasks=[dict(target_id='actual_signed_core', priority=0, status='open')], whole_signed_bound_proved=False, RH_proved=False)
    join = OLD_CHECK._source(parent, WORK)
    terms = [t for t in join['collected_terms'] if t['powers'][2] == 1 and t['powers'][3] >= 2 and
        all(t['powers'][i] == 0 for i in (1, 4, 5, 6, 7))]
    old = []; weighted = []
    for term in terms:
        p, m = term['powers'][0], term['powers'][3]; ident = 'centered_A'+str(p)+'_E'+str(m)
        old.append(dict(target_id=ident, p=p, m=m, theta='2/3', source_term=term, component_bound_proved=False))
        target = dict(target_id=ident, p=p, m=m, theta='2/3', source_term=term, inherited_component_bound_proved=False,
            lines=[], selected_line=None, low_obligation=None, new_source_payment=False,
            centering=dict(kind='analytic_residue', M='A(theta)^p*E(theta)^m',
                centered_coefficient='K*A^p*E^m-(M/theta)*J_theta', retained_opposite_drift='source_coefficient*(M/theta)*J_theta',
                ordinary_moment_established_by_inherited_prefix_rule=Q(m-1, m) < Q(2, 3), ordinary_prefix_power=str(Q(m-1, m)),
                ordinary_convergence_required_for_this_route=False, unit_J_theta_1='1',
                continuous_small_x_tail='-(M/theta)*x^theta on 0<x<1', pole_at_1_removed_in_complete_E=True),
            source_head_identity=dict(domain='every integer 1<=n<=U', expression='(A^p*E^m)(n)', scalar='c^m',
                coefficient=dict(atom='One' if m >= p else 'mu', convolution_power=abs(m-p)), zero_power='delta',
                derivation='mu*One=delta on n<=U and E(n)=c', supplies_full_Gram_bound=False))
        if m == 3:
            sigma, theta, kappa, epsilon, tau = Q(9, 20), Q(2, 3), Q(2, 9), Q(1, 120), Q(45, 2)
            branches = W._branches(p, m, theta, sigma, WORK)
            replay = [dict(j=b['j'], length_slack=str(tau*kappa-b['r']), tail_height_power=str(Q(b['height_power'])+epsilon),
                tail_U_power=str(Q(b['weight_U_power'])+tau*(Q(b['height_power'])+epsilon))) for b in branches]
            plan = dict(kappa=str(kappa), epsilon_fraction='1/4', epsilon=str(epsilon), tau=str(tau), branches=replay,
                within_tau_cap=True, high_U_power='-1/16', high_energy_X_power='-1/10', required_low_U_power='12/5',
                generic_low_U_power='11/2', generic_low_energy_X_power='31/240', integer_error_U_power='10/3',
                integer_error_X_power='-31/36', high_auxiliary_proved=True, generic_complete_component_proved=False,
                low_obligation_status='open_actual_Mobius_bound')
            target['lines'] = [dict(sigma=str(sigma), branches=branches, plans=[plan], selected_plan=0, failed_premises=[])]
            target['selected_line'] = 0; target['low_obligation'] = W._low(p, m, theta, sigma, alpha, plan)
        weighted.append(target)
    parent['auxiliary_bound_targets'] = old; parent['weighted_height_targets'] = weighted
    parent['complete_source_reduction'] = dict(inherited_complete_signed_join=join, bindings=bindings,
        transport_error_retained='-e', whole_join_cross_terms_retained=True,
        common_horizon='N=4X-1 for BOTH blocks; same coefficients and cutoffs', new_paid_components=[])
    parent['proof_dependencies'] = [dict(id='reviewed', status='reviewed_and_imported', depends_on=[]),
        dict(id='complete_signed_complement', status='open', depends_on=['reviewed']),
        dict(id='actual_signed_core', status='open', depends_on=['complete_signed_complement'])]
    target = next(t for t in weighted if t['m'] == 3)
    result = dict(targets=[OLD_PRODUCER.compile_target(target, alpha, WORK)])
    return OLD_PRODUCER.feedback(parent, result, 'synthetic-prior.json', 'synthetic/search.json')



def symbolic_parent():
    import core_cutoff_prime_orbits as ORBIT
    import check_core_cutoff_prime_orbits as OLD
    import core_cutoff_prefix_projections as PREFIX
    cutoff=symbolic_cutoff_parent();binding=OLD.bind_target(cutoff,WORK)
    orbit=ORBIT.feedback(cutoff,binding,OLD.select(OLD.program_catalogue(),[]),[],'synthetic/orbits.json')
    proof=PREFIX.proof_search(orbit,binding,WORK)
    selection=dict(discovery_bases=[64,128,256,512],selected=[dict(lane=p['lane'],program_id=p['id'])
        for p in [PREFIX.program_catalogue()[i] for i in (0,1,6,7,16,17)]],rejected=[],undominated_by_lane={})
    return PREFIX.feedback(orbit,binding,proof,selection,[],'synthetic/prefix.json')


class IndependentWorkMomentTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.parent=symbolic_parent()
        cls.result=PRODUCER.search(cls.parent,deepcopy(PRODUCER.DEFAULT_SPEC),WORK)

    def test_generic_exact_presentations_and_square_crosses(self):
        import check_core_cutoff_work_search as ALG
        for p,m,head,sigma in [(0,2,False,Q(1,3)),(1,2,True,Q(2,5)),(2,3,True,Q(9,20))]:
            transition=ALG.transition(p,m,head,WORK)
            independent=CHECK.source_envelopes(transition,sigma,WORK)
            self.assertEqual(independent,PRODUCER.source_envelopes(transition,sigma,WORK))
            for rep in independent['representations']:
                self.assertTrue(all(Q(r['constant'])>0 for r in rep['envelope']))
                self.assertEqual(sum(Q(r['constant']) for r in rep['squared_envelope']),
                    sum(Q(r['constant']) for r in rep['envelope'])**2)
        value={(Q(1),2):Q(3),(Q(-1),0):Q(5)}
        self.assertEqual(CHECK._multiply(value,value,WORK),{(Q(2),4):Q(9),(Q(0),2):Q(30),(Q(-2),0):Q(25)})

    def test_coupled_E_finite_factor_majorants_and_conjugates(self):
        value=CHECK._absolute({('A','E','Ebar','a','bbar','c','z'):Q(-3)},Q(1,2),WORK)
        # C=2, |c|<=2: coefficient12, q exponent -1 before E factors.
        self.assertEqual(value,{(Q(-1),1):Q(12),(Q(-1,2),2):Q(96),(Q(0),3):Q(192)})
        with self.assertRaises(ValueError): CHECK._absolute({('unknown',):Q(1)},Q(1,2),WORK)

    def test_source_branch_identity_rejects_dropped_odd_even_or_J0(self):
        import check_core_cutoff_work_search as ALG
        transition=ALG.transition(1,2,True,WORK)
        for change in (lambda t:t['work_sectors'].__setitem__(1,[]),lambda t:t['work_sectors'].__setitem__(2,[]),
                       lambda t:t['child'].pop()):
            bad=deepcopy(transition);change(bad)
            with self.assertRaises(ValueError): CHECK.source_envelopes(bad,Q(2,5),WORK)

    def test_compact_head_strict_epsilon_and_positive_common_height(self):
        for h,c,expected in [(Q(-1,30),Q(5),(Q(0),Q(0))), (Q(0),Q(2),(Q(9,200),Q(0))),
                             (Q(0),Q(0),(Q(0),Q(1))), (Q(3,2),Q(11),(Q(13599,400),Q(0)))]:
            moment=dict(best=dict(integral_height_power=str(2+h),epsilon_coefficient=str(c)))
            result=CHECK.height_bound(moment,Q(45,2),Q(1,1000))
            self.assertEqual(CHECK._cost(result['bound']),expected)
            self.assertEqual(result,PRODUCER.height_bound(moment,Q(45,2),Q(1,1000)))
            self.assertTrue(result['compact_head_retained'])
        moment=dict(best=dict(integral_height_power='1',epsilon_coefficient='5'))
        value=CHECK.height_bound(moment,10,1)
        self.assertEqual(value['epsilon'],'1/12');self.assertTrue(value['full_height_bound_available'])
        for eps in (0,-1):
            with self.assertRaises(ValueError): CHECK.height_bound(moment,10,eps)

    def test_height_tamper_compact_epsilon_kernel_and_domain(self):
        moment=dict(best=dict(integral_height_power='3',epsilon_coefficient='2'))
        value=PRODUCER.height_bound(moment,10,'1/1000')
        for key,new in [('compact_head_retained',False),('epsilon','0'),('denominator','abs(s)^4'),
                        ('common_height','2*q^tau'),('tau','1'),('full_height_bound_available',True)]:
            bad=deepcopy(value);bad[key]=new
            with self.assertRaises(ValueError):CHECK.verify_height(moment,10,'1/1000',bad,WORK)

    def test_ordinary_series_sum_boundaries_and_negative_event_weights(self):
        self.assertEqual(CHECK.summed_power('-2'),dict(B_power='0',log_degree='0'))
        self.assertEqual(CHECK.summed_power('-1'),dict(B_power='0',log_degree='1'))
        self.assertEqual(CHECK.summed_power('-1/2'),dict(B_power='1/2',log_degree='0'))
        self.assertEqual(CHECK.summed_power('1'),dict(B_power='2',log_degree='0'))
        # Independent rational weighted Cauchy, including negative omega.
        values=[Q(3),Q(-5),Q(4)];weights=[Q(2),Q(3),Q(4)]
        self.assertLessEqual(sum(values)**2,sum(weights)*sum(x*x/w for x,w in zip(values,weights)))

    def test_event_cauchy_and_minkowski_costs_with_critical_logs(self):
        rep=dict(id='synthetic',envelope=[dict(q_power='-1',zeta_power=1,constant='2')],
                 squared_envelope=[dict(q_power='-2',zeta_power=2,constant='4')])
        heights={2:dict(bound=dict(B_power='3',log_degree='1'))}
        weight=dict(q_power='0')
        c=CHECK.gram_attempt(rep,weight,heights,'weighted_event_Cauchy','1',WORK)
        self.assertEqual(c['bound'],dict(B_power='3',log_degree='3'))
        self.assertEqual(c['coefficient_cost_floor'],dict(B_power='0',log_degree='2'))
        m=CHECK.gram_attempt(rep,weight,heights,'weighted_label_Minkowski',None,WORK)
        self.assertEqual(m['bound'],c['bound'])
        self.assertEqual(c,PRODUCER.gram_attempt(rep,weight,heights,'weighted_event_Cauchy','1',WORK))
        self.assertEqual(m,PRODUCER.gram_attempt(rep,weight,heights,'weighted_label_Minkowski',None,WORK))
        self.assertTrue(c['coefficient_floor_is_not_a_bound_on_actual_work'])
        with self.assertRaises(ValueError):CHECK.gram_attempt(rep,weight,heights,'weighted_label_Minkowski','0',WORK)

    def test_norm_attempt_mutations_rejected_without_using_producer_oracle(self):
        rep=dict(id='synthetic',envelope=[dict(q_power='2',zeta_power=1,constant='3')],
                 squared_envelope=[dict(q_power='4',zeta_power=2,constant='9')])
        heights={2:dict(bound=dict(B_power='7',log_degree='0'))};weight=dict(q_power='1/2')
        result=PRODUCER.gram_attempt(rep,weight,heights,'weighted_event_Cauchy','-1',WORK)
        self.assertEqual(result['bound'],dict(B_power='27/2',log_degree='0'))
        for mutate in (lambda r:r['bottleneck_terms'].pop(),lambda r:r.update(event_mass=dict(B_power='0',log_degree='0')),
            lambda r:r['bound'].update(B_power='0'),lambda r:r.update(target_assumed_in_proof=True),
            lambda r:r.update(every_signed_cross_in_source=False),lambda r:r.update(proved_uniform_bound=False),
            lambda r:r['coefficient_cost_floor'].update(B_power='0')):
            bad=deepcopy(result);mutate(bad)
            with self.assertRaises(ValueError):
                CHECK.verify_gram_attempt(rep,weight,heights,'weighted_event_Cauchy','-1',bad,WORK)

    def test_fixed_prime_smooth_weight_and_growing_window_sign(self):
        programs=CHECK.PREFIX.program_catalogue()
        fixed=CHECK.label_weight(programs[1],'3/2');window=CHECK.label_weight(programs[7],'3/2')
        self.assertEqual(fixed['q_power'],'0');self.assertIn('p=2',fixed['multiplier'])
        self.assertEqual(window['q_power'],'3/2');self.assertEqual(window['multiplier'],'1')
        self.assertTrue(fixed['constant_may_depend_on_gamma'])
        with self.assertRaises(ValueError):CHECK.label_weight(programs[1],'-1')

    def test_independent_product_moment_replay_catches_dropped_outer_factor(self):
        entry=next(r for r in self.result['moment_library'] if r['zeta_power']==6)
        CHECK.verify_product_moment(entry['factors'],['2','4'],entry['moment'],WORK)
        self.assertEqual(entry['moment']['best']['integral_height_power'],'59/30')
        self.assertTrue(entry['height']['full_height_bound_available'])
        bad=deepcopy(entry['moment']);bad['best']['factors'].pop()
        with self.assertRaises(ValueError):CHECK.verify_product_moment(entry['factors'],['2','4'],bad,WORK)
        with self.assertRaises(ValueError):CHECK.verify_product_moment(entry['factors'][:1],['2','4'],entry['moment'],WORK)

    def test_full_252_proof_attempts_source_recovery_and_failure_scope(self):
        checked=CHECK.verify_search(self.parent,self.result,WORK)
        self.assertTrue(checked['verified']);self.assertEqual(checked['requested_Gram_bounds'],252)
        self.assertEqual(checked['requested_Gram_bounds_proved'],0)
        self.assertEqual(checked['direct_grouped_bound'],dict(B_power='11/2',log_degree='0'))
        self.assertFalse(checked['whole_signed_bound_proved'])
        self.assertTrue(all(t['excluded_by_coefficient_cost_floor'] for t in self.result['targets']))

    def test_inherited_source_missing_unit_inverse_channel_or_drift_rejected(self):
        changes=[lambda p:p['selected_source_representation']['cases'][0]['program']['terms'].pop(0),
                 lambda p:p['generated_bound_obligations'].pop(),
                 lambda p:p['complete_source_reduction'].update(transport_error_retained='0'),
                 lambda p:p['prefix_projection_search']['proof_search']['programs'].pop()]
        for change in changes:
            parent=deepcopy(self.parent);change(parent)
            with self.assertRaises((ValueError,KeyError)):CHECK.source_binding(parent,WORK)

    def test_false_closure_target_reference_or_omission_rejected(self):
        bad=deepcopy(self.result)
        bad['targets'][0].update(attempt_id=999,requested_bound_proved=True,status='requested_bound_proved')
        bad['targets'].pop();bad['whole_signed_bound_proved']=True
        with self.assertRaises(ValueError):CHECK.verify_search(self.parent,bad,WORK)

    def test_feedback_full_source_uniform_domain_and_failed_language_retained(self):
        artifact='synthetic/search.json';out=PRODUCER.feedback(self.parent,self.result,artifact)
        self.assertTrue(CHECK.verify_feedback(self.parent,self.result,out,artifact,WORK)['verified'])
        self.assertEqual(out['next_search_tasks'][0]['priority'],0)
        self.assertTrue(all(t['uniform_domain']=='all dyadic B>=1 and every integer B<V<=2B' for t in self.result['targets']))
        bad=deepcopy(out);bad['next_search_tasks'][1].update(arithmetic_bound_refuted=True)
        bad['generated_bound_obligations'].pop();bad['RH_proved']=True
        with self.assertRaises(ValueError):CHECK.verify_feedback(self.parent,self.result,bad,artifact,WORK)


if __name__=='__main__':unittest.main()
