"""Independent rational calibrations and adversarial weighted-height audits."""
from copy import deepcopy
from fractions import Fraction as Q
from math import comb
import time
import unittest

import core_weighted_height_search as PRODUCER
import check_core_weighted_height_search as CHECK
from potential_candidate_language import Meter

START=time.monotonic()
WORK=Meter(50000000,deadline=START+180,max_cells=2000000)


def fixture(alpha=Q(1,6),gamma=Q(1,3)):
    modes=[dict(name='B',coefficient='beta',p=2,q=0,positive_shift='1/3'),
        dict(name='U',coefficient='-beta',p=1,q=1,positive_shift='1/3'),
        dict(name='V',coefficient='-beta',p=1,q=0,positive_shift=None),
        dict(name='power',coefficient='-R_u',p=0,q=1,positive_shift='1/3')]
    cases=[]
    for mode in modes:
        p,q=mode['p'],mode['q'];terms=[]
        for total in range(32):
            for a in range(total+1):
                b=total-a;WORK.charge(5)
                if a*alpha+b*gamma>=1:continue
                ca=comb(p+a-1,a) if p else int(a==0)
                cb=comb(q+b-1,b) if q else int(b==0)
                if ca*cb:terms.append(dict(a=a,b=b,coefficient=str(ca*cb)))
        cases.append(dict(mode=mode,program=dict(alpha=str(alpha),gamma=str(gamma),p=p,q=q,terms=terms)))
    source=dict(id=0,alpha=str(alpha),gamma=str(gamma),cases=cases,
        component_count=sum(len(c['program']['terms']) for c in cases),full_signed_bound_proved=False,RH_proved=False,
        exact_join=dict(all_moment_drifts=[0,1],all_centering_compensations=[0,1],transport_error_coefficient='-1'))
    programs=[];bindings=[]
    for i in range(144):
        transport=dict(id=i,mesh_power=str(Q(1,2+(i%3))))
        programs.append(dict(id=i,transport_program=transport,
            construction=dict(channels=[dict(eta='1/6',polynomial=['0','1'])])))
        bindings.append(dict(parent_obligation_id=i,inherited_binding=dict(transport_program=transport),
            sufficient_goal=dict(p='1',upper='C*(1+log2X)',quantifier='EVERY dyadic X>=1',status='open'),
            whole_signed_bound_proved=False,RH_proved=False))
    parent=dict(schema='core-moment-bound-feedback-v1',status='open',selected_source_representation=source,
        generated_bound_obligations=bindings,retained_original_proof_frontier=[dict(id='full_signed_core',status='open')],
        proof_dependencies=[dict(id='inherited_core',status='open',depends_on=[])],whole_signed_bound_proved=False,RH_proved=False)
    join=CHECK._source(parent,WORK)
    eligible=[t for t in join['collected_terms'] if t['powers'][2]==1 and t['powers'][3]>=2 and
        all(t['powers'][i]==0 for i in (1,4,5,6,7))]
    parent['auxiliary_bound_targets']=[dict(target_id='centered_A'+str(t['powers'][0])+'_E'+str(t['powers'][3]),
        p=t['powers'][0],m=t['powers'][3],theta='2/3',source_term=t,component_bound_proved=False) for t in eligible]
    parent['complete_source_reduction']=dict(inherited_complete_signed_join=join,bindings=bindings,
        transport_error_retained='-e',whole_join_cross_terms_retained=True,
        common_horizon='N=4X-1 for BOTH blocks; same coefficients and cutoffs',new_paid_components=[])
    return parent,dict(complete_signed_join=join,channel_programs=programs)


def line(p=2,m=3,theta=Q(2,3),alpha=Q(1,24),sigma=Q(9,20),spec=None):
    spec=deepcopy(PRODUCER.DEFAULT_SPEC) if spec is None else spec
    value=PRODUCER.line_search(p,m,theta,alpha,sigma,spec,WORK)
    CHECK.verify_line(p,m,theta,alpha,sigma,spec,value,WORK)
    return value


class IndependentWeightedHeightTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.parent,cls.context=fixture()
        cls.spec={**PRODUCER.DEFAULT_SPEC,'sigma_denominator_max':20,'kappa_denominator_max':9}
        cls.result=PRODUCER.search(cls.parent,cls.context,cls.spec,WORK)

    def reject(self,mutate):
        value=deepcopy(self.result);mutate(value)
        with self.assertRaises((ValueError,KeyError,TypeError)):
            CHECK.verify_search(self.parent,self.context,value,WORK)

    def m3(self,value=None):
        return next(t for t in (self.result if value is None else value)['targets'] if t['m']==3)

    def test_independent_high_height_derivation_and_minimum_tau(self):
        value=line()
        self.assertEqual([b['height_power'] for b in value['branches']],['-47/60','-41/60','-7/12','-1/30'])
        selected=value['plans'][value['selected_plan']]
        self.assertEqual((selected['kappa'],selected['epsilon_fraction'],selected['epsilon'],selected['tau']),
            ('2/9','1/4','1/120','45/2'))
        self.assertEqual(selected['high_U_power'],'-1/16')
        self.assertEqual(selected['high_energy_X_power'],'-1/10')
        self.assertEqual(selected['required_low_U_power'],'12/5')
        self.assertEqual(selected['generic_low_energy_X_power'],'31/240')
        self.assertEqual(selected['integer_error_X_power'],'-31/36')
        # The length constraint for j=3 is active, proving minimality of tau.
        self.assertEqual(selected['branches'][3]['length_slack'],'0')

    def test_generic_constant_polynomial_altered_theta_and_fractional_savings(self):
        spec={**PRODUCER.DEFAULT_SPEC,'epsilon_fractions':['1/3','1/6'],'kappa_denominator_max':7}
        value=line(p=0,m=2,theta=Q(3,4),alpha=Q(1,60),sigma=Q(2,5),spec=spec)
        self.assertTrue(value['branches'][0]['coefficient_envelope']['constant_polynomial'])
        self.assertEqual(value['branches'][0]['weight_U_power'],'0')
        self.assertEqual([b['height_power'] for b in value['branches']],['-13/20','-9/20','-1/4'])
        self.assertEqual({p['epsilon_fraction'] for p in value['plans']},{'1/3','1/6'})

    def test_strict_mellin_boundary_and_all_tau_rejections_retained(self):
        for value in (line(sigma=Q(4,9)),line(m=4,sigma=Q(49,100))):
            self.assertIsNone(value['selected_plan']);self.assertEqual(value['plans'],[])
        spec={**PRODUCER.DEFAULT_SPEC,'maximum_tau':'1'}
        value=line(spec=spec)
        self.assertTrue(value['plans']);self.assertIsNone(value['selected_plan'])
        self.assertTrue(all(not p['within_tau_cap'] for p in value['plans']))
        self.assertEqual(value['failed_premises'],['every_valid_common_height_exceeds_declared_tau_cap'])

    def test_low_generic_bound_and_integer_error_are_separate_premises(self):
        value=line(alpha=Q(1,100));plan=value['plans'][value['selected_plan']]
        self.assertTrue(plan['generic_complete_component_proved'])
        self.assertEqual(plan['generic_low_energy_X_power'],'-9/200')
        self.assertEqual(plan['low_obligation_status'],'proved_by_generic_fallback')
        value=line(p=16,m=2,theta=Q(2,5),alpha=Q(1,2),sigma=Q(3,8))
        plan=value['plans'][value['selected_plan']]
        self.assertGreater(Q(plan['integer_error_X_power']),0)
        self.assertFalse(plan['generic_complete_component_proved'])

    def test_independent_tau_epsilon_length_and_branch_cost_tampers(self):
        value=line()
        for mutate in (lambda v:v['plans'][0].update(kappa='1/4'),
                       lambda v:v['plans'][0].update(epsilon='1'),
                       lambda v:v['plans'][0].update(tau='1'),
                       lambda v:v['plans'][0]['branches'][0].update(tail_U_power='0'),
                       lambda v:v['plans'][0]['branches'][3].update(length_slack='1'),
                       lambda v:v['plans'][0].update(generic_low_U_power='0'),
                       lambda v:v['plans'][0].update(high_energy_X_power='-1')):
            bad=deepcopy(value);mutate(bad)
            with self.assertRaises(ValueError):CHECK.verify_line(2,3,Q(2,3),Q(1,24),Q(9,20),PRODUCER.DEFAULT_SPEC,bad,WORK)

    def test_missing_j0_j1_envelope_and_plan_coverage_rejected(self):
        for mutate in (lambda v:v['branches'].pop(0),lambda v:v['branches'].pop(1),
                       lambda v:v['branches'][2]['coefficient_envelope'].update(multiplier='1'),
                       lambda v:v['plans'].pop(),lambda v:v['plans'][0]['branches'].pop(1),
                       lambda v:v.update(selected_plan=0)):
            bad=line();mutate(bad)
            with self.assertRaises(ValueError):CHECK.verify_line(2,3,Q(2,3),Q(1,24),Q(9,20),PRODUCER.DEFAULT_SPEC,bad,WORK)

    def test_exact_nullspace_coverage_and_full_harmonic_unit(self):
        got=PRODUCER.harmonic_null_search(PRODUCER.DEFAULT_SPEC,WORK)
        expected=CHECK._witnesses(PRODUCER.DEFAULT_SPEC,WORK)
        self.assertEqual(got,expected)
        self.assertEqual(got['integer_pairs_examined'],845)
        self.assertEqual([w['dilation'] for w in got['witnesses']],[2,3,4,5,6])
        for witness in got['witnesses']:
            d=witness['dilation'];x,y=Q(witness['x']),Q(witness['y']);q=3
            coeff={1:Q(1)}
            for n in range(q+1,2*q+1):coeff[n]=x;coeff[d*n]=y
            self.assertEqual(sum((a/n for n,a in coeff.items()),Q(0)),1)
            self.assertEqual(max(map(abs,coeff.values())),1)
            self.assertEqual(x+y/d,0)
            self.assertFalse(witness['applies_to_actual_Mobius'])

    def test_empty_amplitude_language_leaves_obstruction_open(self):
        spec={**self.spec,'amplitude_max':1}
        result=PRODUCER.search(self.parent,self.context,spec,WORK)
        self.assertTrue(CHECK.verify_search(self.parent,self.context,result,WORK)['verified'])
        self.assertEqual(result['generic_weight_test']['witnesses'],[])
        node=next(n for n in result['proof_dependencies'] if n['id']=='generic_weight_class_obstruction')
        self.assertEqual(node['status'],'open')
        node['status']='proved'
        with self.assertRaises(ValueError):CHECK.verify_search(self.parent,self.context,result,WORK)

    def test_full_search_low_gram_is_open_with_every_signed_cross(self):
        checked=CHECK.verify_search(self.parent,self.context,self.result,WORK)
        self.assertEqual(checked['targets'],4);self.assertEqual(checked['high_auxiliary_bounds_proved'],2)
        self.assertEqual(checked['new_component_bounds_proved'],0)
        target=self.m3();low=target['low_obligation']
        self.assertEqual(low['status'],'open_actual_Mobius_bound')
        self.assertEqual(len(low['matrix_entries']),16)
        self.assertEqual({(e['j'],e['k']) for e in low['matrix_entries']},{(j,k) for j in range(4) for k in range(4)})
        self.assertEqual(next(e for e in low['matrix_entries'] if (e['j'],e['k'])==(1,2))['contraction'],'9')
        self.assertFalse(target['centering']['ordinary_moment_established_by_inherited_prefix_rule'])
        self.assertEqual(target['source_head_identity']['coefficient'],dict(atom='One',convolution_power=1))

    def test_complete_degree23_inverse_and_144_channel_costs(self):
        parent,context=fixture(Q(1,24),Q(1,2));result=PRODUCER.search(parent,context,self.spec,WORK)
        audit=CHECK.verify_search(parent,context,result,WORK)
        self.assertEqual((audit['targets'],audit['high_auxiliary_bounds_proved']),(22,2))
        target=next(t for t in result['targets'] if t['m']==3)
        self.assertEqual(target['lines'][target['selected_line']]['sigma'],'9/20')
        self.assertEqual(len(target['conditional_recovery_bindings']),144)
        binding=target['conditional_recovery_bindings'][0]
        self.assertEqual(binding['source_coefficient_squared'],'324')
        self.assertEqual(binding['channel_Hardy_constant'],'17956/81')
        self.assertEqual(binding['channel_error_constant'],'324')
        self.assertEqual(binding['low_constant_multiplier'],'18386944')
        self.assertEqual(binding['high_constant_multiplier'],'4596736')
        self.assertEqual(binding['error_constant_multiplier'],'1679616')
        self.assertIsNone(binding['numerical_value'])
        self.assertEqual(result['statistics']['new_component_bounds_proved'],0)
        self.assertTrue(any(t['lines'][t['selected_line']]['plans'][t['lines'][t['selected_line']]['selected_plan']]['generic_complete_component_proved']
            for t in result['targets'] if t['selected_line'] is not None))

    def test_low_head_cross_scope_and_fake_gaussian_replacements_rejected(self):
        for mutate in (lambda t:t.update(low_obligation=None),
                       lambda t:t['low_obligation']['matrix_entries'].pop(),
                       lambda t:t['low_obligation']['matrix_entries'][0].update(contraction='0'),
                       lambda t:t['low_obligation'].update(diagonal_only_allowed=True),
                       lambda t:t['low_obligation'].update(unweighted_Gaussian_substitution_allowed=True),
                       lambda t:t['low_obligation'].update(integer_pairs='only d=e'),
                       lambda t:t['low_obligation']['height'].update(U_power='0'),
                       lambda t:t['low_obligation'].update(status='proved_by_generic_fallback')):
            self.reject(lambda r:mutate(self.m3(r)))

    def test_no_ordinary_moment_drift_unit_or_head_bound_inferred(self):
        for mutate in (lambda t:t['centering'].update(ordinary_moment_established_by_inherited_prefix_rule=True),
                       lambda t:t['centering'].pop('retained_opposite_drift'),
                       lambda t:t['centering'].update(unit_J_theta_1='0'),
                       lambda t:t['centering'].update(pole_at_1_removed_in_complete_E=False),
                       lambda t:t['centering'].update(continuous_small_x_tail='omitted'),
                       lambda t:t['source_head_identity'].update(supplies_full_Gram_bound=True),
                       lambda t:t['source_head_identity']['coefficient'].update(convolution_power=0)):
            self.reject(lambda r:mutate(self.m3(r)))

    def test_unproved_recovery_numeric_constants_and_changed_source_cost_rejected(self):
        for mutate in (lambda t:t.update(new_source_payment=True),
                       lambda t:t['conditional_recovery_bindings'].pop(),
                       lambda t:t['conditional_recovery_bindings'][0].update(source_coefficient_squared='1'),
                       lambda t:t['conditional_recovery_bindings'][0].update(channel_error_constant='0'),
                       lambda t:t['conditional_recovery_bindings'][0].update(high_constant_multiplier='1'),
                       lambda t:t['conditional_recovery_bindings'][0].update(numerical_value='1'),
                       lambda t:t['conditional_recovery_bindings'][0].update(parent_and_child_common_horizon='different N')):
            self.reject(lambda r:mutate(self.m3(r)))

    def test_source_inverse_unit_theta_and_target_membership_rejected(self):
        parent=deepcopy(self.parent)
        parent['selected_source_representation']['cases'][0]['program']['terms'].pop(0)
        with self.assertRaises(ValueError):CHECK.verify_search(parent,self.context,self.result,WORK)
        parent=deepcopy(self.parent);parent['auxiliary_bound_targets'].pop()
        with self.assertRaises(ValueError):CHECK.verify_search(parent,self.context,self.result,WORK)
        parent=deepcopy(self.parent);parent['auxiliary_bound_targets'][1]['theta']='3/4'
        with self.assertRaises(ValueError):CHECK.verify_search(parent,self.context,self.result,WORK)
        parent=deepcopy(self.parent);parent['auxiliary_bound_targets'][1]['component_bound_proved']=True
        with self.assertRaises(ValueError):CHECK.verify_search(parent,self.context,self.result,WORK)
        self.reject(lambda r:r['targets'].pop())
        self.reject(lambda r:r['targets'][0]['source_term'].update(coefficient='1'))

    def test_original_binding_transport_signed_join_and_channels_rejected(self):
        for mutate in (lambda c:c['channel_programs'].pop(),
                       lambda c:c['channel_programs'].append(deepcopy(c['channel_programs'][0])),
                       lambda c:c['channel_programs'][0]['transport_program'].update(mesh_power='1'),
                       lambda c:c['complete_signed_join']['collected_terms'].pop(),
                       lambda c:c['channel_programs'][0]['construction']['channels'][0].update(eta='-1/6')):
            context=deepcopy(self.context);mutate(context)
            with self.assertRaises(ValueError):CHECK.verify_search(self.parent,context,self.result,WORK)
        self.reject(lambda r:r['inherited_bindings'].pop())
        self.reject(lambda r:r['inherited_complete_source_reduction'].update(transport_error_retained='0'))

    def test_graph_cycles_open_low_dependency_and_full_signed_complement(self):
        with self.assertRaises(ValueError):CHECK._audit_graph([dict(id='paid',status='proved',depends_on=['low']),
            dict(id='low',status='open',depends_on=[])],WORK)
        self.reject(lambda r:r['proof_dependencies'][0]['depends_on'].append('actual_signed_core'))
        self.reject(lambda r:next(n for n in r['proof_dependencies'] if n['id']=='route_centered_A2_E3').update(status='proved'))
        self.reject(lambda r:next(n for n in r['proof_dependencies'] if n['id']=='actual_signed_core')['depends_on'].remove('complete_signed_complement'))
        self.reject(lambda r:r.update(whole_signed_bound_proved=True))
        self.reject(lambda r:r['statistics'].update(new_component_bounds_proved=1))

    def test_witness_scope_false_nullness_and_missing_coverage_rejected(self):
        self.reject(lambda r:r['generic_weight_test']['witnesses'].pop())
        self.reject(lambda r:r['generic_weight_test']['witnesses'][0].update(y='0'))
        self.reject(lambda r:r['generic_weight_test']['witnesses'][0].update(c='2'))
        self.reject(lambda r:r['generic_weight_test']['witnesses'][0].update(applies_to_actual_Mobius=True))
        self.reject(lambda r:r['generic_weight_test'].update(integer_pairs_examined=1))

    def test_feedback_preserves_all_inherited_source_and_open_tasks(self):
        value=PRODUCER.feedback(self.parent,self.result,'parent.json','complete.json')
        self.assertTrue(CHECK.verify_feedback(self.parent,self.result,value,'parent.json','complete.json',WORK)['verified'])
        for field in ('auxiliary_bound_targets','weighted_height_targets','generated_bound_obligations','next_search_tasks','retained_original_proof_frontier'):
            bad=deepcopy(value);bad[field].pop()
            with self.assertRaises(ValueError):CHECK.verify_feedback(self.parent,self.result,bad,'parent.json','complete.json',WORK)
        bad=deepcopy(value);bad['RH_proved']=True
        with self.assertRaises(ValueError):CHECK.verify_feedback(self.parent,self.result,bad,'parent.json','complete.json',WORK)

    def test_rule_provenance_limits_and_spec_types_rejected(self):
        self.reject(lambda r:r['supplied_rules']['transfer'].update(below_length_threshold_licensed=True))
        self.reject(lambda r:r['supplied_rules'].update(formal_proof_assistant_verified=True))
        self.reject(lambda r:r.update(actual_source_observations=1))
        self.reject(lambda r:r['spec'].update(sigma_denominator_max=True))
        self.reject(lambda r:r['spec'].update(epsilon_fractions=['1']))


def tearDownModule():
    print('SYNTHETIC_WORK module=test_check_core_weighted_height_search operations='+str(WORK.operations)+
        ' elapsed_seconds='+format(time.monotonic()-START,'.6f'))
