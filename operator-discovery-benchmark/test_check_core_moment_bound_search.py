"""Exact simplex calibration, analytical boundaries, and source tampering."""
from copy import deepcopy
from fractions import Fraction as Q
from math import comb
import time
import unittest

import core_moment_bound_search as PRODUCER
import check_core_moment_bound_search as CHECK
from potential_candidate_language import Meter

START=time.monotonic()
WORK=Meter(50000000,deadline=START+180,max_cells=2000000)

MODES=[dict(name='B',coefficient='beta',p=2,q=0,positive_shift='1/3'),
       dict(name='U',coefficient='-beta',p=1,q=1,positive_shift='1/3'),
       dict(name='V',coefficient='-beta',p=1,q=0,positive_shift=None),
       dict(name='power',coefficient='-R_u',p=0,q=1,positive_shift='1/3')]


def fixture(alpha=Q(1,6),gamma=Q(1,3)):
    cases=[]
    for mode in MODES:
        p,q=mode['p'],mode['q'];terms=[]
        for total in range(32):
            for a in range(total+1):
                b=total-a;WORK.charge(5)
                if a*alpha+b*gamma>=1:continue
                ca=comb(p+a-1,a) if p else int(a==0)
                cb=comb(q+b-1,b) if q else int(b==0)
                if ca*cb:terms.append(dict(a=a,b=b,coefficient=str(ca*cb)))
        cases.append(dict(mode=deepcopy(mode),program=dict(alpha=str(alpha),gamma=str(gamma),p=p,q=q,terms=terms)))
    source=dict(id=0,alpha=str(alpha),gamma=str(gamma),cases=cases,
        component_count=sum(len(c['program']['terms']) for c in cases),full_signed_bound_proved=False,RH_proved=False,
        exact_join=dict(all_moment_drifts=[0,1],all_centering_compensations=[0,1],transport_error_coefficient='-1'))
    old=[];programs=[]
    for i in range(144):
        transport=dict(id=i,mesh_power=str(Q(1,2+(i%3))))
        old.append(dict(parent_obligation_id=i,transport_program=transport,
            sufficient_goal=dict(upper='C*(1+log2X)^p',p='1',quantifier='one fixed finite C; EVERY dyadic X>=1',status='open'),
            recovery='S_g<=2*S_R+2*C_old; S_R<=2*S_g+2*C_old',whole_signed_bound_proved=False,RH_proved=False))
        programs.append(dict(id=i,transport_program=transport,construction=dict(channels=[
            dict(eta='1/2',polynomial=['1','-2','0','3']),dict(eta='0',polynomial=['-2'])])))
    parent=dict(selected_source_representation=source,generated_bound_obligations=old,
        retained_original_proof_frontier=[dict(id='full_signed_core',status='open'),dict(id='old_frame_conditions',status='open')],
        whole_signed_bound_proved=False,RH_proved=False)
    join=CHECK._source(parent,WORK)
    eligible=[t for t in join['collected_terms'] if t['powers'][2]==1 and t['powers'][3]>=2 and
        all(t['powers'][i]==0 for i in (1,4,5,6,7))]
    parent['auxiliary_bound_targets']=[dict(id='centered_A'+str(t['powers'][0])+'_E'+str(t['powers'][3]),
        p=t['powers'][0],m=t['powers'][3],theta='2/3',source_term=t,status='open') for t in eligible]
    return parent,dict(complete_signed_join=join,channel_programs=programs)


def generic(factors,orders=['2','4']):
    result=PRODUCER.product_moment_search(factors,orders,WORK)
    CHECK.verify_product_moment(factors,orders,result,WORK)
    return result


class IndependentMomentBoundTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.parent,cls.context=fixture()
        cls.spec=deepcopy(PRODUCER.DEFAULT_SPEC);cls.spec['sigma_denominator_max']=8
        cls.result=PRODUCER.search(cls.parent,cls.context,cls.spec,WORK)

    def reject(self,mutation):
        v=deepcopy(self.result);mutation(v)
        with self.assertRaises((ValueError,KeyError,TypeError)):
            CHECK.verify_search(self.parent,self.context,v,WORK)

    def test_active_constraint_vertices_fractional_and_degenerate(self):
        expected=[(Q(0),Q(0)),(Q(0),Q(3,4)),(Q(1,4),Q(3,4)),(Q(3,4),Q(0)),(Q(3,4),Q(1,4))]
        self.assertEqual(CHECK.allocation_vertices([Q(3,4),Q(3,4)],WORK),expected)
        self.assertEqual(CHECK.allocation_vertices([0,Q(2,5)],WORK),[(Q(0),Q(0)),(Q(0),Q(2,5))])
        upper=[Q(1,4),Q(1,3),Q(1,2),Q(0)]
        vertices=CHECK.allocation_vertices(upper,WORK)
        self.assertEqual(vertices,PRODUCER.holder_vertices(upper))
        self.assertTrue(any(sum(v)==1 for v in vertices));self.assertTrue(all(v[-1]==0 for v in vertices))

    def test_fractional_product_uses_unused_Holder_mass_without_integer_rounding(self):
        factors=[dict(real_part='3/5',power='1/2'),dict(real_part='7/10',power='3/2'),dict(real_part='4/5',power='7/4')]
        result=generic(factors)
        self.assertEqual(result['best']['integral_height_power'],'1')
        self.assertEqual(result['best']['epsilon_coefficient'],'15/16')
        self.assertEqual(result['best']['holder_unused'],'1/16')
        self.assertEqual([f['holder_weight'] for f in result['best']['factors']],['1/8','3/8','7/16'])

    def test_reflection_and_moment_order_ablation_change_proved_exponent(self):
        factors=[dict(real_part='1/4',power='4')]
        powers=[generic(factors,orders)['best']['integral_height_power'] for orders in ([],['2'],['4'])]
        self.assertEqual(powers,['5/2','9/4','2'])
        best=generic(factors,['4'])['best']['factors'][0]
        self.assertTrue(best['reflected']);self.assertEqual(best['reflection_height_power'],'1')
        self.assertEqual(best['effective_real_part'],'3/4')

    def test_four_generic_factors_and_unlicensed_moment_library(self):
        factors=[dict(real_part=str(a),power=str(b)) for a,b in
            ((Q(1,5),Q(1,3)),(Q(2,5),Q(2,3)),(Q(3,5),Q(3,2)),(Q(4,5),Q(5,2)))]
        result=generic(factors,[])
        self.assertEqual(len(result['best']['factors']),4)
        self.assertTrue(all(f['moment_order']=='0' for f in result['best']['factors']))
        with self.assertRaises(ValueError):CHECK.verify_product_moment(factors,['8'],result,WORK)
        with self.assertRaises(ValueError):CHECK.verify_product_moment([dict(real_part='1',power='2')],[],result,WORK)

    def test_product_optimizer_false_allocation_coverage_and_cost_rejected(self):
        factors=[dict(real_part='1/4',power='4'),dict(real_part='7/12',power='2')]
        result=generic(factors)
        variants=[]
        v=deepcopy(result);v['allocations_examined']-=1;variants.append(v)
        v=deepcopy(result);v['best']['integral_height_power']='0';variants.append(v)
        v=deepcopy(result);v['best']['factors'][0]['holder_weight']='2';variants.append(v)
        v=deepcopy(result);v['best']['factors'][0]['convexity_power']='-1';variants.append(v)
        v=deepcopy(result);v['best']['epsilon_coefficient']='0';variants.append(v)
        for v in variants:
            with self.assertRaises(ValueError):CHECK.verify_product_moment(factors,['2','4'],v,WORK)

    def test_strict_Mellin_height_boundary_and_zero_energy_are_distinct(self):
        for sigma,strict,energy in [(Q(1,3),False,Q(-1,9)),(Q(3,8),True,Q(-1,24)),(Q(2,5),True,Q(0))]:
            c=PRODUCER.candidate(2,2,Q(2,3),Q(1,24),sigma,['2','4'],Q(0),WORK)
            CHECK._candidate(2,2,Q(2,3),Q(1,24),sigma,['2','4'],Q(0),c,WORK,{})
            self.assertEqual(c['strict_tail_summation'],strict);self.assertEqual(Q(c['recovered_energy_X_power']),energy)
            self.assertEqual(c['target_met'],strict)
            if strict:
                for h,b in zip(c['mellin_height_powers'],c['moment_branches']):
                    self.assertLess(Q(h)+Q(c['epsilon'])*Q(b['best']['epsilon_coefficient']),0)
            else:self.assertIsNone(c['epsilon'])

    def test_full_grid_and_unpaid_source_recovery_all_144_routes(self):
        audit=CHECK.verify_search(self.parent,self.context,self.result,WORK)
        self.assertEqual((audit['targets'],audit['new_component_bounds_proved'],audit['inherited_bindings']),(4,0,144))
        self.assertEqual(self.result['source_reduction']['new_paid_components'],[])
        self.assertEqual(self.result['source_reduction']['bindings'][0]['recovery'],self.parent['generated_bound_obligations'][0]['recovery'])
        self.assertEqual(len(self.result['next_search_tasks']),5)

    def test_full_degree_23_source_new_payment_symbolic_constant_and_Hardy_cost(self):
        parent,context=fixture(Q(1,24),Q(1,2));result=PRODUCER.search(parent,context,self.spec,WORK)
        audit=CHECK.verify_search(parent,context,result,WORK)
        self.assertEqual((audit['targets'],audit['new_component_bounds_proved']),(22,1))
        t=result['targets'][0];self.assertEqual(t['m'],2)
        chosen=t['candidate_lines'][t['selected']]
        self.assertEqual((chosen['sigma'],chosen['recovered_energy_X_power'],chosen['full_finite_factor_U_power']),('3/8','-1/24','5'))
        self.assertIsNone(t['proof_constant']['numerical_value'])
        binding=result['source_reduction']['bindings'][0];cost=binding['new_paid_constant']['terms'][0]
        self.assertEqual(cost['channel_Hardy_constant'],'270436/9')
        self.assertEqual(cost['local_and_cutoff_constant'],'8')
        self.assertEqual(cost['rational_multiplier'],'43810632')
        self.assertEqual(Q(t['source_term']['coefficient']),Q(27,2))
        self.assertIn('4*S_Z+4*C_new+2*C_old',binding['recovery'])
        self.assertEqual(result['source_reduction']['new_paid_components'][0]['retained_opposite_drift'],
            'source_coefficient*M/theta*J_theta')
        self.assertTrue(all(not t['component_bound_proved'] for t in result['targets'][1:]))
        for mutate in (lambda r:r['source_reduction']['new_paid_components'][0].pop('retained_opposite_drift'),
                       lambda r:r['targets'][0]['proof_constant'].update(numerical_value='1'),
                       lambda r:r['source_reduction']['bindings'][0]['new_paid_constant']['terms'][0].update(rational_multiplier='1')):
            v=deepcopy(result);mutate(v)
            with self.assertRaises((ValueError,KeyError)):CHECK.verify_search(parent,context,v,WORK)

    def test_higher_degree_ordinary_moment_not_supplied_by_analytic_residue(self):
        c=PRODUCER.candidate(2,3,Q(2,3),Q(1,100),Q(9,20),['2','4'],Q(0),WORK)
        CHECK._candidate(2,3,Q(2,3),Q(1,100),Q(9,20),['2','4'],Q(0),c,WORK,{})
        self.assertTrue(c['strict_tail_summation']);self.assertFalse(c['target_met'])
        self.assertEqual(c['failed_premises'],['ordinary_centering_moment_unproved'])
        self.assertEqual(c['complete_centering']['residual_prefix_power'],'2/3')
        v=deepcopy(c);v['complete_centering']['ordinarily_convergent']=True
        with self.assertRaises(ValueError):CHECK._candidate(2,3,Q(2,3),Q(1,100),Q(9,20),['2','4'],Q(0),v,WORK,{})

    def test_candidate_bounds_retain_unit_tail_pole_and_finite_weight_cost(self):
        self.reject(lambda r:r['targets'][0]['candidate_lines'][0].update(full_unit_and_small_x_tail_retained=False))
        self.reject(lambda r:r['targets'][0]['candidate_lines'][0].update(pole_removal='ignore the pole at1'))
        self.reject(lambda r:r['targets'][0]['candidate_lines'][0].update(full_finite_factor_U_power='0'))
        self.reject(lambda r:r['targets'][0]['candidate_lines'][0]['complete_centering'].update(full_infinite_tail_retained=False))
        self.reject(lambda r:r['targets'][0]['candidate_lines'][0].update(constants_uniform_in=['X']))

    def test_dropped_branch_false_epsilon_and_contour_coverage_rejected(self):
        self.reject(lambda r:r['targets'][0]['candidate_lines'][0]['moment_branches'].pop())
        self.reject(lambda r:r['targets'][0]['candidate_lines'].pop())
        self.reject(lambda r:r['targets'][0]['candidate_lines'][0].update(epsilon='1'))
        self.reject(lambda r:r['targets'][0]['candidate_lines'][0].update(strict_tail_summation=True))
        self.reject(lambda r:r['targets'][0].update(selected=0,component_bound_proved=True))

    def test_actual_target_kernel_source_coefficient_and_complete_membership(self):
        self.reject(lambda r:r['targets'].pop())
        self.reject(lambda r:r['targets'][0]['source_term'].update(coefficient='1'))
        parent=deepcopy(self.parent);parent['auxiliary_bound_targets'][0]['theta']='3/4'
        with self.assertRaises(ValueError):CHECK.verify_search(parent,self.context,self.result,WORK)
        parent=deepcopy(self.parent);parent['auxiliary_bound_targets'][0]['source_term']['powers'][1]=1
        with self.assertRaises(ValueError):CHECK.verify_search(parent,self.context,self.result,WORK)
        context=deepcopy(self.context);context['complete_signed_join']['collected_terms'].pop()
        with self.assertRaises(ValueError):CHECK.verify_search(self.parent,context,self.result,WORK)

    def test_old_channel_route_missing_duplicate_or_changed_transport_rejected(self):
        for mutate in (lambda c:c['channel_programs'].pop(),
                       lambda c:c['channel_programs'].append(deepcopy(c['channel_programs'][0])),
                       lambda c:c['channel_programs'][0]['transport_program'].update(mesh_power='1')):
            context=deepcopy(self.context);mutate(context)
            with self.assertRaises(ValueError):CHECK.verify_search(self.parent,context,self.result,WORK)
        self.reject(lambda r:r['source_reduction']['bindings'].pop())
        self.reject(lambda r:r['source_reduction']['inherited_complete_signed_join']['transport_error'].update(coefficient='0'))

    def test_provenance_fabricated_numeric_constant_and_false_core_closure_rejected(self):
        self.reject(lambda r:r['supplied_rules']['imported_fourth_moment'].update(status='conjecture'))
        self.reject(lambda r:r['supplied_rules']['analytic_bridge'].update(formal_proof_assistant_verified=True))
        self.reject(lambda r:r.update(fitted_constants=1))
        self.reject(lambda r:r.update(whole_signed_bound_proved=True))
        self.reject(lambda r:r['statistics'].update(new_component_bounds_proved=1))

    def test_imported_rule_graph_cycles_open_dependency_and_signed_complement(self):
        with self.assertRaises(ValueError):CHECK._audit_graph([dict(id='a',status='proved',depends_on=['b']),
            dict(id='b',status='open',depends_on=[])],WORK)
        with self.assertRaises(ValueError):CHECK._audit_graph([dict(id='a',status='reviewed_and_imported',depends_on=['b']),
            dict(id='b',status='proved',depends_on=['a'])],WORK)
        self.reject(lambda r:r['proof_dependencies'][0]['depends_on'].append('actual_signed_core'))
        self.reject(lambda r:r['proof_dependencies'][-2]['depends_on'].remove('complete_signed_complement'))
        self.reject(lambda r:r['proof_dependencies'][1].update(status='proved'))

    def test_feedback_retains_complete_Z_original_frontier_and_unpaid_moments(self):
        feedback=PRODUCER.feedback(self.parent,self.result,'parent.json','complete.json')
        self.assertTrue(CHECK.verify_feedback(self.parent,self.result,feedback,'parent.json','complete.json',WORK)['verified'])
        for field in ('auxiliary_bound_targets','generated_bound_obligations','retained_original_proof_frontier','next_search_tasks'):
            v=deepcopy(feedback);v[field].pop()
            with self.assertRaises(ValueError):CHECK.verify_feedback(self.parent,self.result,v,'parent.json','complete.json',WORK)
        v=deepcopy(feedback);v['RH_proved']=True
        with self.assertRaises(ValueError):CHECK.verify_feedback(self.parent,self.result,v,'parent.json','complete.json',WORK)


def tearDownModule():
    print('SYNTHETIC_WORK module=test_check_core_moment_bound_search operations='+str(WORK.operations)+
        ' elapsed_seconds='+format(time.monotonic()-START,'.6f'))
