"""Synthetic independent moment/source mutations, never an arithmetic study."""
import copy
import time
import unittest
from fractions import Fraction as Q
from unittest.mock import patch

import check_core_moment_region_search as C
import core_moment_region_search as P
from prime_bank_candidates import Meter

START=time.monotonic()
METER=Meter(150000000,300)
IDS=[r['id'] for r in C.library()]


def fixture():
    targets=[dict(target_id='centered_A2_E'+str(m),p=2,m=m,theta='2/3',
        source_term=dict(powers=[2,0,1,m,0,0,0,0],coefficient=str(Q((-1)**m*9*m,2))),
        component_bound_proved=m==2) for m in (2,3,4)]
    terms=[t['source_term'] for t in targets]
    terms+=[dict(powers=[1,1,1,3,0,1,1,0],coefficient='-9/2')]
    join=dict(collected_terms=terms,transport_error=dict(coefficient='-1',definition='e=f-g'),
              all_compensations_retained=True,source_expansions=['synthetic full inverse history'])
    goal=dict(expression='complete old residual',upper='C*(1+log2X)^3',p='3',
              quantifier='every dyadic X; same parent and child cutoff',status='open')
    programs=[];bindings=[]
    for i in range(144):
        transport=dict(identity='synthetic transport '+str(i),error='-e',unit=True)
        program=dict(id='original_'+str(i),transport_program=transport,
            construction=dict(channels=[dict(eta='1/2',polynomial=['1','-2','3']),
                                        dict(eta='0',polynomial=['1/3'])]))
        programs.append(program)
        bindings.append(dict(parent_obligation_id=program['id'],inherited_binding=dict(transport_program=transport),
            sufficient_goal=copy.deepcopy(goal),
            recovery='S_g<=4*S_Z+4*C_new+2*C_old; S_Z<=4*S_g+4*C_old+2*C_new'))
    # A trusted prior theorem premise, written directly from accepted032.
    # No old producer/search is imported or executed by these tests.
    chosen=dict(alpha='1/4',beta='3/4',base='T',subcritical_padding=True,
        normalized_error_energy=[dict(constant='5509980288',N_power='-7/36',log_degree=4),
                                 dict(constant='23702740992',N_power='-3/4',log_degree=0)])
    transfer=dict(p=2,theta='2/3',rho='1/24',profile='mobius',selected=0,trials=[chosen])
    parent=dict(schema='core-complete-convolution-feedback-v1',
        selected_source_representation=dict(alpha='1/24',unit='delta',common_horizon='N=4X-1'),
        auxiliary_bound_targets=targets,
        complete_source_reduction=dict(inherited_complete_signed_join=join,
            new_paid_components=[dict(target_id=targets[0]['target_id'],source_term=targets[0]['source_term'])]),
        generated_bound_obligations=bindings,
        cutoff_work_targets=[dict(target_id=targets[1]['target_id'],p=2,m=3,theta='2/3',
            source_term=targets[1]['source_term'],head_bound=dict(atom='One',convolution_power=1,c_power=3,
                centered_prefix_U_power='1',centered_prefix_constant='12'))],
        complete_convolution_search=dict(centered_transfer=transfer),
        next_search_tasks=[dict(priority=0,target_id='actual_signed_core',status='open',search_kind='joint_signed_core_control'),
                           dict(priority=1,status='open',search_kind='inherited_drift_join')],
        full_source_history=dict(exact_unit=True,drifts=['all'],discarded_source_terms=[]),
        whole_signed_bound_proved=False,RH_proved=False)
    return parent,dict(complete_signed_join=copy.deepcopy(join),channel_programs=programs)


def trusted_transfer(f,meter):
    expected=fixture()[0]['complete_convolution_search']['centered_transfer']
    C.equal(f,expected,meter,'exact synthetic prior certificate premise')
    return dict(verified=True)


class MomentRegionCheckerTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.parent,cls.context=fixture()
        cls.spec=dict(P.DEFAULT_SPEC,sigma_denominator_max=12)
        cls.result=P.search(cls.parent,cls.context,cls.spec,METER)
        cls.candidate=P.candidate(2,3,'2/3','1/24','7/20',IDS,METER)

    def reject(self,call):
        with self.assertRaises((ValueError,KeyError,TypeError,OverflowError)):call()

    def audit(self,parent,result,context=None):
        context=self.context if context is None else context
        with patch.object(C,'_source',return_value=context['complete_signed_join']),\
             patch.object(C.TRANSFER,'verify_transfer',side_effect=trusted_transfer):
            return C.verify_search(parent,context,result,METER)

    def test_strict_primary_provider_domains_and_unknown_imports(self):
        for row in C.library():
            low=Q(row['lower'])
            self.assertEqual(C.provider_available(row,low),not row['strict'])
            self.assertTrue(C.provider_available(row,low+Q(1,10000)))
            self.assertFalse(C.provider_available(row,low-Q(1,10000)))
            self.assertFalse(C.provider_available(row,Q(1)))
        for ids in (['conjectural_RH'],['moment8','moment2'],['moment4','moment4']):
            self.reject(lambda:C.licensed(ids))
        factors=[dict(real_part='5/8',power='8')]
        expected=P.product_bound(factors,IDS,METER)
        self.assertTrue(C.verify_product_bound(factors,IDS,expected,METER)['verified'])
        self.assertNotEqual(expected['best']['factors'][0]['provider_id'],'moment8')

    def test_independent_active_constraints_cover_degenerate_and_slanted_vertices(self):
        vertices=C.allocation_vertices((Q(3,4),Q(1,2),Q(0)),METER)
        self.assertIn((Q(3,4),Q(1,4),Q(0)),vertices)
        self.assertIn((Q(1,2),Q(1,2),Q(0)),vertices)
        self.assertEqual(len(vertices),5)
        self.assertTrue(all(sum(v)<=1 and v[2]==0 for v in vertices))

    def test_fractional_absolute_moments_and_four_factor_budget(self):
        factors=[dict(real_part='3/4',power=p) for p in ('1/2','1/3','1/6')]
        result=P.product_bound(factors,IDS,METER)
        C.verify_product_bound(factors,IDS,result,METER)
        self.assertEqual(result['best']['epsilon_coefficient'],'1/12')
        self.assertEqual(result['best']['holder_unused'],'11/12')
        factors=[dict(real_part='3/4',power='1/3')]*4
        result=P.product_bound(factors,['moment2','moment4'],METER)
        C.verify_product_bound(factors,['moment2','moment4'],result,METER)
        self.assertEqual(result['best']['holder_unused'],'2/3')

    def test_reflection_cost_and_optimum_cannot_be_forged(self):
        factors=[dict(real_part='7/20',power='6'),dict(real_part='41/60',power='2')]
        result=P.product_bound(factors,IDS,METER)
        C.verify_product_bound(factors,IDS,result,METER)
        self.assertTrue(result['best']['factors'][0]['reflected'])
        self.assertEqual(result['best']['factors'][0]['reflection_height_power'],'9/10')
        for field,value in (('integral_height_power','1'),('epsilon_coefficient','0'),('holder_unused','-1')):
            bad=copy.deepcopy(result);bad['best'][field]=value
            self.reject(lambda:C.verify_product_bound(factors,IDS,bad,METER))
        bad=copy.deepcopy(result);bad['allocations_examined']-=1
        self.reject(lambda:C.verify_product_bound(factors,IDS,bad,METER))

    def test_height_boundary_epsilon_and_lower_branch_cannot_be_dropped(self):
        boundary=P.candidate(2,3,'2/3','1/24','1/3',IDS,METER)
        C.verify_candidate(2,3,'2/3','1/24','1/3',IDS,boundary,METER)
        self.assertEqual(boundary['mellin_height_powers'][1],'0')
        self.assertFalse(boundary['target_met'])
        C.verify_candidate(2,3,'2/3','1/24','7/20',IDS,self.candidate,METER)
        for field,value in (('epsilon','1'),('paid_height_powers',['-1','-1']),('target_met',False)):
            bad=copy.deepcopy(self.candidate);bad[field]=value
            self.reject(lambda:C.verify_candidate(2,3,'2/3','1/24','7/20',IDS,bad,METER))
        bad=copy.deepcopy(self.candidate);bad['moment_branches'].pop(0)
        self.reject(lambda:C.verify_candidate(2,3,'2/3','1/24','7/20',IDS,bad,METER))

    def test_analytic_cubic_center_does_not_claim_ordinary_convergence(self):
        self.assertTrue(self.candidate['target_met'])
        self.assertEqual(self.candidate['full_finite_factor_U_power'],'13/2')
        self.assertEqual(self.candidate['recovered_energy_N_power'],'-7/240')
        self.assertFalse(self.candidate['centering']['ordinary_coefficient_moment_required'])
        for field,value in (('ordinary_coefficient_moment_claimed',True),('whole_x_below_one_tail_included',False),
                            ('unit_included',False),('exact_moment','0')):
            bad=copy.deepcopy(self.candidate);bad['centering'][field]=value
            self.reject(lambda:C.verify_candidate(2,3,'2/3','1/24','7/20',IDS,bad,METER))

    def test_fractional_kernel_cells_and_energy_zero_vs_strict_height(self):
        changed=P.candidate(1,2,'5/6','1/48','3/8',IDS,METER)
        C.verify_candidate(1,2,'5/6','1/48','3/8',IDS,changed,METER)
        self.assertEqual(changed['integer_cell_correction']['residue_denominator'],'13/12')
        boundary=P.candidate(2,3,'2/3','1/24','7/19',IDS,METER)
        C.verify_candidate(2,3,'2/3','1/24','7/19',IDS,boundary,METER)
        self.assertEqual(boundary['recovered_energy_N_power'],'0')
        self.assertTrue(boundary['target_met'])
        expensive=P.candidate(2,3,'2/3','1/4','7/20',IDS,METER)
        C.verify_candidate(2,3,'2/3','1/4','7/20',IDS,expensive,METER)
        self.assertFalse(expensive['target_met'])

    def test_moment_library_ablation_changes_component_feasibility(self):
        target=self.parent['auxiliary_bound_targets'][1]
        spec=dict(self.spec,library_ids=['moment2','moment4'])
        old=P.target_search(target,Q(1,24),spec,METER)
        self.assertIsNone(old['selected'])
        new=self.result['targets'][1]
        self.assertIsNotNone(new['selected'])
        join=dict(collected_terms=[target['source_term']])
        small=copy.deepcopy(self.parent);small['auxiliary_bound_targets']=[target]
        small['complete_source_reduction']['new_paid_components']=[]
        C.verify_targets(small,join,[old],spec,METER)

    def test_optimistic_moment_floor_is_only_a_grammar_obstruction(self):
        self.assertEqual(C.optimistic_diagnostic(2,4,Q(1,24))['optimistic_energy_infimum'],'1/16')
        self.assertFalse(C.optimistic_diagnostic(2,3,Q(1,24))['stronger_moment_library_alone_insufficient'])
        for rho in (Q(1,2),Q(3,4)):
            record=C.optimistic_diagnostic(2,4,rho)
            self.assertGreaterEqual(Q(record['optimistic_energy_infimum']),0)
            self.assertTrue(record['cutoff_alone_obstructs'])
            self.assertFalse(record['arithmetic_impossibility_claimed'])
        bad=copy.deepcopy(self.result['targets']);bad[2]['optimistic_moment_diagnostic']['arithmetic_impossibility_claimed']=True
        self.reject(lambda:C.verify_targets(self.parent,self.context['complete_signed_join'],bad,self.spec,METER))

    def test_three_synthetic_targets_all144_bindings_and_cube_are_independently_verified(self):
        audit=self.audit(self.parent,self.result)
        self.assertEqual(audit['original_bindings'],144)
        self.assertEqual(audit['new_source_payments'],1)
        self.assertTrue(audit['finite_cube_bound_proved'])
        self.assertFalse(audit['whole_signed_bound_proved'])

    def test_complete_ast_coverage_scalar_kernel_and_inherited_paid_status(self):
        join=self.context['complete_signed_join']
        for field,value in (('theta','5/6'),('component_bound_proved',False)):
            bad=copy.deepcopy(self.parent);bad['auxiliary_bound_targets'][0][field]=value
            self.reject(lambda:C.verify_targets(bad,join,self.result['targets'],self.spec,METER))
        bad=copy.deepcopy(self.parent);bad['auxiliary_bound_targets'].pop()
        self.reject(lambda:C.verify_targets(bad,join,self.result['targets'],self.spec,METER))
        bad=copy.deepcopy(self.parent);bad['auxiliary_bound_targets'][0]['source_term']['coefficient']='1'
        self.reject(lambda:C.verify_targets(bad,join,self.result['targets'],self.spec,METER))
        bad=copy.deepcopy(self.result['targets']);bad[0]['new_source_payment']=True
        self.reject(lambda:C.verify_targets(self.parent,join,bad,self.spec,METER))

    def test_recovery_retains_opposite_drift_hardy_cost_and_correct_reverse(self):
        reduction=self.result['source_reduction']
        C.verify_reduction(self.parent,self.context,self.result['targets'],reduction,METER)
        cost=reduction['bindings'][0]['paid_constant_terms'][0]
        self.assertEqual(cost['local_cutoff_constant'],'8')
        self.assertGreater(Q(cost['rational_multiplier']),Q(27,2)**2)
        self.assertEqual(reduction['bindings'][0]['reverse'],'S_Z033<=8*S_g+8*C_old+4*C_prev+2*C_033')
        for part in ('paid_components','bindings'):
            bad=copy.deepcopy(reduction);bad[part].pop()
            self.reject(lambda:C.verify_reduction(self.parent,self.context,self.result['targets'],bad,METER))
        bad=copy.deepcopy(reduction);bad['paid_components'][0]['retained_opposite_drift']='0'
        self.reject(lambda:C.verify_reduction(self.parent,self.context,self.result['targets'],bad,METER))
        bad=copy.deepcopy(reduction);bad['bindings'][0]['paid_constant_terms'][0]['rational_multiplier']='1'
        self.reject(lambda:C.verify_reduction(self.parent,self.context,self.result['targets'],bad,METER))
        bad=copy.deepcopy(self.parent);bad['generated_bound_obligations'][0]['sufficient_goal']['p']='-1'
        self.reject(lambda:C.verify_reduction(bad,self.context,self.result['targets'],reduction,METER))

    def test_missing_channels_changed_transport_and_cycle_are_rejected(self):
        bad=copy.deepcopy(self.context);bad['channel_programs'].pop()
        self.reject(lambda:C.verify_reduction(self.parent,bad,self.result['targets'],self.result['source_reduction'],METER))
        bad=copy.deepcopy(self.context);bad['channel_programs'][0]['transport_program']['unit']=False
        self.reject(lambda:C.verify_reduction(self.parent,bad,self.result['targets'],self.result['source_reduction'],METER))
        cycle={};cycle['inherited_binding']=cycle
        self.reject(lambda:C.original_transport(cycle))
        self.assertEqual(C.channel_constant([dict(eta='0',polynomial=['1','-2'])],Q(1,2),METER),Q(225))

    def test_finite_cube_composition_keeps_head_moment_and_both_padding_terms(self):
        cube=self.result['cube_composition']
        with patch.object(C.TRANSFER,'verify_transfer',side_effect=trusted_transfer) as prior:
            C.verify_cube(self.parent,self.result['targets'],cube,METER)
            self.assertTrue(prior.called)
            self.assertEqual([r['multiplier'] for r in cube['finite_cube_energy_terms']],
                             ['4','576','11019960576','47405481984'])
            for field,value in (('ordinary_cubic_coefficient_moment_claimed',True),
                                ('original_fixed_sigma_low_Gram_proved',True),('same_head_and_full_moment_defect_retained',False)):
                bad=copy.deepcopy(cube);bad[field]=value
                self.reject(lambda:C.verify_cube(self.parent,self.result['targets'],bad,METER))
            bad=copy.deepcopy(cube);bad['finite_cube_energy_terms'].pop()
            self.reject(lambda:C.verify_cube(self.parent,self.result['targets'],bad,METER))
            bad=copy.deepcopy(self.parent);bad['cutoff_work_targets'][0]['head_bound']['atom']='delta'
            self.reject(lambda:C.verify_cube(bad,self.result['targets'],cube,METER))

    def test_proof_graph_is_acyclic_and_paid_nodes_have_no_open_dependency(self):
        graph=self.result['proof_dependencies'];cube=self.result['cube_composition']
        C.verify_graph(graph,self.result['targets'],cube,METER)
        for ident,dep in (('analytic_residue_bridge','finite_cube'),('supplied_moments','remaining_joint_residual')):
            bad=copy.deepcopy(graph);node=next(n for n in bad if n['id']==ident);node['dependencies']=[dep]
            self.reject(lambda:C.verify_graph(bad,self.result['targets'],cube,METER))
        bad=copy.deepcopy(graph);bad[-1]['proved']=True
        self.reject(lambda:C.verify_graph(bad,self.result['targets'],cube,METER))

    def test_feedback_preserves_full_parent_and_new_mechanism_frontier(self):
        out=P.feedback(self.parent,self.result,'proof033.json')
        C.verify_feedback(self.parent,self.result,out,'proof033.json',METER)
        task=next(t for t in out['next_search_tasks'] if t.get('target_id')=='centered_A2_E4')
        self.assertTrue(task['moment_library_alone_insufficient'])
        self.assertTrue(task['requirement'].startswith('signed finite-factor'))
        self.assertEqual(out['next_search_tasks'][0]['priority'],0)
        for field in ('generated_bound_obligations','full_source_history','complete_source_reduction'):
            bad=copy.deepcopy(out);bad.pop(field)
            self.reject(lambda:C.verify_feedback(self.parent,self.result,bad,'proof033.json',METER))
        bad=copy.deepcopy(out);bad['next_search_tasks'][-1]['status']='proved'
        self.reject(lambda:C.verify_feedback(self.parent,self.result,bad,'proof033.json',METER))

    def test_generic_ablation_not_arithmetic_gain_and_source_context_cannot_change(self):
        self.assertFalse(self.result['ablation']['arithmetic_power_advantage'])
        self.assertEqual(self.result['ablation']['additional_logU_loss'],0)
        bad=copy.deepcopy(self.result);bad['ablation']['arithmetic_power_advantage']=True
        # Isolate the publication envelope from the already tested expensive
        # primitive audits; the final strict record check must still reject it.
        with patch.object(C,'_source',return_value=self.context['complete_signed_join']),\
             patch.object(C,'verify_targets'),patch.object(C,'verify_reduction'),\
             patch.object(C,'verify_cube'),patch.object(C,'verify_graph'):
            self.reject(lambda:C.verify_search(self.parent,self.context,bad,METER))
            false_closure=copy.deepcopy(self.result);false_closure['whole_signed_bound_proved']=True
            self.reject(lambda:C.verify_search(self.parent,self.context,false_closure,METER))
        context=copy.deepcopy(self.context);context['complete_signed_join']['all_compensations_retained']=False
        with patch.object(C,'_source',return_value=self.context['complete_signed_join']):
            self.reject(lambda:C.verify_search(self.parent,context,self.result,METER))
        parent=copy.deepcopy(self.parent);parent['RH_proved']=True
        self.reject(lambda:C.verify_search(parent,self.context,self.result,METER))

    def test_charge_only_meter_and_bounded_input_guards(self):
        meter=Meter(1000000,60);self.assertFalse(hasattr(meter,'number'))
        f=[dict(real_part='3/4',power='1/3')];r=P.product_bound(f,['moment2'],METER)
        C.verify_product_bound(f,['moment2'],r,meter);METER.charge(meter.operations)
        with self.assertRaises(OverflowError):C.verify_product_bound(f,['moment2'],r,Meter(0,60))
        for f in ([dict(real_part='1',power='2')],[dict(real_part='3/4',power='0')],
                  [dict(real_part='3/4',power='129')]):
            self.reject(lambda:C.product_optimum(f,IDS,METER))
        self.reject(lambda:C.rational('01/02',METER))
        self.reject(lambda:C.verify_candidate(True,3,'2/3','1/24','7/20',IDS,self.candidate,METER))


def tearDownModule():
    print('SYNTHETIC_WORK module=test_check_core_moment_region_search operations='+str(METER.operations)+
          ' elapsed_seconds='+str(time.monotonic()-START))


if __name__=='__main__':unittest.main()
