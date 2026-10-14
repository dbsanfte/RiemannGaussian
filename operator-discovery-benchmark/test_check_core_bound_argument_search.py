"""Exact independent calibrations and adversarial replay; no source archive."""
import copy
import math
import time
import unittest
from fractions import Fraction as Q
from unittest.mock import patch

import check_core_bound_argument_search as CHECK
import core_bound_argument_search as PRODUCER
from prime_bank_candidates import Meter

START = time.monotonic()
WORK = Meter(50000000, 180)


def tearDownModule():
    print('SYNTHETIC_WORK module=test_check_core_bound_argument_search operations=' +
          str(WORK.operations) + ' elapsed_seconds=' + str(time.monotonic()-START), flush=True)


def plan(kind='variance', theta=0, profile='bounded', **kw):
    return PRODUCER.plan(PRODUCER.goal(kind,theta,profile,
                         kw.pop('support_power',0),kw.pop('l1_power',0)),WORK,**kw)


def fixture():
    """Wrapper tests isolate the existing source-publication trust boundary."""
    binding = dict(target_id='synthetic_complete_component', bindings=list(range(144)),
                   drifts=['signed_drift'], unit=1, transport='-e')
    parent = dict(schema='core-signed-primitive-feedback-v1',
        signed_primitive_search=dict(binding=binding),
        cutoff_work_targets=[dict(p=2,m=3,sigma='9/20',theta='2/3',
            original_low_obligation=dict(required_upper=dict(U_power='12/5',log_degree=0),
                                         status='open',uniform_domain='all integer U>=1'))],
        source_fixture=dict(unit=1,transport='-e',all_source_rows=['signed original','centering drift'],
                            original_channel_ids=list(range(144)),failed_alternatives=['retained']),
        next_search_tasks=[dict(priority=0,target_id='actual_signed_core',status='open'),
                           dict(priority=1,target_id='retained_old_task',status='open')],
        whole_signed_bound_proved=False,RH_proved=False)
    with patch.object(PRODUCER,'source_binding',return_value=binding):
        result = PRODUCER.search(parent,WORK)
    return parent,binding,result


class IndependentBoundArgumentTests(unittest.TestCase):
    def rejected_plan(self, result):
        with self.assertRaises(ValueError):
            CHECK.verify_plan(result,WORK)

    def test_exact_discrete_period_identity_including_jump_values(self):
        cases = [([1],1),([1,-1,-1,0,-1],1),
                 ([Q(1,3),Q(-2,7),Q(5,11),Q(-3,2)],Q(7,5)),
                 ([0,1,0,-1,1,-1],-2)]
        for weights,constant in cases:
            result = PRODUCER.compile_sawtooth(weights,WORK,constant)
            self.assertTrue(CHECK.verify_compiler(weights,constant,result,WORK)['verified'])
            period = math.lcm(*range(1,len(weights)+1))
            values = [Q(constant)+sum((Q(w)*Q(n%d,d) for d,w in enumerate(weights,1)),Q(0))
                      for n in range(period)]
            mean = sum(values)/period
            variance = sum((v-mean)**2 for v in values)/period
            self.assertEqual(Q(result['mean']),mean)
            self.assertEqual(Q(result['variance']),variance)
            WORK.charge(period*len(weights)*20)

    def test_equal_frequency_sign_cancellation_and_mean_unit(self):
        weights = [1,Q(1,2),0,-1]
        result = PRODUCER.compile_sawtooth(weights,WORK,3)
        CHECK.verify_compiler(weights,3,result,WORK)
        self.assertEqual([row['r'] for row in result['conductors']],[4])
        self.assertEqual(result['conductors'][0]['K'],'-1')
        mu = [1,-1,-1]
        source = PRODUCER.compile_sawtooth(mu,WORK,1)
        c = sum(Q(a,d) for d,a in enumerate(mu,1))
        self.assertEqual(Q(source['mean']),1+(sum(mu)-c)/2)
        # Periodic n=0 equals 1-C; the physical zero-extended prefix equals 0.
        self.assertNotEqual(1-Q(source['mean']),0)
        bad = copy.deepcopy(source);bad['mean']='0'
        with self.assertRaises(ValueError):CHECK.verify_compiler(mu,1,bad,WORK)

    def test_compiler_rejects_missing_conductor_wrong_jordan_and_cross_squares(self):
        weights=[1,1,1,1,1,1];result=PRODUCER.compile_sawtooth(weights,WORK)
        for mutation in ('missing','jordan','variance'):
            bad=copy.deepcopy(result)
            if mutation=='missing':bad['conductors'].pop()
            elif mutation=='jordan':bad['conductors'][0]['J2']+=1
            else:bad['variance']=str(Q(bad['variance'])+Q(1,12))
            with self.assertRaises(ValueError):CHECK.verify_compiler(weights,0,bad,WORK)

    def test_generic_cutoff_variance_has_no_mobius_exponent_gain(self):
        for profile in ('bounded','mobius'):
            result=plan(profile=profile)
            CHECK.verify_plan(result,WORK)
            selected=CHECK.selections(result,WORK)
            equal=PRODUCER.rank(result)
            self.assertEqual(selected,equal)
            self.assertEqual((selected[0]['exponent'],selected[0]['log_degree']),('1',0))
            n=result['nodes'][selected[0]['selected']]
            self.assertEqual(n['rule'],'parseval_keep_cutoff')
            self.assertEqual(n['assumptions'],[])
            self.assertEqual(n['bound'][0]['constant'],'1/2')
            if profile=='mobius':
                inverse=next(n for n in result['nodes'] if n['rule']=='parseval_inverse')
                self.assertEqual(inverse['bound'][0]['constant'],'9')
                self.assertEqual(len(inverse['assumptions']),2)

    def test_cutoff_double_sum_identity_is_valid_for_each_finite_prefix(self):
        for u in range(1,25):
            harmonic=[Q(0)]
            for n in range(1,u+1):harmonic.append(harmonic[-1]+Q(1,n))
            left=sum(harmonic[u//r]**2 for r in range(1,u+1))
            right=sum(Q(u//max(k,l),k*l) for k in range(1,u+1) for l in range(1,u+1))
            self.assertEqual(left,right)
            self.assertLessEqual(left/12,Q(u,2))
            WORK.charge(20*u*u)

    def test_fractional_abel_resonance_and_direct_critical_log(self):
        expected=[('1/6','2/3',0),('1/3','1/3',0),('1/2','0',1),('2/3','0',0),('3/2','0',0)]
        for theta,power,log in expected:
            result=plan(theta=theta)
            CHECK.verify_plan(result,WORK)
            choice=CHECK.selections(result,WORK)[0]
            self.assertEqual((choice['exponent'],choice['log_degree']),(power,log))
            self.assertEqual(CHECK.selections(result,WORK),PRODUCER.rank(result))
        critical=plan(theta='1/2')
        abel=next(n for n in critical['nodes'] if n['rule']=='weighted_Abel' and
                  critical['nodes'][n['premises'][0]]['rule']=='parseval_keep_cutoff')
        self.assertEqual(abel['bound'],[CHECK.env(Q(1,2),logs=2)])
        bad=copy.deepcopy(critical);bad['nodes'][abel['id']]['bound'][0]['log_degree']=0
        self.rejected_plan(bad)

    def test_rule_ablation_is_replayed_as_a_distinct_search(self):
        for enabled,power,logs in [(['bounded_sawtooth','mean_from_supremum'],'2',0),
             ([r for r in CHECK.RULES if r!='parseval_keep_cutoff'],'1',2)]:
            result=plan(enabled=enabled)
            CHECK.verify_plan(result,WORK)
            choice=CHECK.selections(result,WORK)[0]
            self.assertEqual((choice['exponent'],choice['log_degree']),(power,logs))
        bad=copy.deepcopy(result);bad['enabled_rules']=list(CHECK.RULES)
        self.rejected_plan(bad)

    def test_window_choice_and_full_convolution_denominator_cost(self):
        result=plan('interval',support_power='2',l1_power='2')
        CHECK.verify_plan(result,WORK)
        choice=CHECK.selections(result,WORK)
        self.assertEqual(choice,PRODUCER.rank(result))
        row=next(n for n in result['nodes'] if n['rule']=='finite_dilation_spacing' and
                 result['nodes'][n['premises'][0]]['rule']=='parseval_keep_cutoff')
        self.assertEqual(row['bound'],[CHECK.env(Q(1,2),5,1),CHECK.env(3,11,logs=1)])
        self.assertIn('n>=D',row['details']['domain'])
        self.assertIn('Qplus(0)=0',row['details']['short_head'])
        base=plan('interval');ranking=CHECK.selections(base,WORK)
        self.assertEqual(base['nodes'][ranking[1]['selected']]['rule'],'interval_from_supremum')
        self.assertEqual(base['nodes'][ranking[4]['selected']]['rule'],'finite_dilation_spacing')

    def test_rejects_missing_spacing_head_or_offdiagonal_loss(self):
        result=plan('interval',support_power='1/3',l1_power='1/2')
        row=next(n for n in result['nodes'] if n['rule']=='finite_dilation_spacing')
        for mutation in ('power','logs','domain','head','crosses'):
            bad=copy.deepcopy(result);n=bad['nodes'][row['id']]
            if mutation=='power':n['bound'][-1]['U_power']='0'
            elif mutation=='logs':n['bound'][-1]['log_degree']=0
            elif mutation=='domain':n['details']['domain']='all n>=0'
            elif mutation=='head':n['details'].pop('short_head')
            else:n['details']['all_offdiagonal_terms_paid']=False
            self.rejected_plan(bad)

    def test_dag_cycle_forward_reference_and_dropped_attempt_rejected(self):
        result=plan(profile='mobius')
        dependent=next(n for n in result['nodes'] if n['premises'])
        for mutation in ('cycle','forward','missing','solutions','open'):
            bad=copy.deepcopy(result)
            if mutation=='cycle':bad['nodes'][dependent['id']]['premises'][0]=dependent['id']
            elif mutation=='forward':bad['nodes'][dependent['id']]['premises'][0]=len(result['nodes'])
            elif mutation=='missing':bad['attempts'].pop()
            elif mutation=='solutions':bad['solutions'].pop()
            else:bad['frontier'].append(dict(goal=result['target'],reason='arbitrary'))
            self.rejected_plan(bad)

    def test_inverse_profile_provider_and_assumption_changes_rejected(self):
        result=plan(profile='mobius')
        row=next(n for n in result['nodes'] if n['rule']=='coprime_dilation_inverse')
        for field,value in [('provider','absolute'),('non_squarefree_conductor_zero',False)]:
            bad=copy.deepcopy(result);bad['nodes'][row['id']]['details'][field]=value
            self.rejected_plan(bad)
        bad=copy.deepcopy(result);bad['nodes'][row['id']]['assumptions']=[]
        self.rejected_plan(bad)
        bad=copy.deepcopy(result);bad['target']['profile']='bounded'
        self.rejected_plan(bad)

    def test_depth_and_unknown_language_leaves_fail_closed(self):
        for depth in (1,2,3):
            result=plan('interval',profile='mobius',depth_limit=depth)
            CHECK.verify_plan(result,WORK)
            if depth==1:self.assertFalse(result['target_proved'])
        unknown=PRODUCER.plan(dict(kind='unlicensed_pointwise_E_cubed'),WORK)
        CHECK.verify_plan(unknown,WORK)
        self.assertEqual(unknown['solutions'],[])
        self.assertFalse(unknown['target_proved'])
        bad=copy.deepcopy(unknown);bad['target_proved']=True
        self.rejected_plan(bad)

    def test_local_rational_guard_and_unvalidated_goal_rejected(self):
        self.assertFalse(hasattr(WORK,'number'))
        self.assertEqual(CHECK.rational(Q(1,3),WORK),Q(1,3))
        for value in (1<<4096,Q(1,1<<4096),True,'0/0'):
            with self.assertRaises(ValueError):CHECK.rational(value,WORK)
        result=plan('interval')
        for field,value in [('theta','-1/4'),('support_power','-1'),('l1_power','-1'),
                            ('theta','2/4'),('profile','unlicensed')]:
            bad=copy.deepcopy(result);bad['target'][field]=value
            self.rejected_plan(bad)
        bad=copy.deepcopy(result);bad['target']['extra_scope']=True
        self.rejected_plan(bad)
        bad=copy.deepcopy(result);bad['nodes'][0]['id']=False
        self.rejected_plan(bad)

    def test_representation_proofs_are_not_numeric_bounds(self):
        for kind in ('spectrum','cofactor','reciprocal'):
            result=plan(kind,profile='mobius')
            CHECK.verify_plan(result,WORK)
            self.assertTrue(result['target_proved'])
            self.assertTrue(all(n['bound'] is None for n in result['nodes']))
        spectrum=plan('spectrum')
        bad=copy.deepcopy(spectrum);bad['nodes'][0]['bound']=[CHECK.env(1)]
        self.rejected_plan(bad)

    def test_component_generates_auxiliary_but_cannot_close_bridge(self):
        goal=dict(kind='component_mellin',p=1,m=4,sigma='2/5',theta='3/4',
                  required=dict(U_power='7/3',log_degree=0))
        result=PRODUCER.plan(goal,WORK)
        CHECK.verify_plan(result,WORK)
        self.assertFalse(result['target_proved'])
        self.assertTrue(any(f['goal']['kind']=='signed_convolution_mellin_bridge' for f in result['frontier']))
        source=next(a for a in result['attempts'] if a['rule']=='source_prefix_auxiliary')
        self.assertEqual(source['premises'][0]['support_power'],'1')
        self.assertEqual(source['premise_solutions'][1],[])
        bad=copy.deepcopy(result);bad['solutions']=[source['premise_solutions'][0][0]];bad['target_proved']=True
        self.rejected_plan(bad)
        for field,value in [('sigma','0'),('theta','1'),('p',-1),('m',0)]:
            bad=copy.deepcopy(result);bad['target'][field]=value
            self.rejected_plan(bad)

    def test_search_recovery_keeps_all_mean_branches_and_ordered_crosses(self):
        parent,binding,result=fixture()
        with patch.object(CHECK,'source_binding',return_value=binding):
            CHECK.verify_search(parent,result,WORK)
            self.assertEqual(len(result['recovery']['branches']),4)
            self.assertEqual(len(result['recovery']['all_ordered_cross_terms']),16)
            self.assertFalse(result['statistics']['auxiliary_exponent_advantage_over_unsigned'])
            for mutation in ('mean','branch','cross','head','pointwise','closed','rank','ablation'):
                bad=copy.deepcopy(result)
                if mutation=='mean':bad['recovery']['mean_bound_assumed']=True
                elif mutation=='branch':bad['recovery']['branches'].pop(0)
                elif mutation=='cross':bad['recovery']['all_ordered_cross_terms'].pop()
                elif mutation=='head':bad['recovery']['deterministic_head']='discarded'
                elif mutation=='pointwise':bad['recovery']['pointwise_power_substitution_allowed']=True
                elif mutation=='closed':bad['statistics']['full_component_bound_proved']=True
                elif mutation=='rank':bad['auxiliary_selection'][0]['exponent']='0'
                else:bad['trials'].pop()
                with self.assertRaises(ValueError):CHECK.verify_search(parent,bad,WORK)

    def test_source_boundary_replays_binding_and_actual_degree_guard(self):
        import check_core_signed_primitive_search as PRIOR
        parent,binding,result=fixture()
        with patch.object(PRIOR,'source_binding',return_value=binding) as replay:
            self.assertEqual(CHECK.source_binding(parent,WORK),binding)
            self.assertEqual(replay.call_args.args[0]['schema'],'core-work-moment-proof-feedback-v1')
            for mutation in ('binding','degree','schema'):
                bad=copy.deepcopy(parent)
                if mutation=='binding':bad['signed_primitive_search']['binding']['unit']=0
                elif mutation=='degree':bad['cutoff_work_targets'][0]['m']=4
                else:bad['schema']='wrong'
                with self.assertRaises(ValueError):CHECK.source_binding(bad,WORK)

    def test_feedback_preserves_full_source_failed_routes_and_old_tasks(self):
        parent,binding,result=fixture();artifact='synthetic/proof_search.json'
        out=PRODUCER.feedback(parent,result,artifact)
        with patch.object(CHECK,'source_binding',return_value=binding):
            CHECK.verify_feedback(parent,result,out,artifact,WORK)
            for mutation in ('source','task','priority','proof','core','artifact'):
                bad=copy.deepcopy(out)
                if mutation=='source':bad['source_fixture']['original_channel_ids'].pop()
                elif mutation=='task':bad['next_search_tasks'].pop()
                elif mutation=='priority':bad['next_search_tasks'][0]['priority']=1
                elif mutation=='proof':bad['next_search_tasks'][1]['status']='proved'
                elif mutation=='core':bad['whole_signed_bound_proved']=True
                else:bad['complete_search_artifact']='other.json'
                with self.assertRaises(ValueError):CHECK.verify_feedback(parent,result,bad,artifact,WORK)


if __name__=='__main__':
    unittest.main()
