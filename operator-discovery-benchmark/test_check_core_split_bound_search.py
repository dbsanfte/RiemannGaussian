"""Independent algebra, global lower bounds, and complete signed mutations."""
from copy import deepcopy
from fractions import Fraction as Q
import resource
import time
import unittest

import bound_split_search as GENERIC
import core_split_bound_search as PRODUCER
import check_core_split_bound_search as CHECK
from potential_candidate_language import Meter

START=time.monotonic()
WORK=Meter(50000000,deadline=START+180,max_cells=2000000)
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))


def split(lines,lower='0',upper='1'):
    return GENERIC.solve(dict(lower=lower,upper=upper,
        terms=[dict(intercept=a,slope=b) for a,b in lines]),WORK)


MODES=[dict(name='B',coefficient='beta',p=2,q=0,positive_shift='1/3'),
       dict(name='U',coefficient='-beta',p=1,q=1,positive_shift='1/3'),
       dict(name='V',coefficient='-beta',p=1,q=0,positive_shift=None),
       dict(name='power',coefficient='-R_u',p=0,q=1,positive_shift='1/3')]


def parent_fixture():
    # 144 symbolic routes: no source observations or archived source reads.
    parents=[]
    for i in range(144):
        parents.append(dict(id='route_'+str(i),reduction=dict(target_log_power='3',
            required_coarse_forcing_log_power='0',rho='1'),
            construction=dict(channels=[dict(eta='1/2',polynomial=['1','-2','0','3']),
                dict(eta='0',polynomial=['-2'])],recovery_log_power='2',recovery_constant='8'),
            conditional_conclusion=dict(original_recovery='full original recovery for route '+str(i)),
            transport_program=dict(id=i,mesh_power=str(Q(1,2+(i%3))))))
    programs=dict(schema='detector-bound-program-search-input-v1',generated_bound_program_obligations=parents)
    source=dict(schema='source-specific-short-inverse-search-input-v1',
        source_geometries=[dict(cases=[dict(mode=deepcopy(m)) for m in MODES])],parent_obligation=programs)
    return dict(schema='synthetic-current-open-input',parent_obligation=source,
        whole_signed_bound_proved=False,RH_proved=False)


class IndependentSplitBoundTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.parent=parent_fixture()
        cls.spec=deepcopy(PRODUCER.DEFAULT_SPEC)
        cls.spec.update(root_denominator_min=18,root_denominator_max=19)
        cls.result=PRODUCER.search(cls.parent,cls.spec,WORK)

    def reject(self,mutate):
        corrupted=deepcopy(self.result);mutate(corrupted)
        with self.assertRaises((ValueError,KeyError,TypeError)):
            CHECK.verify_search(self.parent,corrupted,WORK)

    def test_global_minimax_generic_interior_with_hand_value(self):
        cert=split([('1/7','3/2'),('5/6','-7/3'),('-2','5/4')])
        point=Q(29,161);value=Q(133,322)
        self.assertEqual((Q(cert['parameter']),Q(cert['power'])),(point,value))
        audit=CHECK.verify_split(cert,WORK)
        self.assertEqual(audit['independent_global_lower_bound']['kind'],'convex_dual_support')
        for j in range(201):
            t=Q(j,200)
            self.assertGreaterEqual(max(Q(row['intercept'])+Q(row['slope'])*t for row in cert['problem']['terms']),value)
            WORK.charge(30)

    def test_global_minimax_plateau_boundary_duplicates_and_general_interval(self):
        plateau=split([('0','1'),('1','-1'),('3/4','0')])
        self.assertEqual((plateau['parameter'],plateau['power']),('1/4','3/4'))
        CHECK.verify_split(plateau,WORK)
        cases=[([('2','3'),('2','3')],'0','1','0'),
               ([('1','-2'),('-1','-3')],'0','1','1'),
               ([('0','1'),('0','-1')],'-2','3','0')]
        for lines,lo,hi,answer in cases:
            cert=split(lines,lo,hi);self.assertEqual(cert['parameter'],answer);CHECK.verify_split(cert,WORK)

    def test_optimizer_rejects_missing_vertex_false_optimum_and_dual(self):
        original=split([('0','1'),('1','-2'),('-2','5')])
        variants=[]
        v=deepcopy(original);v['vertices'].pop();variants.append(v)
        v=deepcopy(original);v['parameter']='0';variants.append(v)
        v=deepcopy(original);v['dual_weights']=['1','0','0'];v['dual_slope']='1';variants.append(v)
        v=deepcopy(original);v['dual_weights'][0]='-1';variants.append(v)
        for v in variants:
            with self.assertRaises(ValueError):CHECK.verify_split(v,WORK)

    def test_fractional_split_balances_both_errors_and_small_n_guard(self):
        for theta in (Q(1,11),Q(1,2),Q(2,3),Q(17,19)):
            cert=GENERIC.solve(GENERIC.power_kernel_problem(str(theta)),WORK)
            audit=CHECK.verify_split(cert,WORK);r=Q(audit['power'])
            self.assertEqual(r,theta/(1+theta));self.assertLess(r,theta)
            weights=list(map(Q,cert['dual_weights']))
            self.assertEqual(weights,[theta/(1+theta),1/(1+theta)])
            # The exact small-n comparison exponent is theta-r>0.
            self.assertGreaterEqual(1-r,1-theta)
        wrong=split([('0','1'),('1/3','0')])
        with self.assertRaises(ValueError):
            CHECK._routes(MODES[0],Q(2),Q(1,24),Q(1,2),wrong,self.spec['target'],WORK)

    def test_full_inverse_beyond_old_degree_cap_and_exact_support_frontier(self):
        # Closed binomial product, hand-built independently of inverse generator.
        terms=[]
        for total in range(24):
            for a in range(total+1):
                b=total-a
                if Q(a,24)+Q(b,2)<1:terms.append(dict(a=a,b=b,coefficient=str(a+1)))
        program=dict(alpha='1/24',gamma='1/2',p=2,q=1,terms=terms)
        keys=CHECK.verify_inverse(program,Q(1,24),Q(1,2),2,1,WORK)
        self.assertIn((23,0),keys);self.assertNotIn((24,0),keys)
        for mutation in ('unit','high_degree','mixed_coefficient','boundary'):
            v=deepcopy(program)
            if mutation=='unit':v['terms'].pop(0)
            if mutation=='high_degree':v['terms'].pop()
            if mutation=='mixed_coefficient':next(t for t in v['terms'] if (t['a'],t['b'])==(1,1))['coefficient']='1'
            if mutation=='boundary':v['terms'].append(dict(a=24,b=0,coefficient='25'))
            with self.assertRaises(ValueError):CHECK.verify_inverse(v,Q(1,24),Q(1,2),2,1,WORK)

    def test_complete_grid_selection_and_all_144_route_bindings(self):
        audit=CHECK.verify_search(self.parent,self.result,WORK)
        self.assertEqual((audit['geometries'],audit['component_controls'],audit['inherited_route_bindings']),(4,2,144))
        self.assertEqual(self.result['selected_geometry'],2)
        chosen=self.result['geometries'][2]
        self.assertEqual((chosen['alpha'],chosen['gamma']),('1/19','1/18'))
        # Hand cost: (2*(1+2*(2+0+3)))^2+(-2)^2=488.
        for binding in self.result['selected_bindings']:
            self.assertEqual(binding['channel_abel_constant'],'488')
            self.assertEqual(binding['sufficient_goal']['p'],'1')
            self.assertEqual(binding['inherited_recovery_log_power'],'2')
        first=chosen['applications'][0]
        self.assertEqual(first['routes'][1]['prefix_constant'],'525')
        self.assertEqual(first['routes'][1]['energy'],dict(constant='89302500',power='-1/95',log_degree=2))
        self.assertFalse(audit['complete_signed_join_proved'])

    def test_all_signed_replacement_coefficients_and_complete_moment(self):
        chosen=self.result['geometries'][2]
        for app in chosen['applications']:
            theta=Q(app['theta']);coefficient=Q(app['source_coefficient'])
            self.assertEqual([Q(p['coefficient']) for p in app['pieces']],
                [coefficient,coefficient/theta,-coefficient])
            # Formal K*h and J basis coefficients, canceling only the retained drift.
            m=Q(-13,7);c=Q(5,17)
            main=coefficient*Q(11,3)-coefficient*m/theta
            main+=Q(app['pieces'][1]['coefficient'])*m
            main+=Q(app['pieces'][2]['coefficient'])*c*Q(19,5)
            self.assertEqual(main,coefficient*(Q(11,3)-c*Q(19,5)))
            self.assertFalse(app['moment']['truncated_at_horizon'])
        self.reject(lambda r:r['geometries'][2]['applications'][0]['pieces'].pop(1))
        self.reject(lambda r:r['geometries'][2]['applications'][1]['pieces'][2].update(coefficient='1'))
        self.reject(lambda r:r['geometries'][2]['applications'][0]['moment'].update(truncated_at_horizon=True))

    def test_route_thresholds_include_harmonic_boundary_and_full_commutator(self):
        for theta,expected in [(Q(1,3),('1/12',1)),(Q(1,2),('0',2)),(Q(2,3),('0',1))]:
            mode=dict(name='calibration',coefficient='-beta',p=1,q=1,positive_shift=str(1-theta))
            cert=GENERIC.solve(GENERIC.power_kernel_problem(str(theta)),WORK)
            routes=CHECK._routes(mode,Q(1),Q(1,24),Q(1,6),cert,self.spec['target'],WORK)
            self.assertEqual((routes[1]['V_power'],routes[1]['log_degree']),expected)
            self.assertTrue(routes[1]['premises']['commutator_all_d_including_d_gt_n'])
            self.assertEqual(routes,PRODUCER.proof_routes(mode,dict(coefficient='1'),'1/24','1/6',cert,self.spec['target'],WORK))
        self.reject(lambda r:r['geometries'][2]['applications'][0]['routes'][1]['premises'].update(commutator_all_d_including_d_gt_n=False))
        self.reject(lambda r:r['geometries'][2]['applications'][0]['routes'][1]['premises'].update(E_moment_constant='0'))
        self.reject(lambda r:r['geometries'][2]['applications'][0]['routes'].pop())

    def test_complete_commutator_has_nonzero_beyond_prefix_tail(self):
        # theta=1/2, d=4,9 are perfect squares: exact full finite moment.
        h={4:Q(2),9:Q(-3)};moment=Q(2,2)-Q(3,3)
        self.assertEqual(moment,0)
        h[16]=Q(1);moment+=Q(1,4)
        raw_prefix=sum((c for d,c in h.items() if d<=1),Q(0))
        self.assertEqual(raw_prefix-moment,-Q(1,4))
        # For n=1 every finite factor exceeds n; truncation would report zero.
        self.assertNotEqual(-moment,0)
        WORK.charge(200)

    def test_cutoff_boundary_unpaid_logs_and_explicit_uniform_payment(self):
        boundary=self.result['geometries'][0]['applications'][0]
        route=boundary['routes'][boundary['selected_route']]
        self.assertEqual(route['energy']['power'],'0');self.assertEqual(route['energy']['log_degree'],2)
        self.assertEqual(route['cutoff_condition']['alpha_upper'],'1/18');self.assertTrue(route['cutoff_condition']['strict'])
        self.assertIsNone(route['target_constant']);self.assertFalse(boundary['component_target_proved'])
        energy=dict(constant='3',power='-1/2',log_degree=2)
        self.assertEqual(CHECK.uniform_payment(energy,dict(energy_power='0',log_degree=0),WORK),'204')
        energy['power']='0'
        self.assertIsNone(CHECK.uniform_payment(energy,dict(energy_power='0',log_degree=0),WORK))
        self.assertEqual(CHECK.uniform_payment(energy,dict(energy_power='0',log_degree=2),WORK),'3')
        self.reject(lambda r:r['geometries'][0]['applications'][0].update(component_target_proved=True))
        self.reject(lambda r:r['geometries'][2]['applications'][0]['routes'][1].update(target_constant='1'))

    def test_source_join_missing_unit_row_drift_compensation_or_error_rejected(self):
        self.reject(lambda r:r['geometries'][0]['cases'].pop())
        self.reject(lambda r:r['geometries'][0]['cases'][0]['program']['terms'].pop(0))
        self.reject(lambda r:r['geometries'][2]['exact_join']['untouched_source_terms'].pop())
        self.reject(lambda r:r['geometries'][2]['exact_join']['all_moment_drifts'].clear())
        self.reject(lambda r:r['geometries'][2]['exact_join']['all_centering_compensations'].clear())
        self.reject(lambda r:r['geometries'][2]['exact_join'].update(transport_error_coefficient='0'))

    def test_candidate_coverage_selection_statistics_and_false_closure_rejected(self):
        self.reject(lambda r:r['geometries'].pop())
        self.reject(lambda r:r.update(selected_geometry=0))
        self.reject(lambda r:r['statistics'].update(source_terms=1))
        self.reject(lambda r:r.update(whole_signed_bound_proved=True))
        self.reject(lambda r:r['geometries'][2].update(full_signed_bound_proved=True))
        self.reject(lambda r:r.update(source_observations=1))
        self.reject(lambda r:r['geometries'][2]['applications'][0].update(compensating_terms_bounded=0))

    def test_binding_omission_transport_and_abel_variation_rejected(self):
        self.reject(lambda r:r['selected_bindings'].pop())
        self.reject(lambda r:r['selected_bindings'][0].update(channel_abel_constant='144'))
        self.reject(lambda r:r['selected_bindings'][0].update(combined_paid_energy_constant='1'))
        self.reject(lambda r:r['selected_bindings'][0]['transport_program'].update(mesh_power='1'))
        self.reject(lambda r:r['selected_bindings'][0]['sufficient_goal'].update(p='3'))
        parent=deepcopy(self.parent)
        obligation=parent['parent_obligation']['parent_obligation']['generated_bound_program_obligations'][0]
        obligation['construction']['recovery_log_power']='4'
        with self.assertRaises(ValueError):CHECK.verify_search(parent,self.result,WORK)

    def test_ancestry_missing_mode_and_negative_recovery_cost_rejected(self):
        for kind in ('missing','scalar','negative_eta','negative_recovery'):
            parent=deepcopy(self.parent);source=parent['parent_obligation']
            if kind=='missing':source['source_geometries'][0]['cases'].pop()
            if kind=='scalar':source['source_geometries'][0]['cases'][0]['mode']['coefficient']='-beta'
            obligation=source['parent_obligation']['generated_bound_program_obligations'][0]
            if kind=='negative_eta':obligation['construction']['channels'][0]['eta']='-1'
            if kind=='negative_recovery':obligation['construction']['recovery_constant']='-1'
            with self.assertRaises(ValueError):CHECK.verify_search(parent,self.result,WORK)

    def test_generic_log_target_uses_no_unlicensed_whole_source_bridge(self):
        spec=deepcopy(self.spec);spec.update(root_denominator_max=18);spec['target']['log_degree']=2
        result=PRODUCER.search(self.parent,spec,WORK)
        audit=CHECK.verify_search(self.parent,result,WORK)
        self.assertEqual(audit['inherited_route_bindings'],0);self.assertEqual(audit['component_controls'],2)
        self.assertTrue(result['geometries'][0]['applications'][0]['component_target_proved'])

    def test_feedback_retains_previous_frontier_and_complete_signed_goal(self):
        feedback=PRODUCER.feedback(self.result,'parent.json','complete.json')
        self.assertTrue(CHECK.verify_feedback(self.result,feedback,'parent.json','complete.json',WORK)['verified'])
        variants=[]
        v=deepcopy(feedback);v['proof_frontier'].pop();variants.append(v)
        v=deepcopy(feedback);v['selected_source_representation']['exact_join']['all_moment_drifts'].clear();variants.append(v)
        v=deepcopy(feedback);v['parent_obligation_file']='other.json';variants.append(v)
        v=deepcopy(feedback);v['RH_proved']=True;variants.append(v)
        for v in variants:
            with self.assertRaises(ValueError):CHECK.verify_feedback(self.result,v,'parent.json','complete.json',WORK)


def tearDownModule():
    print('SYNTHETIC_WORK module=test_check_core_split_bound_search operations='+str(WORK.operations)+
        ' elapsed_seconds='+format(time.monotonic()-START,'.6f'))
