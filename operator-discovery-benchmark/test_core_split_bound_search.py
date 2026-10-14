from copy import deepcopy
from fractions import Fraction as Q
import unittest

import bound_split_search as S
import core_split_bound_search as P
from prime_bank_candidates import Meter


class SplitBoundTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.meter = Meter(20000000, 180)

    @classmethod
    def tearDownClass(cls):
        print('producer operations='+str(cls.meter.operations))

    def test_generic_envelopes_including_flat_minimum_and_boundaries(self):
        def solve(lines):
            return S.solve(dict(lower='0', upper='1', terms=[dict(intercept=a, slope=b) for a,b in lines]), self.meter)
        value = solve([('1/4','1/2'), ('3/4','-2')])
        self.assertEqual((value['parameter'], value['power']), ('1/5','7/20'))
        plateau = solve([('1/4','1/2'), ('3/4','-2'), ('2/5','0')])
        self.assertEqual((plateau['parameter'], plateau['power']), ('7/40','2/5'))
        self.assertEqual(solve([('0','-2'), ('-1','-2')])['parameter'], '1')
        self.assertEqual(solve([('2','3'), ('2','3')])['parameter'], '0')

    def test_fractional_split_parameters_are_solved(self):
        for theta in ('1/6','1/3','1/2','2/3','5/6','7/11'):
            result = S.solve(S.power_kernel_problem(theta), self.meter)
            t = Q(result['parameter'])
            self.assertEqual(t, Q(theta)*(1-t))
            self.assertLessEqual(Q(result['power']), Q(theta))
            weights = list(map(Q, result['dual_weights']))
            self.assertEqual(sum(weights), 1)
            self.assertEqual(weights[0]-Q(theta)*weights[1], 0)

    def test_weight_threshold_keeps_the_harmonic_log(self):
        self.assertEqual(P.weighted_mass('1'), dict(constant='1', cutoff_power='0', log_degree=1))
        self.assertEqual(P.weighted_mass('5/6'), dict(constant='6', cutoff_power='1/6', log_degree=0))
        self.assertEqual(P.weighted_mass('7/6'), dict(constant='7', cutoff_power='0', log_degree=0))

    def test_target_gate_includes_cutoff_and_log_costs(self):
        mode = dict(name='B', coefficient='beta', p=2, q=0, positive_shift='1/3')
        term = dict(a=1,b=0,coefficient='2')
        split = S.solve(S.power_kernel_problem('2/3'), self.meter)
        at_boundary = P.application(mode,term,'1/18','1/2',split,P.DEFAULT_SPEC['target'],0,self.meter)
        route = at_boundary['routes'][at_boundary['selected_route']]
        self.assertEqual(route['energy']['power'], '0')
        self.assertEqual(route['energy']['log_degree'], 2)
        self.assertFalse(at_boundary['component_target_proved'])
        self.assertEqual(route['cutoff_condition']['alpha_upper'], '1/18')
        self.assertTrue(route['cutoff_condition']['strict'])
        improved = P.application(mode,term,'1/24','1/2',split,P.DEFAULT_SPEC['target'],0,self.meter)
        self.assertTrue(improved['component_target_proved'])
        self.assertEqual(improved['routes'][improved['selected_route']]['energy']['power'],'-1/20')
        self.assertEqual(improved['pieces'][1]['coefficient'],'3')
        self.assertEqual(improved['pieces'][2]['coefficient'],'-2')
        log_target = dict(energy_power='0',log_degree=2)
        boundary_paid = P.application(mode,term,'1/18','1/2',split,log_target,0,self.meter)
        self.assertTrue(boundary_paid['component_target_proved'])

    def test_competing_routes_retain_fractional_threshold_cases(self):
        for theta in ('1/3','1/2','2/3'):
            mode = dict(name='generic',coefficient='-beta',p=1,q=1,positive_shift=str(1-Q(theta)))
            split = S.solve(S.power_kernel_problem(theta), self.meter)
            routes = P.proof_routes(mode,dict(coefficient='1'),'1/24','1/6',split,P.DEFAULT_SPEC['target'],self.meter)
            sharp = routes[1]
            self.assertTrue(sharp['premises']['commutator_all_d_including_d_gt_n'])
            if theta == '1/3':
                self.assertGreater(Q(sharp['V_power']),0)
            elif theta == '1/2':
                self.assertEqual(sharp['log_degree'],2)
            else:
                self.assertEqual((sharp['V_power'],sharp['log_degree']),('0',1))

    def test_centering_commutator_has_a_nonzero_complete_tail(self):
        # Independent generic finite signed sequences, NOT observed core data.
        # h0 at2 exceeds prefixn1, so truncating its moment gives a false zero.
        theta = 2/3
        h0 = {2:1,7:-3}
        moment = sum(c*d**(-theta) for d,c in h0.items())
        self.assertNotEqual(moment,0)
        for n in (1,2,3,7,13):
            commutator = sum(c*(n//d)**theta for d,c in h0.items())-n**theta*moment
            r = theta/(1+theta)
            upper = n**r*sum(abs(c)*d**(-r) for d,c in h0.items())
            self.assertLessEqual(abs(commutator),upper+1e-12)
        self.assertAlmostEqual(sum(c*(1//d)**theta for d,c in h0.items())-moment,-moment)

    def test_full_inverse_degree_and_source_partition_are_preserved(self):
        modes = [dict(name='B',coefficient='beta',p=2,q=0,positive_shift='1/3'),
                 dict(name='U',coefficient='-beta',p=1,q=1,positive_shift='1/3'),
                 dict(name='V',coefficient='-beta',p=1,q=0,positive_shift=None),
                 dict(name='power',coefficient='-R_u',p=0,q=1,positive_shift='1/3')]
        split = S.solve(S.power_kernel_problem('2/3'), self.meter)
        row = P.geometry(modes,'1/24','1/2',P.DEFAULT_SPEC,{'2/3':split},0,self.meter)
        self.assertGreater(max(t['a'] for c in row['cases'] for t in c['program']['terms']),20)
        keys = {(c['mode']['name'],t['a'],t['b']) for c in row['cases'] for t in c['program']['terms']}
        join = row['exact_join']
        kept = join['untouched_source_terms']+join['replaced_source_terms']
        self.assertEqual({(k['mode'],k['a'],k['b']) for k in kept},keys)
        self.assertEqual(len(kept),len(keys))
        self.assertEqual(join['all_moment_drifts'],[0,1])
        self.assertEqual(join['all_centering_compensations'],[0,1])
        self.assertEqual(join['transport_error_coefficient'],'-1')
        self.assertFalse(row['full_signed_bound_proved'])
        too_small = deepcopy(P.DEFAULT_SPEC)
        too_small['maximum_inverse_factors']=8
        with self.assertRaises(ValueError):
            P.geometry(modes,'1/24','1/2',too_small,{'2/3':split},0,self.meter)

    def test_original_recovery_spends_its_log_budget_before_residual_target(self):
        parent = dict(id='generic_parent', reduction=dict(target_log_power='3',
            required_coarse_forcing_log_power='0',rho='1'),
            construction=dict(channels=[dict(eta='0',polynomial=['1','-1'])],
                              recovery_log_power='2',recovery_constant='8'),
            conditional_conclusion=dict(original_recovery='original inequality with log^2 recovery'),
            transport_program=dict(theta='1/2'))
        row = dict(id=0, applications=[])
        value = P.reductions(row,[parent],P.DEFAULT_SPEC['target'],self.meter)[0]
        self.assertEqual(value['sufficient_goal']['p'],'1')
        self.assertEqual(value['original_target_log_degree'],'3')
        self.assertEqual(value['channel_abel_constant'],'9')
        parent['construction']['recovery_log_power']='4'
        with self.assertRaises(ValueError):
            P.reductions(row,[parent],P.DEFAULT_SPEC['target'],self.meter)
