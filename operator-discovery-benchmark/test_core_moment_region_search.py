"""Meaningful boundary, counterexample, transfer and source-preservation checks."""
import copy
from fractions import Fraction as Q
import unittest

import core_moment_region_search as P
from prime_bank_candidates import Meter

METER = Meter(100000000, 600)
ALL = P.DEFAULT_SPEC['library_ids']


def fixture():
    targets = [dict(target_id='centered_A2_E'+str(m), p=2, m=m, theta='2/3',
        source_term=dict(coefficient=str(3*m), powers=[2, 0, 1, m, 0, 0, 0, 0]),
        component_bound_proved=(m == 2)) for m in (2, 3, 4)]
    transfer = dict(alpha='1/4', beta='3/4', base='T', subcritical_padding=True,
        normalized_error_energy=[dict(constant='5509980288', N_power='-7/36', log_degree=4),
                                 dict(constant='23702740992', N_power='-3/4', log_degree=0)])
    program = dict(id='original_channel', transport_program=dict(theta='7/12'),
        construction=dict(channels=[dict(eta='0', polynomial=['1', '2'])]))
    goal = dict(expression='old whole residual', upper='C*(1+log2X)^3', p='3',
                quantifier='every dyadic X>=1; one fixed C', status='open')
    parent = dict(schema='core-complete-convolution-feedback-v1',
        selected_source_representation=dict(alpha='1/24'), auxiliary_bound_targets=targets,
        complete_source_reduction=dict(inherited_complete_signed_join=dict(
            collected_terms=[t['source_term'] for t in targets], transport_error='-e')),
        generated_bound_obligations=[dict(parent_obligation_id='original_channel',
            transport_program=program['transport_program'], sufficient_goal=goal,
            recovery='S_g<=4*S_Z+4*C_new+2*C_old; S_Z<=4*S_g+4*C_old+2*C_new')],
        cutoff_work_targets=[dict(target_id='centered_A2_E3', p=2, m=3, theta='2/3',
            source_term=targets[1]['source_term'], head_bound=dict(atom='One', convolution_power=1,
            c_power=3, centered_prefix_U_power='1', centered_prefix_constant='12'))],
        complete_convolution_search=dict(centered_transfer=dict(selected=0, trials=[transfer])),
        next_search_tasks=[dict(priority=0, target_id='actual_signed_core',
            search_kind='joint_signed_core_control', status='open')],
        whole_signed_bound_proved=False, RH_proved=False)
    context = dict(complete_signed_join=copy.deepcopy(parent['complete_source_reduction']['inherited_complete_signed_join']),
                   channel_programs=[program])
    return parent, context


class MomentRegionTests(unittest.TestCase):
    def test_strict_provider_boundaries_prevent_endpoint_promotion(self):
        for row in P.LIBRARY:
            line = Q(row['lower'])
            self.assertEqual(P.available(row, line), not row['strict'])
            self.assertTrue(P.available(row, line+Q(1, 10000)))
            self.assertFalse(P.available(row, line-Q(1, 10000)))
            self.assertFalse(P.available(row, Q(1)))
        with self.assertRaises(ValueError):
            P.providers(['RH_moment'])
        with self.assertRaises(ValueError):
            P.providers(['moment8', 'moment2'])

    def test_fractional_absolute_powers_share_the_holder_budget(self):
        factors = [dict(real_part='3/4', power=x) for x in ['1/2', '1/3', '1/6']]
        r = P.product_bound(factors, ALL, METER)['best']
        self.assertEqual(r['integral_height_power'], '1')
        self.assertEqual(r['epsilon_coefficient'], '1/12')
        self.assertEqual(r['holder_unused'], '11/12')
        self.assertTrue(all(Q(f['convexity_power']) == 0 for f in r['factors']))
        self.assertTrue(all(f['moment_order'] == '12' for f in r['factors']))

    def test_a_strictly_negative_height_margin_is_required(self):
        boundary = P.candidate(2, 3, '2/3', '1/24', '1/3', ALL, METER)
        paid = P.candidate(2, 3, '2/3', '1/24', '7/20', ALL, METER)
        self.assertFalse(boundary['target_met'])
        self.assertEqual(boundary['mellin_height_powers'][1], '0')
        self.assertTrue(paid['target_met'])
        self.assertEqual(paid['full_finite_factor_U_power'], '13/2')
        self.assertEqual(paid['recovered_energy_N_power'], '-7/240')
        self.assertTrue(all(Q(x) < 0 for x in paid['paid_height_powers']))

    def test_library_expansion_changes_feasibility_without_nominating_a_contour(self):
        parent, _ = fixture()
        target = parent['auxiliary_bound_targets'][1]
        before = P.target_search(target, Q(1, 24), dict(P.DEFAULT_SPEC, library_ids=['moment2', 'moment4']), METER)
        after = P.target_search(target, Q(1, 24), P.DEFAULT_SPEC, METER)
        self.assertIsNone(before['selected'])
        self.assertIsNotNone(after['selected'])
        self.assertEqual(len(before['trials']), len(after['trials']))
        choice = after['trials'][after['selected']]
        self.assertLess(Q(choice['recovered_energy_N_power']), 0)
        self.assertFalse(choice['centering']['ordinary_coefficient_moment_claimed'])
        self.assertTrue(choice['centering']['unit_included'])
        self.assertTrue(choice['centering']['whole_x_below_one_tail_included'])

    def test_too_large_cutoff_rejects_an_otherwise_valid_contour(self):
        c = P.candidate(2, 3, '2/3', '1/4', '7/20', ALL, METER)
        self.assertTrue(all(Q(x) < 0 for x in c['paid_height_powers']))
        self.assertFalse(c['target_met'])
        self.assertIn('finite_factor_cost_exceeds_subpower_target', c['failed_premises'])

    def test_more_moments_alone_cannot_pay_the_next_absolute_envelope(self):
        a = P.ideal_moment_envelope(2, 3, '1/24')
        b = P.ideal_moment_envelope(2, 4, '1/24')
        self.assertFalse(a['stronger_moment_library_alone_insufficient'])
        self.assertEqual(b['optimistic_energy_infimum'], '1/16')
        self.assertTrue(b['stronger_moment_library_alone_insufficient'])
        self.assertFalse(b['arithmetic_impossibility_claimed'])
        self.assertTrue(P.ideal_moment_envelope(2, 4, '1/2')['cutoff_alone_obstructs'])

    def test_full_source_payment_preserves_drifts_and_both_recovery_directions(self):
        parent, context = fixture()
        spec = dict(P.DEFAULT_SPEC, sigma_denominator_max=6)
        # A synthetic valid analytic norm suffices to test source composition;
        # this test does not claim search completeness for its one witness.
        c = P.candidate(2, 3, '2/3', '1/24', '7/20', ALL, METER)
        t = dict(parent['auxiliary_bound_targets'][1], selected=0, trials=[c],
                 new_source_payment=True, constant='C_test')
        r = P.reduction(parent, context, [t], METER)
        self.assertIn('M_analytic', r['paid_components'][0]['retained_opposite_drift'])
        self.assertEqual(r['transport_error_retained'], '-e')
        b = r['bindings'][0]
        self.assertEqual(b['reverse'], 'S_Z033<=8*S_g+8*C_old+4*C_prev+2*C_033')
        self.assertEqual(b['residual_goal']['p'], '3')
        self.assertEqual(b['paid_constant_terms'][0]['local_cutoff_constant'], '8')
        self.assertGreater(Q(b['paid_constant_terms'][0]['rational_multiplier']), 9**2)
        parent['generated_bound_obligations'][0]['recovery'] = 'drop an old constant'
        with self.assertRaises(ValueError):
            P.reduction(parent, context, [t], METER)

    def test_cube_composition_pays_head_and_both_tail_errors(self):
        parent, _ = fixture()
        c = P.candidate(2, 3, '2/3', '1/24', '7/20', ALL, METER)
        target = dict(parent['auxiliary_bound_targets'][1], selected=0, trials=[c], constant='C_test')
        r = P.cube_composition(parent, [target])
        self.assertTrue(r['finite_cube_bound_proved'])
        self.assertEqual(len(r['finite_cube_energy_terms']), 4)
        self.assertEqual([x['multiplier'] for x in r['finite_cube_energy_terms']],
                         ['4', '576', '11019960576', '47405481984'])
        self.assertEqual(r['finite_cube_energy_terms'][1]['N_power'], '-11/12')
        self.assertFalse(r['original_fixed_sigma_low_Gram_proved'])
        parent['cutoff_work_targets'][0]['head_bound']['atom'] = 'delta'
        with self.assertRaises(ValueError):
            P.cube_composition(parent, [target])

    def test_different_fractional_kernel_retains_the_correct_integer_cell_cost(self):
        c = P.candidate(1, 2, '5/6', '1/48', '3/8', ALL, METER)
        self.assertEqual(c['residue_squared_U_power'], '1')
        self.assertEqual(c['integer_cell_correction']['residue_denominator'], '13/12')
        with self.assertRaises(ValueError):
            P.candidate(2, 3, '1/3', '1/24', '1/3', ALL, METER)
        with self.assertRaises(ValueError):
            P.candidate(True, 3, '2/3', '1/24', '7/20', ALL, METER)
        with self.assertRaises(ValueError):
            P.product_bound([dict(real_part='1', power='1/2')], ALL, METER)

    def test_resource_exhaustion_is_not_a_negative_mathematical_result(self):
        with self.assertRaises(OverflowError):
            P.product_bound([dict(real_part='3/4', power='1/6')], ALL, Meter(0, 60))

    def test_generic_parameters_cannot_change_the_actual_source_binding(self):
        parent, context = fixture()
        parent['auxiliary_bound_targets'][0]['theta'] = '5/6'
        with self.assertRaises(ValueError):
            P.search(parent, context, P.DEFAULT_SPEC, METER)
        parent, _ = fixture()
        parent['selected_source_representation']['alpha'] = '1/12'
        with self.assertRaises(ValueError):
            P.cube_composition(parent, parent['auxiliary_bound_targets'])


def tearDownModule():
    print('operations='+str(METER.operations))
