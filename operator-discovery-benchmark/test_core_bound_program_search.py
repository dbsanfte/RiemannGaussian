import copy
from fractions import Fraction as F
import unittest
from flint import arb, ctx
from prime_bank_candidates import Meter
import core_bound_program_search as P
import check_core_bound_program_search as C


M = Meter(20000000, 120)


def tearDownModule():
    print('SYNTHETIC_WORK module=test_core_bound_program_search operations='+str(M.operations))


class BoundSearchTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        ctx.prec = 192

    def test_recovery_rejects_common_zero_and_disguised_target_loss(self):
        self.assertIsNone(P.recover([(F(1), F(-1)), (F(1), F(-2), F(1))]))
        p = P.compile_program([(F(1), F(-1)), (F(0), F(1))], F(1), M)
        self.assertTrue(C.check_program(p, M)['verified'])
        p['recovery_coefficients'][0] = '2'
        with self.assertRaises(ArithmeticError):
            C.check_program(p, M)

    def test_fractional_weights_and_recovery_cost_cannot_be_dropped(self):
        for eta in ('1/6', '1/3', '1/2', '2/3', '1', '3/2'):
            p = P.compile_program([(F(1), F(-2), F(1)), (F(0), F(2), F(-1))], F(eta), M)
            self.assertTrue(C.check_program(p, M)['verified'])
            self.assertEqual(F(p['recovered_detail_log_power']), 3)
            b = P.target_branch(p, '1/2', '2', '1/2', M)
            self.assertEqual(b['status'], 'unpaid_recovered_detail_log')
            self.assertTrue(C.check_branch(p, b, M))
        bad = copy.deepcopy(p)
        bad['recovery_log_power'] = '0'
        with self.assertRaises(ArithmeticError):
            C.check_program(bad, M)

    def test_complete_prefix_semantics_against_separate_raw_moments(self):
        p = P.compile_program([(F(1), F(-3), F(3), F(-1)), (F(0), F(3), F(-3), F(1))], F(1, 3), M)
        g = [arb(0)] + [arb(-9)] + [arb((n*n+3*n) % 7 - 3) for n in range(2, 20)]
        channels = P.literal_channels(g, p)
        for n in (1, 2, 7, 19):
            L = arb(2*n).log()
            recovered = arb(0)
            for i, channel in enumerate(p['channels']):
                eta = F(channel['eta'])
                raw = arb(0)
                for j, c in enumerate(channel['polynomial']):
                    q = F(c)
                    H = sum((g[k]*arb(k).log()**j for k in range(1, n+1)), arb(0))
                    raw += (arb(q.numerator)/q.denominator)*H/L**j
                self.assertTrue((raw/L.root(eta.denominator)**eta.numerator).overlaps(channels[i][n]))
                a = F(p['recovery_coefficients'][i])
                recovered += (arb(a.numerator)/a.denominator)*L.root(eta.denominator)**eta.numerator*channels[i][n]
            self.assertTrue(recovered.overlaps(sum(g[1:n+1], arb(0))))
        M.charge(120000)

    def test_generic_generator_finds_higher_cancellations_without_named_formula(self):
        spec = dict(degree=3, coefficient_cap=3, coefficient_l1=8,
                    recovery_multipliers=['-1', '1'], gains=['0', '1/3', '1'],
                    meshes=['1/3', '1/2', '2/3'], target_log_powers=['2', '3'],
                    rhos=['1/2', '1'], archive_limit=18)
        result = P.search(spec, M)
        self.assertTrue(any(p['cancellation_order'] == 3 for p in result['programs']))
        self.assertTrue(any(F(c['eta']).denominator == 3 for p in result['programs'] for c in p['channels']))
        self.assertFalse(result['candidate_selection_uses_source_values'])
        self.assertTrue(result['selected'])
        for b in result['selected']:
            p = result['programs'][b['program_id']]
            self.assertTrue(C.check_program(p, M)['verified'])
            self.assertTrue(C.check_branch(p, b, M))
            self.assertFalse(b['full_bound_proved'])

    def test_backward_target_and_all_scale_payment(self):
        p = P.compile_program([(F(1), F(-1)), (F(0), F(1))], F(1), M)
        b = P.target_branch(p, '1/3', '2', '1/2', M)
        self.assertEqual(b['status'], 'partial_bound_open_signed_coarse')
        self.assertEqual(b['required_coarse_forcing_log_power'], '0')
        self.assertTrue(C.check_branch(p, b, M))
        self.assertEqual(P.target_branch(p, '2/3', '100', '1/2', M)['status'], 'unpaid_detail_power')
        self.assertEqual(P.target_branch(p, '1/3', '1', '1/2', M)['status'],
                         'requires_decaying_coarse_bound_outside_recurrence_rule')
        bad = dict(b, detail_absorption_constant='1')
        with self.assertRaises(ArithmeticError):
            C.check_branch(p, bad, M)

    def test_open_leaf_survives_and_circular_proofs_are_rejected(self):
        p = P.compile_program([(F(1), F(-1)), (F(0), F(1))], F(1), M)
        b = P.target_branch(p, '1/3', '2', '1/2', M)
        parent = dict(id='complete-source', transport_program=dict(theta='5/6'), uniform_premise_established=False)
        ob = P.open_obligation(p, b, parent)
        self.assertTrue(C.check_dependency_graph(ob))
        self.assertFalse(ob['required']['proved'])
        self.assertFalse(ob['variable_weights_commuted_through_projection'])
        bad = copy.deepcopy(ob)
        bad['dependency_graph'][0]['depends_on'] = ['core_growth']
        with self.assertRaises(ValueError):
            C.check_dependency_graph(bad)
        bad = copy.deepcopy(ob)
        bad['dependency_graph'][-1]['status'] = 'proved'
        with self.assertRaises(ValueError):
            C.check_dependency_graph(bad)
        guard = P.weak_fact_guard(p, b)
        self.assertFalse(guard['actual_core_bound_disproved'])
        self.assertFalse(guard['full_actual_source_AST_satisfied'])


if __name__ == '__main__':
    unittest.main()
