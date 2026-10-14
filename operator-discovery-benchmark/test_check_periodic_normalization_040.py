"""Synthetic exact source/cost challenges; no archive or production observation."""
from copy import deepcopy
from fractions import Fraction as F
import time
import unittest

from flint import arb, ctx
import prime_bank_candidates as BANK
import source_pole_guard as POLE_PRODUCER
import periodic_normalization_search_040 as PRODUCER
import check_periodic_normalization_040 as CHECK


START = time.monotonic()
METER = BANK.Meter(50_000_000, 180)


def model(lattice=14, r=5, v=9, beta='2'):
    return {'lattice': lattice, 'channels': [
        {'atoms': [{'kind': 'power', 'shift': r}, {'kind': 'mu', 'shift': 0},
                   {'kind': 'mu', 'shift': 0}], 'weight': [beta, '0']},
        {'atoms': [{'kind': 'power', 'shift': r}, {'kind': 'mu', 'shift': 0},
                   {'kind': 'mu', 'shift': v}], 'weight': [str(-F(beta)), '0']},
        {'atoms': [{'kind': 'power', 'shift': r}, {'kind': 'mu', 'shift': v}], 'weight': ['0', '-1']},
        {'atoms': [{'kind': 'mu', 'shift': 0}], 'weight': [str(-F(beta)), '0']}]}


def scalar_definition(s):
    theta = 1-F(s['channels'][0]['atoms'][0]['shift'], s['lattice'])
    v = F(s['channels'][2]['atoms'][1]['shift'], s['lattice'])
    beta = F(s['channels'][0]['weight'][0])
    rows = [{'coefficient': str(beta), 'powers': sorted([[str(theta), -2], [str(theta+v), 1]])},
            {'coefficient': str(-beta), 'powers': [[str(theta), -1]]}]
    return sorted(rows, key=lambda row: tuple(tuple(p) for p in row['powers']))


def normalization(s):
    return {'actual_R': scalar_definition(s), 'source_pole_certificate': POLE_PRODUCER.inspect(s, METER)}


def audit(s, proposal=None, norm=None, bound='100'):
    if proposal is None:
        proposal = PRODUCER.search(s, q_values=[2, 3], scalar_bound=bound, meter=METER)
    return CHECK.verify(s, proposal, normalization(s) if norm is None else norm,
                        scalar_bound=bound, meter=METER)


def row(proposal, q=2, power=1):
    return next(p for p in proposal['programs'] if p['q'] == q and p['power'] == power)


class PeriodicProof(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.source = model()
        cls.proposal = PRODUCER.search(cls.source, q_values=[2, 3], scalar_bound='100', meter=METER)
        cls.norm = normalization(cls.source)

    def reject(self, proposal):
        with self.assertRaises(ValueError):
            audit(self.source, proposal, self.norm)

    def test_changed_rational_family_and_global_minimax(self):
        result = audit(self.source, self.proposal, self.norm)
        self.assertTrue(result['verified'])
        self.assertEqual(self.proposal['hyperbola_search']['selected_alpha'], '9/23')
        self.assertEqual(self.proposal['hyperbola_search']['selected_exponent'], '9/23')
        self.assertEqual(self.proposal['hyperbola_search']['critical_shift_margin'], '11/322')
        self.assertEqual(result['minimax_dual_weights'], ['9/23', '14/23'])
        self.assertEqual(result['selected'], {'q': 2, 'power': 1})
        self.assertFalse(result['original_F_bound_proved'])

    def test_full_source_transform_is_a_coefficient_identity(self):
        program = row(self.proposal)
        self.assertEqual([c['periodic_copies'] for c in program['channels']], [0, 0, 1, 0])
        self.assertEqual([c['dilation_power'] for c in program['channels']], [1, 1, 0, 1])
        self.assertEqual([c['atoms'] for c in program['channels']], [
            [{'kind': 'mu', 'shift': '0'}, {'kind': 'power', 'shift': '5/14'}],
            [{'kind': 'power', 'shift': '5/14'}, {'kind': 'mu', 'shift': '9/14'}],
            [{'kind': 'power', 'shift': '5/14'}, {'kind': 'mu', 'shift': '9/14'}], []])
        self.assertEqual(program['prices'][3]['constant'], '2')
        self.assertEqual(program['reduction']['energy_implications']['new_target_from_preconditioned_source'],
                         {'target_coefficient': '1/2', 'remainder_coefficient': '1/2'})

    def test_periodic_primitive_and_real_prefix_bound(self):
        for q in (2, 3, 5):
            total = 0
            for n in range(1, 20):
                total += 1-q*int(n % q == 0)
                self.assertEqual(total, n-q*(n//q))
                self.assertTrue(0 <= total <= q-1)
            self.assertEqual(1+F(-q, q), 0)
        self.assertTrue(audit(self.source, self.proposal, self.norm)['normalization_exact'])

    def test_all_real_hyperbola_calibration_including_subunit(self):
        old = ctx.prec
        try:
            ctx.prec = 160
            theta = F(2, 3)
            sigma = F(2, 5)
            t = arb(theta.numerator)/theta.denominator
            z = t.zeta()
            for q in (2, 3):
                moment = (1-(arb(q).log()*(1-t)).exp())*z
                for x in (F(1, 2), F(1), F(3, 2), F(7, 2), F(9)):
                    a = arb(x.numerator)/x.denominator
                    prefix = arb(0)
                    for n in range(1, x.numerator//x.denominator+1):
                        for d in range(1, n+1):
                            if n % d == 0:
                                prefix += (1-q*int(d % q == 0))*(arb(n//d).log()*(t-1)).exp()
                    centered = prefix-moment*(a.log()*t).exp()/t
                    constant = F(7*(q-1), 1)/theta
                    upper = arb(constant.numerator)/constant.denominator*(a.log()*
                            (arb(sigma.numerator)/sigma.denominator)).exp()
                    self.assertTrue(abs(centered) <= upper)
        finally:
            ctx.prec = old

    def test_changed_legal_periods_and_unrestricted_rational_source(self):
        s = model(lattice=257, r=123, v=193)
        p = PRODUCER.search(s, q_values=[4, 17], scalar_bound='100', meter=METER)
        self.assertEqual(audit(s, p)['selected'], {'q': 4, 'power': 1})
        self.assertEqual(p['family']['theta'], '134/257')

    def test_exact_normalization_and_scalar_bound_required(self):
        bad = deepcopy(self.norm)
        bad['actual_R'] = [{'coefficient': '2', 'powers': []}]
        with self.assertRaises(ValueError): audit(self.source, self.proposal, bad)
        bad = {'actual_R': {'lower': '1', 'upper': '5'}, 'source_pole_certificate': self.norm['source_pole_certificate']}
        with self.assertRaises(ValueError): audit(self.source, self.proposal, bad)
        p = PRODUCER.search(self.source, q_values=[2], scalar_bound='1/1000', meter=METER)
        with self.assertRaises(ValueError): audit(self.source, p, bound='1/1000')

    def test_source_unit_sign_and_role_swap_rejected(self):
        for mode in ('unit', 'weight', 'source', 'shift'):
            bad = deepcopy(self.proposal)
            if mode == 'unit': bad['source_binding']['channels'].pop()
            elif mode == 'weight': row(bad)['channels'][1]['weight'][0] = '2'
            elif mode == 'source': row(bad)['channels'][0]['source_channel'] = 2
            else: bad['family']['v'] = '5/14'
            self.reject(bad)

    def test_missing_preconditioner_terms_or_mean_rejected(self):
        for mode in ('step', 'mean', 'negative_prefix', 'unit'):
            bad = deepcopy(self.proposal)
            periodic = row(bad)['periodic']
            if mode == 'step': periodic['step_coefficients'].pop()
            elif mode == 'mean': periodic['solved_mean_equation'][1] = '1'
            elif mode == 'negative_prefix': periodic['prefix_nonnegative'] = False
            else: row(bad)['channels'][3]['unit_retained'] = False
            self.reject(bad)

    def test_missing_hyperbola_branch_vertex_and_wrong_optimum(self):
        for mode in ('line', 'vertex', 'optimum', 'margin'):
            bad = deepcopy(self.proposal)
            h = bad['hyperbola_search']
            if mode == 'line': h['lines'].pop()
            elif mode == 'vertex': h['vertices'].pop()
            elif mode == 'optimum': h['selected_alpha'] = '1/257'
            else: h['critical_shift_margin'] = '1'
            self.reject(bad)

    def test_strict_contraction_boundary_remains_open(self):
        s = model(lattice=6, r=2, v=3)
        p = PRODUCER.search(s, q_values=[2], scalar_bound='100', meter=METER)
        self.assertEqual(p['hyperbola_search']['critical_shift_margin'], '-1/10')
        self.assertFalse(p['hyperbola_search']['absolute_shift_contraction'])
        self.assertNotIn('reduction', row(p))
        self.assertIsNone(audit(s, p)['selected'])
        bad = deepcopy(p)
        row(bad)['prices'][2]['status'] = 'PROVED'
        with self.assertRaises(ValueError): audit(s, bad)

    def test_padded_exponent_proves_strict_margin_without_changing_split(self):
        s = model(lattice=15, r=5, v=9)
        p = PRODUCER.search(s, q_values=[2], scalar_bound='100', meter=METER)
        h = p['hyperbola_search']
        self.assertEqual(h['envelope_minimum'], '2/5')
        self.assertEqual(h['selected_alpha'], '2/5')
        self.assertEqual(h['selected_exponent'], '9/20')
        self.assertEqual(h['critical_shift_margin'], '1/20')
        self.assertEqual(audit(s, p)['selected'], {'q': 2, 'power': 1})
        bad = deepcopy(p)
        bad['hyperbola_search']['selected_exponent'] = '2/5'
        with self.assertRaises(ValueError): audit(s, bad)

    def test_full_shifted_tail_and_subunit_cost_required(self):
        for mode in ('tail', 'subunit', 'kernel'):
            bad = deepcopy(self.proposal)
            price = row(bad)['prices'][2]
            if mode == 'tail': price['constant'] = str(F(price['constant'])/2)
            elif mode == 'subunit': price['all_subunit_arguments_retained'] = False
            else: row(bad)['prices'][1]['constant'] = '0'
            self.reject(bad)

    def test_all_dilation_coefficients_are_retained(self):
        bad = deepcopy(self.proposal)
        row(bad, power=2)['prices'][0]['full_dilation'].pop()
        self.reject(bad)
        bad = deepcopy(self.proposal)
        row(bad)['prices'][3]['constant'] = '0'
        self.reject(bad)

    def test_norm_recovery_beta_triangle_and_growth_costs(self):
        for mode in ('beta', 'triangle', 'growth', 'constant', 'head'):
            bad = deepcopy(self.proposal)
            r = row(bad)['reduction']
            if mode == 'beta': r['open_weight'] = '1'
            elif mode == 'triangle': r['energy_implications']['preconditioned_source_from_new_target']['remainder_coefficient'] = '1'
            elif mode == 'growth': r['paid_remainder']['energy_power'] = '-1'
            elif mode == 'constant': r['paid_remainder']['energy_constant'] = str(F(r['paid_remainder']['energy_constant'])/4)
            else: r['paid_remainder']['constant'] = str(F(r['paid_remainder']['constant'])-2)
            self.reject(bad)

    def test_two_copies_destroy_registered_rh_bridge(self):
        erased = row(self.proposal, power=2)
        self.assertEqual(erased['pole_budget']['channel_orders'], [0, -1, -2, -1])
        self.assertFalse(erased['pole_budget']['RH_pole_bridge_available'])
        self.assertEqual(erased['open_source_channels'], [2])
        bad = deepcopy(self.proposal)
        row(bad, power=2)['pole_budget']['RH_pole_bridge_available'] = True
        self.reject(bad)

    def test_false_closure_ordinary_moment_and_bounded_inverse_rejected(self):
        for mode in ('closure', 'ordinary', 'inverse', 'rh', 'cycle'):
            bad = deepcopy(self.proposal)
            if mode == 'closure': row(bad)['reduction']['new_target_bound_proved'] = True
            elif mode == 'ordinary': row(bad)['centering']['ordinary_mu_moment_assumed'] = True
            elif mode == 'inverse': row(bad)['reduction']['inverse_A_q_bound_used'] = True
            elif mode == 'rh': bad['RH_proved'] = True
            else: bad['proof_dependencies'] = [{'id': 'root', 'premises': ['root'], 'proved': True}]
            self.reject(bad)

    def test_full_dictionary_coverage_and_selection(self):
        for mode in ('program', 'selected', 'power', 'q'):
            bad = deepcopy(self.proposal)
            if mode == 'program': bad['programs'].pop()
            elif mode == 'selected': bad['selected'] = {'q': 3, 'power': 1}
            elif mode == 'power': bad['powers'] = [0, 1]
            else: bad['q_values'] = [2, 2]
            self.reject(bad)

    def test_source_order_is_not_a_hardcoded_actual_answer(self):
        s = model()
        s['channels'] = [s['channels'][2], s['channels'][3], s['channels'][0], s['channels'][1]]
        p = PRODUCER.search(s, q_values=[3], scalar_bound='100', meter=METER)
        # The normalization definition is preserved from the unreordered model.
        n = {'actual_R': scalar_definition(model()), 'source_pole_certificate': POLE_PRODUCER.inspect(s, METER)}
        result = audit(s, p, n)
        self.assertEqual(p['family']['channel_roles'], [2, 3, 0, 1])
        self.assertEqual(result['selected'], {'q': 3, 'power': 1})

    def test_strict_types_and_production_meter(self):
        for mode in ('bool', 'float', 'coefficient', 'extra'):
            bad = deepcopy(self.proposal)
            if mode == 'bool': bad['powers'][1] = True
            elif mode == 'float': bad['q_values'][0] = 2.0
            elif mode == 'coefficient': row(bad)['prices'][1]['constant'] = '2/2'
            else: bad['fitted_uniform_constant'] = '1'
            self.reject(bad)
        self.assertGreater(METER.operations, 0)


def tearDownModule():
    print('SYNTHETIC_WORK module=test_check_periodic_normalization_040 operations=%d elapsed_seconds=%.6f' %
          (METER.operations, time.monotonic()-START))


if __name__ == '__main__':
    unittest.main()
