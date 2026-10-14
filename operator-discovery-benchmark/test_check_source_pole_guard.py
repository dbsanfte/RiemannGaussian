"""Small source ASTs and adversarial normalization checks; no source samples."""
from copy import deepcopy
from fractions import Fraction as Q
import time
import unittest

from flint import ctx
import prime_bank_candidates as BANK
import source_pole_guard as PRODUCER
import check_source_pole_guard as CHECK


START = time.monotonic()
METER = BANK.Meter(50_000_000, 180)


def source():
    return {'lattice': 6, 'channels': [
        {'atoms': [{'kind': 'power', 'shift': 2}, {'kind': 'mu', 'shift': 0}, {'kind': 'mu', 'shift': 0}],
         'weight': ['9/2', '0']},
        {'atoms': [{'kind': 'power', 'shift': 2}, {'kind': 'mu', 'shift': 0}, {'kind': 'mu', 'shift': 4}],
         'weight': ['-9/2', '0']},
        {'atoms': [{'kind': 'power', 'shift': 2}, {'kind': 'mu', 'shift': 4}], 'weight': ['0', '-1']},
        {'atoms': [{'kind': 'mu', 'shift': 0}], 'weight': ['-9/2', '0']}]}


def binding():
    return [{'coefficient': '9/2', 'powers': [['2/3', -2], ['4/3', 1]]},
            {'coefficient': '-9/2', 'powers': [['2/3', -1]]}]


def simple(weight=('1', '-1')):
    return {'lattice': 2, 'channels': [{'atoms': [{'kind': 'power', 'shift': 0}],
                                      'weight': list(weight)}]}


def admit(s, scalar=None, proposal=None, **kwargs):
    p = PRODUCER.inspect(s, METER) if proposal is None else proposal
    return CHECK.verify(s, p, actual_R=scalar, meter=METER, **kwargs)


class PoleAudit(unittest.TestCase):
    def test_source_generated_residue_matches_hand_algebra(self):
        p = PRODUCER.inspect(source(), METER)
        self.assertEqual(p['positive_poles'][0]['channel_orders'], [1, 1, 1, 0])
        self.assertEqual(p['positive_poles'][0]['residue'], {
            'constant': [{'coefficient': '9/2', 'powers': [['2/3', -2]]},
                         {'coefficient': '-9/2', 'powers': [['2/3', -1], ['4/3', -1]]}],
            'R': [{'coefficient': '-1', 'powers': [['4/3', -1]]}]})
        self.assertEqual(p['positive_poles'][0]['cancellation']['laurent_solution'], binding())
        self.assertTrue(admit(source(), binding(), p)['verified'])

    def test_correct_exact_normalization_and_family_obstruction_are_distinct(self):
        result = admit(source(), binding())
        pole = result['pole_checks'][0]
        self.assertTrue(pole['exact_cancellation_proved'])
        self.assertEqual(pole['substituted_residue'], [])
        self.assertFalse(pole['binding_residue_nonzero'])
        self.assertTrue(pole['formal_family_pole_proved'])
        self.assertTrue(pole['family_subpower_energy_excluded'])
        self.assertFalse(result['scope']['actual_source_bound_refuted'])
        self.assertFalse(result['scope']['uniform_bound_proved'])
        self.assertFalse(result['ordinary_series_convergence_at_poles_asserted'])

    def test_mismatching_exact_scalar_has_uncancelled_source_family_pole(self):
        result = admit(source(), [{'coefficient': '2', 'powers': []}])
        pole = result['pole_checks'][0]
        self.assertFalse(pole['exact_cancellation_proved'])
        self.assertTrue(pole['supplied_binding_subpower_energy_excluded'])
        self.assertFalse(result['scope']['actual_source_bound_refuted'])

    def test_interval_only_scalar_cannot_replace_fixed_definition(self):
        for bad in ({'lower': '1', 'upper': '5'}, '4.543468', [1, 5]):
            with self.assertRaises(ValueError):
                admit(source(), bad)
        self.assertFalse(admit(source())['pole_checks'][0]['normalization_admitted'])

    def test_exact_cancellation_not_numeric_zero_containment(self):
        shifted = binding() + [{'coefficient': str(Q(1, 2**1024)), 'powers': []}]
        shifted.sort(key=lambda row: tuple(tuple(p) for p in row['powers']))
        result = admit(source(), shifted)
        self.assertFalse(result['pole_checks'][0]['exact_cancellation_proved'])
        self.assertNotEqual(result['pole_checks'][0]['substituted_residue'], [])

    def test_whole_channel_and_unit_term_cannot_be_omitted(self):
        p = PRODUCER.inspect(source(), METER)
        for change in ('unit', 'channel', 'pole'):
            bad = deepcopy(p)
            if change == 'unit': bad['channels'].pop()
            elif change == 'channel': bad['source_binding']['channels'].pop(1)
            else: bad['positive_poles'].clear()
            with self.assertRaises(ValueError): admit(source(), binding(), bad)

    def test_valuation_factors_are_combined_before_poles(self):
        s = simple()
        s['channels'][0]['atoms'].append({'kind': 'mu', 'shift': 0})
        p = PRODUCER.inspect(s, METER)
        self.assertEqual(p['channels'][0]['factors'], [])
        self.assertEqual(admit(s, proposal=p)['pole_checks'], [])

    def test_multiple_poles_and_half_boundary(self):
        s = {'lattice': 2, 'channels': [
            {'atoms': [{'kind': 'power', 'shift': 0}], 'weight': ['1', '0']},
            {'atoms': [{'kind': 'power', 'shift': 1}], 'weight': ['1', '0']}]}
        result = admit(s)
        self.assertEqual([r['point'] for r in result['pole_checks']], ['1/2', '1'])
        self.assertFalse(result['pole_checks'][0]['family_subpower_energy_excluded'])
        self.assertTrue(result['pole_checks'][1]['family_subpower_energy_excluded'])

    def test_higher_order_is_not_treated_as_one_residue(self):
        s = simple()
        s['channels'][0]['atoms'] *= 2
        result = admit(s, [{'coefficient': '1', 'powers': []}])
        self.assertEqual(result['pole_checks'][0]['status'], 'higher_order_unsupported')
        self.assertFalse(result['pole_checks'][0]['normalization_admitted'])
        bad = PRODUCER.inspect(s, METER)
        bad['positive_poles'][0]['status'] = 'simple_affine_residue'
        with self.assertRaises(ValueError): admit(s, proposal=bad)

    def test_nonpositive_regular_argument_is_explicitly_unsupported(self):
        s = {'lattice': 2, 'channels': [{'atoms': [{'kind': 'power', 'shift': 1},
                                                                {'kind': 'mu', 'shift': -2}],
                                      'weight': ['1', '0']}]}
        result = admit(s)
        self.assertEqual(result['initial_identity_domain'], 'Re(s)>2')
        self.assertEqual(result['pole_checks'][0]['status'], 'nonpositive_regular_argument_unsupported')

    def test_nonmonomial_affine_denominator_has_no_fabricated_laurent_solution(self):
        s = {'lattice': 2, 'channels': [
            {'atoms': [{'kind': 'power', 'shift': 0}], 'weight': ['1', '1']},
            {'atoms': [{'kind': 'power', 'shift': 0}, {'kind': 'mu', 'shift': 2}], 'weight': ['0', '1']}]}
        p = PRODUCER.inspect(s, METER)
        self.assertIsNone(p['positive_poles'][0]['cancellation']['laurent_solution'])
        self.assertTrue(admit(s, proposal=p)['verified'])
        p['positive_poles'][0]['cancellation']['laurent_solution'] = []
        with self.assertRaises(ValueError): admit(s, proposal=p)

    def test_no_parameter_and_zero_residue_are_distinguished(self):
        p = PRODUCER.inspect(simple(('1', '0')), METER)
        self.assertIsNone(p['positive_poles'][0]['cancellation']['laurent_solution'])
        self.assertTrue(admit(simple(('1', '0')))['pole_checks'][0]['formal_family_pole_proved'])
        s = {'lattice': 2, 'channels': simple(('1', '0'))['channels'] + simple(('-1', '0'))['channels']}
        result = admit(s, [])
        self.assertTrue(result['pole_checks'][0]['exact_cancellation_proved'])
        self.assertFalse(result['pole_checks'][0]['formal_family_pole_proved'])

    def test_mutated_orders_solution_and_scope_rejected(self):
        original = PRODUCER.inspect(source(), METER)
        for name in ('order', 'denominator', 'solution', 'scope', 'abscissa'):
            bad = deepcopy(original)
            if name == 'order': bad['positive_poles'][0]['channel_orders'][3] = 1
            elif name == 'denominator': bad['positive_poles'][0]['cancellation']['denominator'] = []
            elif name == 'solution': bad['positive_poles'][0]['cancellation']['laurent_solution'][0]['coefficient'] = '1'
            elif name == 'scope': bad['scope']['uniform_bound_proved'] = True
            else: bad['initial_abscissa'] = '2/3'
            with self.assertRaises(ValueError): admit(source(), binding(), bad)

    def test_strict_input_and_forged_argument_guards(self):
        for kind in ('bool', 'float', 'noncanonical'):
            s = simple()
            if kind == 'bool': s['lattice'] = True
            elif kind == 'float': s['channels'][0]['atoms'][0]['shift'] = 0.0
            else: s['channels'][0]['weight'][0] = '2/2'
            with self.assertRaises(ValueError):
                CHECK.verify(s, {}, meter=METER)
        for scalar in ([{'coefficient': '1', 'powers': [['1', -1]]}],
                       [{'coefficient': '1', 'powers': [['0', 1]]}],
                       [{'coefficient': '1', 'powers': [['2', True]]}]):
            with self.assertRaises(ValueError): admit(simple(), scalar)
        with self.assertRaises(ValueError): admit(simple(), target_sigma='1/3')

    def test_precision_restored_and_external_meter_supported(self):
        old = ctx.prec
        ctx.prec = 90
        try:
            result = admit(simple(), [{'coefficient': '1', 'powers': []}])
            self.assertEqual(ctx.prec, 90)
            self.assertTrue(result['pole_checks'][0]['exact_cancellation_proved'])
            self.assertGreater(METER.operations, 0)
        finally:
            ctx.prec = old


def tearDownModule():
    print('SYNTHETIC_WORK module=test_check_source_pole_guard operations=%d elapsed_seconds=%.6f' %
          (METER.operations, time.monotonic() - START))


if __name__ == '__main__':
    unittest.main()
