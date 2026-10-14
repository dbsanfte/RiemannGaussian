import copy
from fractions import Fraction as Q
import tempfile
from pathlib import Path
import unittest

import reversible_divisor_circuits as L
import reversible_circuit_discovery as D
import run_reversible_circuit_discovery as R

WORK = L.Meter(2000000)


def conv(alpha, phase=None):
    return dict(op='convolve', alpha=alpha, prime_phase=phase or ['constant', 1])


class CircuitDiscoveryTests(unittest.TestCase):
    def test_complete_divisor_operator_not_floor_sum(self):
        values = [0, 1, -1, -1, 0, -1, 1, -1, 0, 0, 1, -1, 0]
        output = L.evaluate({'stages': [conv('1')]}, values, WORK)
        prefix = L.evaluate({'stages': []}, values, WORK)
        for n in range(1, len(values)):
            WORK.charge(n)
            self.assertEqual(output[n], sum(prefix[d] for d in range(1, n + 1) if n % d == 0))
        self.assertEqual(output[11], prefix[11] + prefix[1])
        self.assertNotEqual(output[11], sum(prefix[11 // d] for d in range(1, 12)))

    def test_fractional_circuits_have_exact_inverse_same_source(self):
        values = [0] + [(-1, 0, 1, 1, -1)[n % 5] for n in range(1, 65)]
        prefix = L.evaluate({'stages': []}, values, WORK)
        for alpha in ['-1/2', '-1/3', '-1/6', '1/6', '2']:
            program = {'stages': [
                conv(alpha, ['source_sign', ['subtract_root', 1, 2]]),
                dict(op='sign', phase=['multiply', ['source_sign', ['n']], ['parity', ['root', 2, 3]]]),
                conv('-1/3', ['residue_sign', ['n'], 5, [1, 4]])]}
            transformed = L.evaluate(program, values, WORK)
            restored = L.apply_to_state(L.inverse(program, WORK), values, transformed, WORK)
            self.assertEqual(restored, prefix)

    def test_zero_source_coefficients_do_not_erase_coordinates(self):
        values = [0, 1, 0, -1, 0, 1, 0, 0]
        program = {'stages': [dict(op='sign', phase=['source_sign', ['n']])]}
        transformed = L.evaluate(program, values, WORK)
        restored = L.apply_to_state(program, values, transformed, WORK)
        self.assertEqual(restored, L.evaluate({'stages': []}, values, WORK))
        self.assertEqual(transformed[2], 1)
        with self.assertRaises(ValueError):
            L.validate({'stages': [dict(op='sign', phase=['mu', ['n']])]}, WORK)

    def test_exact_fractional_index_boundaries(self):
        for denominator in (2, 3, 6):
            n = 3 ** denominator
            for x, expected in ((n - 1, 2), (n, 3), (n + 1, 3)):
                self.assertEqual(L.root(x, 1, denominator, WORK), expected)
        self.assertEqual(L.root(0, 1, 6, WORK), 0)
        self.assertEqual(L.root(64, 2, 3, WORK), 16)

    def test_strict_source_and_syntax_domains(self):
        for invalid in (
                {'stages': [conv('2/4')]}, {'stages': [conv('0')]},
                {'stages': [dict(op='sign', phase=['constant', 0])]},
                {'stages': [dict(op='sign', phase=['parity', ['root', 2, 2]])]},
                {'stages': [dict(op='sign', phase=['parity', ['root', True, 2]])]},
                {'stages': [dict(op='sign', phase=['residue_sign', ['n'], 3, [2, 1]])]},
                {'stages': [conv('1')] * 4}, {'stages': [], 'target': 'other'}):
            with self.assertRaises((ValueError, OverflowError)):
                L.validate(invalid, WORK)
        for values in ([0], [True, 1], [0, True], [0, 2]):
            with self.assertRaises(ValueError):
                L.evaluate({'stages': []}, values, WORK)

    def test_full_energy_with_all_cross_terms(self):
        values = [0] + [1, -1, 0, 1] * 8
        output = L.evaluate({'stages': [conv('-1/2'), conv('1/3')]}, values, WORK)
        measured = L.moments(output, [4, 8, 16], WORK)
        for row in measured:
            X = row['X']; WORK.charge(X)
            self.assertEqual(Q(row['energy']), sum(value * value for value in output[X:2 * X]) / Q(X * X))
        with self.assertRaises(ValueError):
            L.moments(output, [17], WORK)
        with self.assertRaises(ValueError):
            L.moments(output, [4, 4], WORK)

    def test_complete_arithmetic_controls(self):
        actual = L.source('mu', 32, WORK)
        control = L.source('partial_prime_13', 32, WORK)
        self.assertEqual(actual[:17], control[:17])
        self.assertEqual((actual[17], control[17]), (-1, 1))
        self.assertEqual(control[25], 0)
        self.assertEqual(actual[30], -1)
        self.assertEqual(L.source('one', 3, WORK), [0, 1, 1, 1])

    def test_generation_covers_structures_and_replays(self):
        first = D.generate(WORK)
        self.assertEqual(first, D.generate(WORK))
        self.assertEqual([r['id'] for r in first], list(range(65)))
        self.assertEqual(first[0]['program'], {'stages': []})
        for family in D.FAMILIES:
            self.assertEqual(sum(r['family'] == family for r in first), 16)
        for r in first[1:]:
            self.assertEqual(r['program']['stages'][-1]['op'], 'convolve')
            self.assertEqual(r['certificate']['program'], r['program'])
            self.assertEqual(L.inverse(r['inverse'], WORK), r['program'])
        interleaved = [r for r in first if r['family'] == 'interleaved']
        for record in interleaved[::4]:
            stages = record['program']['stages']
            self.assertEqual(stages[0]['prime_phase'], stages[2]['prime_phase'])
            self.assertEqual(Q(stages[0]['alpha']), -Q(stages[2]['alpha']))

    def test_train_fit_and_frozen_bound_fail_on_larger_response(self):
        cases = [dict(X=32, energy='3/8'), dict(X=64, energy='1/2')]
        fitted = D.constants(cases, WORK)
        saved = copy.deepcopy(fitted)
        scores = D.scores([dict(X=1024, energy='100')], fitted, WORK)
        self.assertTrue(all(not row['passed'] for row in scores))
        self.assertEqual(fitted, saved)
        self.assertEqual(fitted, R._independent_fit(cases, WORK))
        self.assertEqual(scores, R._independent_scores([dict(X=1024, energy='100')], fitted, WORK))

    def test_selection_retains_family_diversity_and_inverse_cost(self):
        records = D.generate(WORK)
        evidence = [dict(id=r['id'], status='available', initial_cost='1',
                         constants={str(q): '1/4' for q in D.LEVELS}, scores=[]) for r in records]
        selected = D.choose(records, evidence, WORK)
        self.assertEqual(selected, R._independent_choose(records, evidence, WORK))
        self.assertEqual(len(selected), 8)
        self.assertEqual([sum(r['family'] == family for r in selected) for family in D.FAMILIES], [2, 2, 2, 2])
        row = evidence[1]
        self.assertEqual(D.conditional_cost(records[1], row, 12, WORK), 13 ** 2 * 13)
        row['status'] = 'missing'
        self.assertNotIn(1, [r['id'] for r in D.choose(records, evidence, WORK)])

    def test_artifact_write_is_exclusive(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'protocol.json'
            R.write(path, {'immutable': True})
            self.assertEqual(R.read(path), {'immutable': True})
            with self.assertRaises(FileExistsError):
                R.write(path, {'immutable': False})


def tearDownModule():
    print('SYNTHETIC_WORK module=test_reversible_circuit_discovery operations=' + str(WORK.operations))


if __name__ == '__main__':
    unittest.main()
