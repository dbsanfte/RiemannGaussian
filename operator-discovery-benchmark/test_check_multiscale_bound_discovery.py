"""Synthetic adversarial admission tests; no held-out/source observations."""
import copy
from fractions import Fraction as F
import time
import unittest

import check_multiscale_bound_discovery as C
from prime_bank_candidates import Meter


METER = Meter(cap=50000000, seconds=180)
STARTED = time.monotonic()


def encode(a):
    return [[str(x) for x in row] for row in a]


def identity(n):
    return [[F(int(i == j)) for j in range(n)] for i in range(n)]


def make_model(matrices, initial, output, base=2):
    return dict(base=base, matrices=[encode(a) for a in matrices],
                initial=list(map(str, initial)), output=list(map(str, output)))


def certificate(states, matrices, alpha, projection, block, metric, base=2):
    return dict(base=base, states=states, transitions=[encode(a) for a in matrices],
                bound=dict(alpha=str(alpha), projection=encode(projection),
                           block_transition=encode(block), Q=encode(metric)))


def alternating():
    matrices = [[[1, 0], [1, 0]], [[1, 0], [-1, 0]]]
    model = make_model(matrices, [1, 1], [0, 1])
    transitions = [[[0, 1], [0, 1]], [[0, -1], [0, 1]]]
    cert = certificate([[1, 0], [2, 0]], transitions, 0, [[1, 0]], [[0]], [[1]])
    return model, cert


def fractional(q):
    cycle = [[F(int(j == (i + 1) % q)) for j in range(q)] for i in range(q)]
    sparse = [[F(int(i == 0 and j == 1)) for j in range(q)] for i in range(q)]
    block = [[a + b for a, b in zip(x, y)] for x, y in zip(cycle, sparse)]
    model = make_model([cycle, sparse], [1] * q, [1] + [0] * (q - 1))
    cert = certificate([[2 ** k, 0] for k in range(q)], [cycle, sparse],
                       F(1, q), identity(q), block, identity(q))
    return model, cert


def value(model, n):
    vector = list(map(F, model['initial']))
    digits = []
    while n:
        digits.append(n % model['base'])
        n //= model['base']
    for digit in reversed(digits):
        matrix = [[F(x) for x in row] for row in model['matrices'][digit]]
        METER.charge(len(vector) ** 2)
        vector = [sum((x * y for x, y in zip(row, vector)), F(0)) for row in matrix]
    return sum((F(x) * y for x, y in zip(model['output'], vector)), F(0))


class AdmissionTests(unittest.TestCase):
    def assert_prefixes(self, model, admission, last=128):
        total, alpha = F(0), F(admission['alpha'])
        constant = F(admission['squared_bound']['constant'])
        for n in range(1, last + 1):
            total += value(model, n - 1)
            if alpha:
                self.assertLessEqual(total ** (2 * alpha.denominator),
                                     constant ** alpha.denominator * n ** (2 * alpha.numerator))
            else:
                level, rest = 0, n
                while rest >= model['base']:
                    rest //= model['base']
                    level += 1
                self.assertLessEqual(total ** 2, constant * (1 + level) ** 2)

    def test_alternating_target_quotient_discards_unobserved_growth(self):
        model, cert = alternating()
        answer = C.verify(model, cert, METER)
        self.assertTrue(answer['verified'])
        self.assertEqual(answer['bound_dimension'], 1)
        self.assertEqual(answer['alpha'], '0')
        self.assertEqual(answer['squared_bound']['constant'], '1')
        self.assertEqual(answer['squared_bound']['expression'], '(1+floor(log_base(N)))^2')
        self.assert_prefixes(model, answer)
        self.assertFalse(answer['whole_signed_bound_proved'])

    def test_fractional_one_third_bound_pays_every_phase(self):
        model, cert = fractional(3)
        answer = C.verify(model, cert, METER)
        self.assertEqual(answer['phase_costs'], ['1', '4', '4'])
        self.assertEqual(answer['state_energy_bound'], '3')
        self.assertEqual(answer['squared_bound']['constant'], '1728')
        self.assert_prefixes(model, answer, 257)

    def test_fractional_one_sixth_bound_covers_nonaligned_prefixes(self):
        model, cert = fractional(6)
        answer = C.verify(model, cert, METER)
        self.assertEqual(answer['alpha'], '1/6')
        self.assertEqual(answer['phase_max'], '4')
        self.assert_prefixes(model, answer, 257)

    def test_general_base_and_nonscalar_seed_bound(self):
        model = make_model([[[1]], [[-1]], [[1]]], [F(3, 2)], [F(-2, 3)], 3)
        cert = certificate([[1, 0]], [[[1]], [[-1]], [[1]]], 0, [[1]], [[1]], [[7]], 3)
        answer = C.verify(model, cert, METER)
        self.assertEqual(answer['source_bound'], '1')
        self.assertEqual(answer['state_energy_bound'], '7')
        self.assertEqual(answer['phase_max'], '1/7')
        self.assertEqual(answer['squared_bound']['constant'], '4')
        self.assert_prefixes(model, answer, 100)

    def test_unit_impulse_cannot_be_erased(self):
        model = make_model([[[1]], [[0]]], [1], [1])
        cert = certificate([[1, 0]], [[[1]], [[0]]], 0, [[1]], [[1]], [[1]])
        answer = C.verify(model, cert, METER)
        self.assertEqual(value(model, 0), 1)
        self.assert_prefixes(model, answer)
        bad = copy.deepcopy(model)
        bad['matrices'][0][0][0] = '0'
        with self.assertRaisesRegex(ValueError, 'unit'):
            C.verify(bad, cert, METER)

    def test_reachable_subspace_accepts_true_latent_alias(self):
        model = make_model([[[1, 0], [0, 1]], [[1, 0], [0, -1]]], [1, 0], [1, 7])
        cert = certificate([[1, 0]], [[[1]], [[1]]], 1, [[1]], [[2]], [[1]])
        answer = C.verify(model, cert, METER)
        self.assertEqual(answer['reachable_dimension'], 1)
        self.assertEqual(answer['source_bound'], '8')
        # Full row equality fails on the unreachable second coordinate.
        self.assertTrue(C.verify_closure(model, cert['states'], cert['transitions'], METER)['valid'])

    def test_actual_counterexample_has_correct_index_values(self):
        model, cert = alternating()
        cert['transitions'][1][0] = ['0', '1']
        answer = C.verify_closure(model, cert['states'], cert['transitions'], METER)
        self.assertFalse(answer['valid'])
        witness = answer['counterexample']
        a, c = cert['states'][witness['state']]
        left = value(model, a * (2 * witness['n'] + witness['residue']) + c)
        right = sum((F(t) * value(model, b * witness['n'] + d)
                     for t, (b, d) in zip(cert['transitions'][witness['residue']][witness['state']],
                                         cert['states'])), F(0))
        self.assertEqual((str(left), str(right)), (witness['left'], witness['right']))
        self.assertNotEqual(left, right)
        with self.assertRaisesRegex(ValueError, 'false global'):
            C.verify(model, cert, METER)

    def test_long_transient_fit_is_not_global_closure(self):
        d = 24
        shift = [[F(int(j == i + 1)) for j in range(d)] for i in range(d)]
        model = make_model([identity(d), shift], [1] * d, [1] + [0] * (d - 1))
        transitions = [[['1']], [['1']]]
        self.assertTrue(all(value(model, n) == 1 for n in range(1024)))
        answer = C.verify_closure(model, [[1, 0]], transitions, METER)
        self.assertFalse(answer['valid'])
        witness = answer['counterexample']
        self.assertGreater(witness['n'], 1024)
        self.assertNotEqual(value(model, 2 * witness['n'] + witness['residue']),
                            value(model, witness['n']))

    def test_projection_recovery_and_commutation_are_mandatory(self):
        model, cert = alternating()
        for field, replacement in [('projection', [['0', '1']]),
                                   ('projection', [['2', '0']]),
                                   ('block_transition', [['2']])]:
            bad = copy.deepcopy(cert)
            bad['bound'][field] = replacement
            with self.subTest(field=field, replacement=replacement), self.assertRaises(ValueError):
                C.verify(model, bad, METER)

    def test_endpoint_only_cancellation_does_not_bound_auxiliary_growth(self):
        model, cert = alternating()
        cert['bound'] = dict(alpha='0', projection=encode(identity(2)),
                             block_transition=[['0', '0'], ['0', '2']], Q=encode(identity(2)))
        # Target block endpoints cancel, but a full metric falsely controls the
        # constant companion. The quotient in the valid certificate is essential.
        with self.assertRaisesRegex(ValueError, 'PSD'):
            C.verify(model, cert, METER)

    def test_metric_must_be_strictly_positive_and_symmetric(self):
        model, cert = fractional(3)
        for matrix in [[['0', '0', '0']] * 3,
                       [['1', '0', '0'], ['0', '1', '0'], ['0', '0', '0']],
                       [['1', '1', '0'], ['0', '1', '0'], ['0', '0', '1']]]:
            bad = copy.deepcopy(cert)
            bad['bound']['Q'] = matrix
            with self.subTest(matrix=matrix), self.assertRaises(ValueError):
                C.verify(model, bad, METER)

    def test_zero_psd_pivot_cannot_hide_cross_terms(self):
        model = make_model([[[1]], [[1]]], [1], [1])
        transitions = [[[1, 0], [1, 0]], [[1, 0], [1, 0]]]
        cert = certificate([[1, 0], [2, 0]], transitions, 1, identity(2),
                           [[2, 0], [2, 0]], [[2, -1], [-1, 2]])
        with self.assertRaisesRegex(ValueError, 'zero PSD pivot'):
            C.verify(model, cert, METER)

    def test_complete_quadratic_cross_cost_is_paid(self):
        model = make_model([[[1]], [[1]]], [1], [1])
        transitions = [[[1, 0], [1, 0]], [[1, 0], [1, 0]]]
        cert = certificate([[1, 0], [2, 0]], transitions, 1, identity(2),
                           [[2, 0], [2, 0]], [[2, -1], [-1, 1]])
        answer = C.verify(model, cert, METER)
        self.assertEqual(answer['state_energy_bound'], '5')
        self.assertEqual(answer['squared_bound']['constant'], '80')
        self.assert_prefixes(model, answer)

    def test_redundant_projection_rows_remain_sound(self):
        model = make_model([[[1]], [[1]]], [1], [1])
        transitions = [[[1, 0], [1, 0]], [[1, 0], [1, 0]]]
        cert = certificate([[1, 0], [2, 0]], transitions, 1,
                           [[1, 0], [1, 0]], [[2, 0], [0, 2]], identity(2))
        answer = C.verify(model, cert, METER)
        self.assertEqual(answer['state_energy_bound'], '2')
        self.assert_prefixes(model, answer)

    def test_row_envelope_and_complete_source_schema_are_required(self):
        model, cert = alternating()
        variants = []
        bad = copy.deepcopy(model)
        bad['matrices'][1][0] = ['2', '0']
        variants.append(bad)
        bad = copy.deepcopy(model)
        bad['matrices'].pop()
        variants.append(bad)
        bad = copy.deepcopy(model)
        bad.pop('initial')
        variants.append(bad)
        bad = copy.deepcopy(model)
        bad['initial'][0] = '1/1'
        variants.append(bad)
        bad = copy.deepcopy(model)
        bad['output'][0] = '1e999999999'
        variants.append(bad)
        for bad in variants:
            with self.subTest(bad=bad), self.assertRaises(ValueError):
                C.verify(bad, cert, METER)

    def test_state_domains_and_bound_parameters_fail_closed(self):
        model, cert = alternating()
        for states in [[[True, 0], [2, 0]], [[1, 0], [3, 0]],
                       [[1, 0], [2, 2]], [[1, 0], [1, 0]], [[1, 0], [512, 0]]]:
            bad = copy.deepcopy(cert)
            bad['states'] = states
            with self.subTest(states=states), self.assertRaises(ValueError):
                C.verify(model, bad, METER)
        for alpha in ['-1', '2', '1/25', '0/1']:
            bad = copy.deepcopy(cert)
            bad['bound']['alpha'] = alpha
            with self.subTest(alpha=alpha), self.assertRaises(ValueError):
                C.verify(model, bad, METER)
        bad = copy.deepcopy(cert)
        bad['base'] = 3
        with self.assertRaisesRegex(ValueError, 'base binding'):
            C.verify(model, bad, METER)

    def test_zero_source_closure_uses_zero_reachable_space(self):
        model = make_model([[[0]], [[0]]], [0], [1])
        cert = certificate([[1, 0]], [[[17]], [[-17]]], 0, [[1]], [[0]], [[1]])
        answer = C.verify(model, cert, METER)
        self.assertEqual(answer['reachable_dimension'], 0)
        self.assertEqual(answer['squared_bound']['constant'], '0')

    def test_core_numeric_identity_and_flags_never_supply_a_proof(self):
        answer = C.check_core_closure({'finite_fit': True, 'bound_proved': True}, meter=METER)
        self.assertEqual(answer['status'], 'unknown')
        for field in ['verified', 'valid', 'bound_proved', 'whole_signed_bound_proved', 'RH_proved']:
            self.assertFalse(answer[field])
        # The production meter has only charge/live; no number() is required.
        model, cert = alternating()
        self.assertTrue(C.verify(model, cert, METER)['verified'])


def tearDownModule():
    print('SYNTHETIC_WORK module=test_check_multiscale_bound_discovery '
          f'operations={METER.operations} elapsed_seconds={time.monotonic() - STARTED:.6f}')


if __name__ == '__main__':
    unittest.main()
