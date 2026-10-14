"""Tiny exact/formal calibrations; no actual pilot inputs or scores."""
from copy import deepcopy
from fractions import Fraction as Q
import time
import unittest
from unittest.mock import patch

import cancellation_arithmetic_language as LEGACY
import potential_candidate_language as P

_METERS = []
_ORIGINAL_METER = P.Meter


class TrackedMeter(_ORIGINAL_METER):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        _METERS.append(self)


def setUpModule():
    global _PATCH
    _PATCH = patch.object(P, 'Meter', TrackedMeter)
    _PATCH.start()


def tearDownModule():
    _PATCH.stop()
    print('SYNTHETIC_WORK module=test_potential_candidate_language operations=' +
          str(sum(m.operations for m in _METERS)))


def meter(**kwargs):
    return P.Meter(1000000, **kwargs)


def candidate(tree=None, weight='1'):
    return dict(states=[] if tree is None else [dict(weight=weight, tree=tree)])


def formal(candidate_value, X, values, shared):
    class MeteredCompiler(LEGACY.Compiler):
        def charge(self, count=1):
            shared.charge(count)
            super().charge(count)
    compiler = MeteredCompiler(X, len(values) - 1, max_operations=shared.max_operations,
        max_degree=16, max_terms=10000, max_coefficient_bits=4096, max_integer_bits=4096)
    polynomial = compiler.compile(P.potential_tree(candidate_value))
    shared.charge(len(values) + sum(1 + len(monomial) for monomial in polynomial))
    return LEGACY.L.evaluate(polynomial, {n: value for n, value in enumerate(values) if n})


class CandidateLanguageTests(unittest.TestCase):
    def test_complete_divisor_inversion_and_declared_controls(self):
        m = meter(); mu = P.mobius(20, m)
        self.assertEqual(mu, [0, 1, -1, -1, 0, -1, 1, -1, 0, 0, 1,
                              -1, 0, -1, 1, 1, 0, -1, 0, -1, 0])
        for n in range(1, 21):
            m.charge(n)
            self.assertEqual(sum(mu[d] for d in range(1, n + 1) if n % d == 0), int(n == 1))
        self.assertEqual(P.control_source('one', mu, m), [0] + [1] * 20)
        partial = P.control_source('partial_prime_2', mu, m)
        self.assertEqual(partial[2], -1)
        self.assertEqual(partial[3], 1)
        self.assertEqual(partial[4], 0)
        copied = P.control_source('mu', mu, m); copied[1] = 0
        self.assertEqual(mu[1], 1)

    def test_baseline_keeps_complete_energy_and_signed_child_increment(self):
        m = meter(); evaluator = P.Evaluator(P.mobius(15, m), m)
        record = evaluator.case(candidate(), 2)
        self.assertEqual(record['parent'], dict(X=2, E='1/4', V='0', W='1/4'))
        self.assertEqual(record['child'], dict(X=4, E='5/8', V='0', W='5/8'))
        self.assertEqual(record['innovation'], '3/8')
        self.assertEqual(evaluator.measure(candidate(), 1), dict(X=1, E='1', V='0', W='1'))

    def test_prime_square_retains_signed_cross_terms(self):
        tree = ['sum', 'p', ['int', 2], ['v', 't'],
                ['guard', ['prime', ['v', 'p']], ['x', ['v', 'p']]]]
        value = candidate(tree); m = meter(); values = P.mobius(15, m)
        scalar = P.Evaluator(values, m).measure(value, 2)
        self.assertEqual(scalar['V'], '5/4')
        self.assertEqual(scalar['W'], '3/2')
        self.assertNotEqual(scalar['V'], '3/4')
        self.assertEqual(Q(scalar['V']), formal(value, 2, values, m))

    def test_formal_calibration_on_actual_and_unrelated_values(self):
        tree = ['sum', 'n', ['int', 1], ['v', 't'], ['guard',
            ['and', ['squarefree', ['v', 'n']], ['eq', ['gcd', ['v', 'n'], ['v', 'X']], ['int', 1]]],
            ['mul', ['x', ['v', 'n']], ['add', ['q', '-1/2'],
                                             ['ratio', ['v', 'n'], ['v', 't']]]]]]
        value = dict(states=[dict(weight='2/3', tree=tree),
                            dict(weight='1/4', tree=['mul', ['x', ['v', 't']], ['x', ['v', 't']]])])
        m = meter()
        for values in (P.mobius(15, m), [0] + [Q((n % 5) - 2, 3) for n in range(1, 16)]):
            evaluator = P.Evaluator(values, m)
            for X in (1, 2, 4):
                self.assertEqual(Q(evaluator.measure(value, X)['V']), formal(value, X, values, m))

    def test_child_rebinds_X_and_exact_fractional_roots(self):
        m = meter(); values = [0] + [1] * 31; evaluator = P.Evaluator(values, m)
        record = evaluator.case(candidate(['embed', ['v', 'X']]), 2)
        self.assertEqual(record['parent']['V'], '2')
        self.assertEqual(record['child']['V'], '4')
        for denominator in (2, 3, 6):
            value = candidate(['embed', ['root', ['v', 't'], 1, denominator]])
            self.assertEqual(Q(evaluator.measure(value, 4)['V']), formal(value, 4, values, m))
        self.assertEqual(evaluator.measure(candidate(['embed', ['root', ['int', 0], 0, 6]]), 2)['V'], '1/2')
        self.assertEqual(evaluator.measure(candidate(['embed', ['root', ['int', 0], 1, 6]]), 2)['V'], '0')

    def test_floor_division_residue_masks_and_signed_products(self):
        tree = ['add', ['embed', ['idiv', ['int', -3], ['int', 2]]],
            ['guard', ['not', ['eq', ['imod', ['v', 't'], ['int', 2]], ['int', 0]]],
             ['mul', ['x', ['v', 't']], ['scale', '-2', ['x', ['v', 't']]]]]]
        value = candidate(tree); m = meter(); values = [0] + [1] * 15
        self.assertEqual(P.Evaluator(values, m).measure(value, 2)['V'], '5')
        self.assertEqual(formal(value, 2, values, m), Q(5))

    def test_short_circuit_guard_and_boolean_validation(self):
        m = meter(); evaluator = P.Evaluator([0, 1, -1, -1], m)
        bad_index = ['x', ['int', 0]]
        invalid_boolean = ['divides', ['idiv', ['int', 1], ['int', 0]], ['int', 1]]
        for predicate in (['and', ['eq', ['int', 0], ['int', 1]], invalid_boolean],
                          ['not', ['or', ['eq', ['int', 1], ['int', 1]], invalid_boolean]]):
            self.assertEqual(evaluator.measure(candidate(['guard', predicate, bad_index]), 1)['V'], '0')
        with self.assertRaises(ValueError):
            evaluator.measure(candidate(['guard', ['eq', ['int', 0], ['int', 0]], bad_index]), 1)
        with self.assertRaises(ValueError):
            P.validate_candidate(candidate(['guard', ['eq', ['int', 0], ['int', 1]], ['unknown']]), m)

    def test_sum_lower_endpoint_and_all_free_dependencies_bind_cache(self):
        m = meter(); values = [0] + [1] * 31; evaluator = P.Evaluator(values, m)
        tree = ['sum', 'n', ['int', 1], ['root', ['v', 't'], 1, 2],
                ['mul', ['embed', ['v', 'X']], ['mul', ['embed', ['v', 't']], ['x', ['v', 'n']]]]]
        value = candidate(tree)
        self.assertEqual(evaluator.measure(value, 2)['V'], '13')
        self.assertEqual(evaluator.measure(value, 4)['V'], '504')
        self.assertEqual(Q(evaluator.measure(value, 4)['V']), formal(value, 4, values, m))
        moving = candidate(['sum', 'n', ['v', 't'], ['v', 't'], ['x', ['v', 'n']]])
        source = [0] + list(range(1, 16)); fresh = P.Evaluator(source, m)
        self.assertEqual(fresh.measure(moving, 2)['V'], '13/4')
        self.assertEqual(Q(fresh.measure(moving, 2)['V']), formal(moving, 2, source, m))

    def test_bounded_sum_never_precomputes_unrequested_invalid_terms(self):
        m = meter(); evaluator = P.Evaluator([0, 1, 2, 3], m)
        value = candidate(['sum', 'n', ['int', 1], ['v', 'X'],
                           ['x', ['iadd', ['v', 'n'], ['int', 2]]]])
        self.assertEqual(evaluator.measure(value, 1)['V'], '9')
        before = m.operations
        with self.assertRaises(ValueError):
            evaluator.measure(value, 2)
        self.assertGreater(m.operations, before)
        empty = candidate(['sum', 'n', ['int', 1], ['int', 0], ['x', ['int', 0]]])
        self.assertEqual(evaluator.measure(empty, 1)['V'], '0')

    def test_memoization_preserves_full_payload_and_source_immutability(self):
        m = meter(); values = [0] + [1] * 31; before = list(values)
        value = candidate(['sum', 'n', ['int', 1], ['v', 't'], ['x', ['v', 'n']]])
        evaluator = P.Evaluator(values, m); start = m.operations
        first = evaluator.measure(value, 8); first_cost = m.operations - start
        start = m.operations; repeated = evaluator.measure(value, 8)
        self.assertEqual(first, repeated)
        self.assertLess(m.operations - start, first_cost)
        value['states'][0]['weight'] = '2'
        self.assertEqual(Q(evaluator.measure(value, 8)['V']), 2 * Q(first['V']))
        self.assertEqual(values, before)

    def test_full_strict_syntax_schema_and_nonnegative_weights(self):
        m = meter()
        for value in (candidate(['q', '1'], '-1'), candidate(['q', '01']), candidate(['embed', ['v', 'N']]),
                      candidate(['sum', 't', ['int', 1], ['int', 2], ['q', '1']]),
                      candidate(['x', ['q', '1']]), dict(states=[], extra=0),
                      dict(states=[dict(weight='1', tree=['q', '1'])] * 3)):
            with self.assertRaises(ValueError):
                P.validate_candidate(value, m)
        deep = ['q', '1']
        for _ in range(25):
            deep = ['scale', '1', deep]
        with self.assertRaises(OverflowError):
            P.validate_candidate(candidate(deep), m)

    def test_resource_caps_are_shared_and_no_partial_case_is_returned(self):
        tiny = P.Meter(10)
        with self.assertRaises(OverflowError):
            P.mobius(10, tiny)
        self.assertGreater(tiny.operations, 0)
        expired = P.Meter(100, deadline=time.monotonic() - 1)
        with self.assertRaises(TimeoutError):
            expired.charge(7)
        self.assertEqual(expired.operations, 7)
        bits = P.Meter(1000, max_bits=8)
        bounded = P.Evaluator([0, 1], bits)
        with self.assertRaises(OverflowError):
            bounded.measure(candidate(['embed', ['root', ['int', 2], 128, 1]]), 1)
        cells = P.Meter(1000, max_cells=4)
        with self.assertRaises(OverflowError):
            P.Evaluator([0, 1], cells)
        m = meter(); evaluator = P.Evaluator([0, 1, -1, -1], m)
        with self.assertRaises(ValueError):
            evaluator.case(candidate(), 2)
        before = m.operations
        with self.assertRaises(ValueError):
            evaluator.measure(candidate(['ratio', ['int', 1], ['int', 0]]), 1)
        self.assertGreater(m.operations, before)

    def test_direct_legacy_compiler_paths_never_generate_hashes(self):
        m = meter(); values = P.mobius(7, m); value = candidate(['x', ['v', 't']])
        original = deepcopy(value)
        with patch('hashlib.sha256', side_effect=AssertionError('no hashes')), \
             patch.object(LEGACY, 'digest', side_effect=AssertionError('no digest wrapper')):
            scalar = P.Evaluator(values, m).measure(value, 2)
            self.assertEqual(Q(scalar['V']), formal(value, 2, values, m))
        self.assertEqual(value, original)


if __name__ == '__main__':
    unittest.main()
