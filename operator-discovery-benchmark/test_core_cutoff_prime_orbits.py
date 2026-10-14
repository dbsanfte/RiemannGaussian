"""Root-owned tests: complete work, partial orbits, and proof-scope guards."""
import copy
import json
from pathlib import Path
import unittest

from flint import arb, acb, ctx
import core_cutoff_prime_orbits as P
from prime_bank_candidates import Meter

METER = Meter(100000000, 300)
ROOT = Path(__file__).resolve().parent


def tiny_mu(N):
    values = [0]+[1]*N
    for n in range(2, N+1):
        values[n] = -sum(values[d] for d in range(1, n) if n % d == 0)
    return values


def artificial(B, works):
    mu = tiny_mu(2*B)
    return dict(start=B+1, end=2*B, heights=P.HEIGHTS, mu=mu, records=[
        dict(q=q, mu=mu[q], values=[dict(w1='0', w2=str(works.get(q, 0)))]+[
            dict(w1='0', w2='0') for _ in P.HEIGHTS[1:]]) for q in range(B+1, 2*B+1)])


class Arithmetic(unittest.TestCase):
    def setUp(self):
        ctx.prec = 192

    def test_inverse_equations_reject_wrong_prime_or_square(self):
        mu = tiny_mu(16)
        P.validate_mu(mu, METER)
        for q in (1, 7, 9):
            bad = mu[:]; bad[q] = 1 if mu[q] != 1 else -1
            with self.assertRaises(ValueError): P.validate_mu(bad, METER)

    def test_complete_ternary_energy_crosses(self):
        A, E, c, D, z, a, b = acb(1, 2), acb(2, -1), arb(1), acb(3, 1), acb(1, -2), arb(1)/2, acb(1, 1)
        zero, odd, even, children = P.work_sectors(A, E, c, D, z, a, b)
        old = A**2*E**3-c**3*D
        for x in (-1, 0, 1):
            self.assertTrue((P.norm(children[x])-P.norm(old)-zero-x*odd-x*x*even).contains(0))
        self.assertFalse(zero.contains(0))

    def test_first_shell_zero_mu_head_and_continuation(self):
        mu = tiny_mu(8)
        initial = P.measure(mu[:5], 2, 4, None, METER)
        first = initial['records'][0]
        self.assertEqual(first['mask_old'], [True, True, True, False, False, False, False])
        self.assertEqual(first['mask_new'], [True]*7)
        self.assertTrue(all(arb(v['shell']) > 0 for v in first['values'][3:]))
        self.assertEqual(initial['records'][-1]['mu'], 0)
        self.assertTrue(any(not arb(v['zero']).contains(0) for v in initial['records'][-1]['values']))
        continuation = P.measure(mu, 5, 8, initial['state'], METER)
        self.assertTrue(all(arb(a).overlaps(arb(b)) for a, b in
            zip(continuation['initial_energy'], initial['state']['last_energy'])))
        self.assertEqual([r['q'] for r in continuation['records']], [5, 6, 7, 8])
        bad = copy.deepcopy(initial['state']); bad['q'] = 2
        with self.assertRaises(ValueError): P.measure(mu, 5, 8, bad, METER)


class Orbits(unittest.TestCase):
    def setUp(self):
        ctx.prec = 192

    def test_exact_fractional_cutoffs_and_catalogue(self):
        self.assertEqual(len(P.program_catalogue()), 18)
        for B in (2, 63, 64, 65, 729):
            for exponent in P.EXPONENTS:
                k = P.floor_power(B, exponent); e = P.Q(exponent)
                self.assertLessEqual(k**e.denominator, B**e.numerator)
                self.assertGreater((k+1)**e.denominator, B**e.numerator)

    def test_partial_peak_keeps_an_unmatched_face(self):
        # In (4,8], primes {2,3} place 6 alone. In (8,16], 10 and 15
        # share cofactor 5; the first partial sum must survive endpoint cancellation.
        program = next(p for p in P.program_catalogue() if p.get('lower') == '0' and p.get('upper') == '2/3')
        data = artificial(8, {10: 7, 15: -7})
        case = P.group_case(program, 8, data, METER)
        self.assertEqual(case['primes'], [2, 3])
        self.assertEqual(arb(case['grouped_endpoint_absolute']), 0)
        self.assertEqual(arb(case['grouped_peak_absolute']), 7)
        self.assertEqual(arb(case['ungrouped_absolute']), 14)
        self.assertEqual(case['cancellation_bits'], 1)
        self.assertEqual(len(case['partial_curve']), 8)

    def test_zero_events_and_single_prime_degeneracy(self):
        data = artificial(16, {q: 1 for q in range(17, 33)})
        for program in P.program_catalogue()[:3]:
            case = P.group_case(program, 16, data, METER)
            self.assertFalse(case['nontrivial_partition'])
            self.assertTrue(all(count == 1 for _, count in case['group_sizes']))
            self.assertEqual(sum(c for _, c in case['group_sizes'])+case['zero_events'], 16)
            self.assertEqual(arb(case['grouped_peak_absolute']), arb(case['ungrouped_absolute']))

    def test_selection_needs_all_prefixes_and_ignores_evaluation(self):
        programs = P.program_catalogue()
        cases = [dict(program_id=p['id'], B=B, cancellation_bits=p['id'] % 3,
                      nontrivial_partition=p['id'] >= 3) for p in programs for B in P.DISCOVERY]
        result = P.select(programs, cases)
        self.assertEqual([x['program_id'] for x in result['selected']], [5, 8])
        self.assertEqual(result, P.select(programs, cases+[
            dict(program_id=p['id'], B=1024, cancellation_bits=20, nontrivial_partition=True) for p in programs]))
        damaged = [c for c in cases if (c['program_id'], c['B']) != (5, 512)]
        self.assertEqual(P.select(programs, damaged)['selected'][0]['program_id'], 4)


class Scope(unittest.TestCase):
    def test_binding_and_full_source_preservation(self):
        parent = json.loads((ROOT/'candidate10_cutoff_work_obligation.json').read_text())
        binding = P.bind_target(parent, METER)
        selected = dict(selected=[dict(lane='prefix', program_id=5, minimum_cancellation_bits=0)])
        out = P.feedback(parent, binding, selected, [], 'test-only.json')
        for key in ('selected_source_representation', 'generated_bound_obligations', 'complete_source_reduction',
                    'retained_original_proof_frontier', 'cutoff_work_targets', 'inherited_proof_dependencies'):
            self.assertEqual(out[key], parent[key])
        self.assertEqual(out['next_search_tasks'][0], parent['next_search_tasks'][0])
        self.assertEqual(out['next_search_tasks'][-1], parent['next_search_tasks'][-1])
        self.assertFalse(out['whole_signed_bound_proved'])
        self.assertFalse(out['prime_orbit_search']['continuous_integral_control'])
        self.assertIn('every integer V', out['next_search_tasks'][1]['quantifier'])
        bad = copy.deepcopy(parent); bad['cutoff_work_targets'][0]['sigma'] = '1/2'
        with self.assertRaises(ValueError): P.bind_target(bad, METER)


def tearDownModule():
    print('operations='+str(METER.operations))
