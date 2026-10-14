"""Synthetic source algebra and metadata-only transition coverage tests."""
from copy import deepcopy
from fractions import Fraction as Q
import json
from pathlib import Path
import time
import unittest

import floor_residual_transition_search_050 as S

COUNTS = []


def recipe(theta='7/13'):
    return dict(id='synthetic_transition', auxiliary=None,
        base=dict(kind='drift_mixture', a='2/3', theta=theta,
                  terms=[dict(rate='1/2', weight='3/2'), dict(rate='3/2', weight='-1/2')]))


def request(p=3, N=7, d='5/7'):
    return dict(source_recipe=recipe(), prime=p, parent_support=N, d=d, rounding=deepcopy(S.ROUNDING))


def mu(n):
    count = 0
    for p in range(2, n+1):
        if n % p == 0:
            n //= p; count += 1
            if n % p == 0:
                return 0
    return (-1)**count


def cell(program, k):
    return (Q(program['constant'])-
        sum(Q(r['value'])*(Q(k, r['n'])-k//r['n']) for r in program['coefficients'])-
        sum(Q(r['value'])*int(k >= r['q']) for r in program['steps']))


class TransitionSearchTests(unittest.TestCase):
    def test_state_direct_definition_on_head_and_tail_cells(self):
        compiler = S.StateCompiler()
        req = request()
        cert = compiler.compile(req)
        U, V = list(map(Q, cert['parent_values'])), list(map(Q, cert['child_values']))
        p, N, d = req['prime'], req['parent_support'], Q(req['d'])
        for k in list(range(1, 253))+[1000, 10000, 1000001]:
            f = lambda n, j: Q(j, n)-j//n
            e_child = 1+sum(mu(n)*V[n-1]*f(n, k) for n in range(2, p*N+1))
            D_parent = int(k >= p)+sum(mu(n)*U[n-1]*(f(p*n, k)-f(p, k)/n) for n in range(2, N+1))
            A = ((1-V[p-1])*int(k >= p)+sum(mu(n)*(U[n-1]-V[p*n-1])*
                (f(p*n, k)-f(p, k)/n) for n in range(2, N+1)))
            self.assertEqual(cell(cert['programs']['h'], k), e_child+D_parent)
            self.assertEqual(cell(cert['programs']['A'], k), A)
            self.assertEqual(cell(cert['programs']['v'], k), e_child+D_parent-d*A)
        self.assertEqual(U[0], 1); self.assertEqual(V[0], 1)
        self.assertFalse(cert['uniform_bound_proved']); self.assertFalse(cert['rh_claim'])
        COUNTS.append(compiler.meter.operations+compiler.drift_meter.operations)

    def test_drift_profile_cache_reuses_atoms_without_aliasing_d(self):
        compiler = S.StateCompiler()
        first = compiler.compile(request())
        after = compiler.drift_meter.operations
        second = compiler.compile(request(d='-2/5'))
        self.assertEqual(compiler.drift_meter.operations, after)
        self.assertEqual(first['programs']['h'], second['programs']['h'])
        self.assertEqual(first['programs']['A'], second['programs']['A'])
        self.assertNotEqual(first['programs']['v'], second['programs']['v'])
        COUNTS.append(compiler.meter.operations+compiler.drift_meter.operations)

    def test_transitions_cover_level_and_rounding_preimages_both_parities(self):
        spec = recipe('8/17')['base']
        result = S.transition_cases(spec, 3, minimum=4, maximum_index=300, neighborhood=1)
        cases = {(r['N'], r['r']): r for r in result['cases']}
        for N in range(result['minimum']+1, result['maximum']+1):
            for r in (0, 1):
                maps = [(1, 0), (3, 0), (2, r), (6, 3*r)]
                if any(((a*N+b).bit_length(), (a*N+b-1).bit_length()) !=
                       ((a*(N-1)+b).bit_length(), (a*(N-1)+b-1).bit_length()) for a, b in maps):
                    self.assertIn((N, r), cases)
        self.assertFalse(result['scores_used']); self.assertFalse(result['actual_source_arrays_evaluated'])
        self.assertEqual(len(cases), len(result['cases']))
        for row in result['cases']:
            self.assertLessEqual(3*row['child'], 300)
            self.assertEqual(row['child'], 2*row['N']+row['r'])
        COUNTS.append(result['metadata_counts']['operations'])

    def test_arbitrary_rational_theta_and_exact_ceiling_classification(self):
        result = S.transition_cases(recipe('11/19')['base'], 5, minimum=4, maximum_index=500)
        self.assertTrue(result['cases'])
        for row in result['cases']:
            for event in row['events']:
                for v in (event['before'], event['after']):
                    z, L = int(v['ceiling']), v['level']
                    # a=2/3, theta=11/19, no floating root.
                    self.assertLess((z-1)**19*3**19, 2**19*L**11)
                    self.assertGreaterEqual(z**19*3**19, 2**19*L**11)
                self.assertEqual(event['ceiling_increases'],
                    int(event['after']['ceiling']) > int(event['before']['ceiling']))
        COUNTS.append(result['metadata_counts']['operations'])

    def test_strict_source_inputs_and_resource_scope(self):
        for key, value in [('prime', 4), ('prime', True), ('parent_support', 1),
                           ('parent_support', 1667), ('d', '2/4')]:
            bad = request(); bad[key] = value
            with self.assertRaises((ValueError, OverflowError)):
                S.validate_request(bad)
        bad = request(); bad['rounding']['bits_multiplier'] = True
        with self.assertRaises(ValueError): S.validate_request(bad)
        bad = request(); bad['source_recipe']['auxiliary'] = {}
        with self.assertRaises(ValueError): S.validate_request(bad)
        with self.assertRaises(ValueError): S.transition_cases(recipe()['base'], 3, maximum_index=5001)


if __name__ == '__main__':
    path = Path(__file__).with_name('floor_residual_transition_search_050_development.json')
    if path.exists(): raise SystemExit('preserve focused development receipt')
    start = time.monotonic()
    result = unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(TransitionSearchTests))
    receipt = dict(schema='floor-transition-search-development-v1', invocations=[dict(
        returncode=0 if result.wasSuccessful() else 1, tests=result.testsRun,
        failures=len(result.failures), errors=len(result.errors), operations=sum(COUNTS),
        elapsed_seconds=time.monotonic()-start)],
        scope='synthetic direct cells, exact rational exponents, metadata transition coverage; no actual candidate arrays or norms')
    path.write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps(receipt), flush=True)
    raise SystemExit(0 if result.wasSuccessful() else 1)
