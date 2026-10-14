"""Fresh tiny-source and adversarial 068 audits, with append-only receipts.

Fixtures use trial division, direct source inversion, and scalar floor sums.
No producer, optimizer, historical checker suite, or scientific record is run.
"""
import copy
from fractions import Fraction as Q
import json
from math import isqrt
from pathlib import Path
import resource
import time
import unittest
from unittest import mock
import check_mobius_floor_control_068 as C


class ChargeOnly:
    def __init__(self):
        self.operations = 0

    def charge(self, n=1):
        self.operations += n


METER = ChargeOnly()


def context():
    return C._Context(METER)


def trial_mu(n):
    answer, divisor = 1, 2
    while divisor*divisor <= n:
        if n % divisor == 0:
            n //= divisor
            answer = -answer
            if n % divisor == 0:
                return 0
        divisor += 1
    return -answer if n > 1 else answer


def W(N, base, d):
    return 4*N//(base*d)-3*(2*N//(base*d))+2*(N//(base*d))


def fixture(N=12, y=3, max_j=5, p=2, q=3, exponents=None, limit=512):
    """Build proposals without optimization, using scalar independent arithmetic."""
    D = 4*N//p
    exponents = ['0', '1/2', '1/257', '1'] if exponents is None else exponents
    depths = [max(v for v in range(1, N+1)
                  if v**Q(e).denominator <= N**Q(e).numerator) for e in exponents]
    cert = dict(schema=C.SCHEMA, N=N, y=y, max_j=max_j,
        parameters=dict(primes=[p, q], p=p, q=q, alpha='1/2', gamma='1/3', tau='1/4'),
        exponent_requests=exponents, horizon_limit=limit, coefficient_grid=C.GRID,
        endpoints=[], learner_mobius_signs_accessed=False,
        uniform_head_bound_proved=False, RH_proved=False)
    for ratio in (Q(p, q), Q(1)):
        den = ratio.denominator
        full = [0]+[int(den*(W(N, p, d)-ratio*W(N, q, d))) for d in range(1, D+1)]+[0]
        g = [0]+[-full[d] if d > y else 0 for d in range(1, D+1)]+[0]
        endpoint = dict(ratio=str(ratio), denominator=den, rows=[])
        for j in range(1, max_j+1):
            k = [0]+[g[j*n]-(g[(j+1)*n] if (j+1)*n <= D else 0)
                     for n in range(1, D//j+1)]
            direct = sum(trial_mu(n)*(full[j*n]-(full[(j+1)*n] if (j+1)*n <= D else 0))
                         for n in range(1, D//j+1))
            anchors = [n for n in range(D//j, 0, -1)
                       if k[n] != (k[n+1] if n < D//j else 0)]
            row = dict(j=j, direct_scaled=direct, unit_kernel_scaled=k[1],
                       anchors=anchors, models=[], plans=[], selected_model=0)
            realized = []
            for exponent, depth in zip([None]+exponents, [0]+depths):
                ordered = []
                # Fully scalar enumeration, independent of quotient blocks.
                for divisor in range(1, depth+1):
                    for A in anchors:
                        X = A//divisor
                        if X >= 2 and X not in ordered:
                            ordered.append(X)
                full_horizons = sorted(ordered)
                truncated = len(full_horizons) > limit
                if not truncated:
                    horizons = full_horizons
                elif limit == 1:
                    horizons = [max(full_horizons)]
                else:
                    # Integer rank grid, checked below against hand fixtures.
                    horizons = [full_horizons[index*(len(full_horizons)-1)//(limit-1)]
                                for index in range(limit)]
                complete_set = {A//divisor for A in anchors for divisor in range(1, A+1)
                                if A//divisor >= 2}
                if horizons not in realized:
                    realized.append(horizons)
                    sf_ns = [n for n in range(2, len(k)) if trial_mu(n)]
                    box = 4*den*max(1, len(horizons))
                    x = [(-1 if i % 2 else 1)*C.GRID//4 for i in range(len(horizons))]
                    eps = C.GRID*((direct+k[1] > 0)-(direct+k[1] < 0))
                    z = [C.GRID*((k[n] > 0)-(k[n] < 0)) for n in sf_ns]
                    center = C.GRID*(direct+k[1])+sum(v*(1-X) for X, v in zip(horizons, x))
                    residual = sum(abs(C.GRID*k[n]-sum(v*(X//n) for X, v in zip(horizons, x)))
                                   for n in sf_ns)
                    penalty = sum(abs(eps*(1-X)-sum(zn*(X//n) for n, zn in zip(sf_ns, z)))
                                  for X in horizons)
                    bound = Q(abs(center)+residual, den*C.GRID)
                    lower = Q(eps*(direct+k[1])+sum(zn*k[n] for n, zn in zip(sf_ns, z))
                              -box*penalty, den*C.GRID)
                    row['models'].append(dict(horizons=horizons, coefficient_box=box,
                        primal_numerators=x, dual_constant_numerator=eps, dual_weight_numerators=z,
                        center_numerator=center, residual_l1_numerator=residual,
                        dual_defect_l1_numerator=penalty, bound=str(bound),
                        box_optimum_lower=str(lower), box_gap=str(bound-lower),
                        solver=dict(status='optimal_float_proposal' if horizons else 'empty_dictionary_exact',
                                    iterations=1 if horizons else 0, message='tiny fixture' if horizons else '')))
                row['plans'].append(dict(exponent=exponent, depth=depth,
                    model_index=realized.index(horizons), dictionary_truncated=truncated,
                    complete_endpoint_quotients=complete_set <= set(horizons)))
            row['selected_model'] = min(range(len(row['models'])), key=lambda i: (
                Q(row['models'][i]['bound']), sum(v != 0 for v in row['models'][i]['primal_numerators']),
                len(row['models'][i]['horizons']), i))
            endpoint['rows'].append(row)
        cert['endpoints'].append(endpoint)
    return cert


def accept(cert):
    return C.verify_control(cert, METER)


class Tests(unittest.TestCase):
    def reject(self, cert):
        with self.assertRaises((ValueError, OverflowError, MemoryError)):
            accept(cert)

    def test_complete_certificate_and_exact_actual_head(self):
        cert = fixture()
        verdict = accept(cert)
        self.assertTrue(verdict['verified'])
        self.assertTrue(verdict['quotient_block_primal_replay'])
        self.assertTrue(verdict['exact_boxed_dual_replay'])
        self.assertFalse(verdict['uniform_N_growth_proved'])
        self.assertFalse(verdict['original_source_binding_proved'])
        for endpoint in verdict['endpoints']:
            ratio = Q(endpoint['ratio'])
            f = lambda d: Q(W(12, 2, d))-ratio*W(12, 3, d) if d <= 3 else Q(0)
            expected = [sum((trial_mu(n)*(f(j*n)-f((j+1)*n)) for n in range(1, 24//j+1)), Q(0))
                        for j in range(1, 6)]
            self.assertEqual([Q(row['actual_coefficient']) for row in endpoint['rows']], expected)
            self.assertEqual(Q(endpoint['actual_head_variation']), sum(map(abs, expected), Q(0)))

    def test_exhaustive_tiny_sources_prefixes_and_prime_pairs(self):
        for N in range(2, 9):
            for p, q in ((2, 3), (3, 5)):
                D = 4*N//p
                for y in range(1, D+1):
                    accept(fixture(N=N, y=y, max_j=min(D, 4), p=p, q=q))

    def test_zero_rows_full_prefix_and_dictionary_reuse(self):
        accept(fixture(max_j=0))
        cert = fixture(y=24)
        accept(cert)
        self.assertTrue(all(len(row['models']) == 1 for ep in cert['endpoints'] for row in ep['rows']))
        cert = fixture(exponents=['0', '1/257', '1/1025'])
        accept(cert)
        row = cert['endpoints'][0]['rows'][0]
        self.assertEqual(len(row['models']), 2)
        row['plans'][-1]['model_index'] = 0
        self.reject(cert)

    def test_deterministic_clipping_and_complete_span_flags(self):
        cert = fixture(limit=1)
        accept(cert)
        self.assertTrue(any(p['dictionary_truncated'] for ep in cert['endpoints'] for row in ep['rows'] for p in row['plans']))
        for field in ('dictionary_truncated', 'complete_endpoint_quotients'):
            bad = copy.deepcopy(cert)
            bad['endpoints'][0]['rows'][0]['plans'][-1][field] = not bad['endpoints'][0]['rows'][0]['plans'][-1][field]
            self.reject(bad)
        bad = fixture(); bad['endpoints'][0]['rows'][0]['plans'][0]['exponent'] = '0'; self.reject(bad)

    def test_capped_quotient_union_depth_and_rank_boundaries(self):
        self.assertEqual(C._dictionary([100], 0, 2, context()), ([], False, False))
        self.assertEqual(C._dictionary([100], 1, 2, context()), ([100], False, False))
        self.assertEqual(C._dictionary([100], 2, 2, context()), ([50, 100], False, False))
        self.assertEqual(C._dictionary([100], 3, 2, context()), ([33, 100], True, False))
        self.assertEqual(C._dictionary([100], 5, 2, context()), ([20, 100], True, False))
        self.assertEqual(C._dictionary([100], 5, 1, context()), ([100], True, False))
        self.assertEqual(C._dictionary([9, 6, 1], 2, 512, context()), ([3, 4, 6, 9], False, False))
        self.assertEqual(C._dictionary([9, 6, 1], 4, 512, context()), ([2, 3, 4, 6, 9], False, True))
        self.assertEqual(C._dictionary([9, 6, 1], 4, 3, context()), ([2, 4, 9], True, False))
        cert = fixture(N=150, y=160, max_j=1, p=3, q=5, limit=2,
                       exponents=['0', '1/3', '1'])
        accept(cert)
        self.assertTrue(any(row['plans'][2]['model_index'] != row['plans'][3]['model_index']
                            for ep in cert['endpoints'] for row in ep['rows']))

    def test_mutate_every_exact_cost_and_raw_source_field(self):
        base = fixture()
        for field in ('direct_scaled', 'unit_kernel_scaled', 'j'):
            cert = copy.deepcopy(base); cert['endpoints'][0]['rows'][0][field] += 1; self.reject(cert)
        for field in ('coefficient_box', 'center_numerator', 'residual_l1_numerator',
                      'dual_defect_l1_numerator'):
            cert = copy.deepcopy(base); cert['endpoints'][0]['rows'][0]['models'][1][field] += 1; self.reject(cert)
        for field in ('bound', 'box_optimum_lower', 'box_gap'):
            cert = copy.deepcopy(base)
            model = cert['endpoints'][0]['rows'][0]['models'][1]
            model[field] = str(Q(model[field])+Q(1, C.GRID))
            self.reject(cert)

    def test_mutate_every_primal_and_dual_coordinate(self):
        base = fixture()
        model = base['endpoints'][0]['rows'][0]['models'][1]
        for field in ('primal_numerators', 'dual_weight_numerators'):
            for index in range(len(model[field])):
                cert = copy.deepcopy(base)
                cert['endpoints'][0]['rows'][0]['models'][1][field][index] += 1
                self.reject(cert)
        cert = copy.deepcopy(base)
        cert['endpoints'][0]['rows'][0]['models'][1]['dual_constant_numerator'] += 1
        self.reject(cert)

    def test_coordinate_masks_boundaries_and_box_mutations(self):
        for field in ('primal_numerators', 'dual_weight_numerators'):
            for action in ('pop', 'append'):
                cert = fixture(); vector = cert['endpoints'][0]['rows'][0]['models'][1][field]
                vector.pop() if action == 'pop' else vector.append(0)
                self.reject(cert)
        cert = fixture(); model = cert['endpoints'][0]['rows'][0]['models'][1]
        model['primal_numerators'][0] = model['coefficient_box']*C.GRID+1; self.reject(cert)
        cert = fixture(); cert['endpoints'][0]['rows'][0]['models'][1]['dual_weight_numerators'][0] = -C.GRID-1; self.reject(cert)

    def test_grammar_anchor_order_horizon_order_and_plan_depth(self):
        for field in ('anchors',):
            cert = fixture(); cert['endpoints'][0]['rows'][0][field].reverse(); self.reject(cert)
        for action in ('reverse', 'pop', 'append'):
            cert = fixture(); horizons = cert['endpoints'][0]['rows'][0]['models'][-1]['horizons']
            horizons.append(1) if action == 'append' else getattr(horizons, action)()
            self.reject(cert)
        for field in ('depth', 'model_index'):
            cert = fixture(); cert['endpoints'][0]['rows'][0]['plans'][1][field] += 1; self.reject(cert)
        cert = fixture(); cert['endpoints'][0]['rows'][0]['plans'].reverse(); self.reject(cert)
        cert = fixture(); cert['endpoints'][0]['rows'][0]['models'].reverse(); self.reject(cert)

    def test_complete_rows_endpoints_selection_and_boolean_gates(self):
        for mutate in ('pop', 'reverse'):
            cert = fixture(); getattr(cert['endpoints'], mutate)(); self.reject(cert)
            cert = fixture(); getattr(cert['endpoints'][0]['rows'], mutate)(); self.reject(cert)
        cert = fixture(); cert['endpoints'][0]['rows'][0]['selected_model'] = 999; self.reject(cert)
        for field in ('learner_mobius_signs_accessed', 'uniform_head_bound_proved', 'RH_proved'):
            cert = fixture(); cert[field] = True; self.reject(cert)
            cert = fixture(); cert[field] = 0; self.reject(cert)
        cert = fixture(); cert['endpoints'][0]['rows'][0]['models'][1]['primal_numerators'][0] = True; self.reject(cert)

    def test_schema_source_parameters_and_resource_gates(self):
        for field, value in (('N', True), ('N', 65537), ('y', 0), ('y', 25),
                             ('max_j', -1), ('max_j', 4097), ('horizon_limit', 513),
                             ('coefficient_grid', 8), ('exponent_requests', []),
                             ('exponent_requests', ['1/2', '1/2']), ('schema', 'other')):
            cert = fixture(); cert[field] = value; self.reject(cert)
        for field, value in (('p', 3), ('q', 2), ('primes', [2, 4]), ('primes', [3, 2]),
                             ('alpha', '0'), ('gamma', '0'), ('tau', '1')):
            cert = fixture(); cert['parameters'][field] = value; self.reject(cert)
        for location in ('top', 'row', 'model', 'plan'):
            cert = fixture()
            target = cert if location == 'top' else cert['endpoints'][0]['rows'][0]
            if location == 'model': target = target['models'][1]
            if location == 'plan': target = target['plans'][1]
            target['assumed_uniform_bound'] = '0'; self.reject(cert)
        with self.assertRaises(OverflowError):
            C.verify_control(fixture(), C.Meter(cap=0))

    def test_noncanonical_certificate_rationals_and_finite_claims(self):
        for text in ('2/2', '0.5', ' 1', '1/0', '', str(1 << 4096)):
            cert = fixture(); cert['endpoints'][0]['ratio'] = text; self.reject(cert)
            cert = fixture(); cert['endpoints'][0]['rows'][0]['models'][1]['box_gap'] = text; self.reject(cert)
        for requests in (['-1'], ['2'], ['2/4'], ['1/100001']):
            cert = fixture(); cert['exponent_requests'] = requests; self.reject(cert)
        for flag in ('uniform_N_growth_proved', 'RH_evidence', 'prime_signs', 'source_repair', 'full_core_inverse'):
            cert = fixture(); cert[flag] = True; self.reject(cert)
        cert = fixture(); cert['endpoints'][0]['denominator'] = 6; self.reject(cert)
        cert = fixture(); cert['endpoints'][0]['rows'][0]['plans'][1]['dictionary_truncated'] = 0; self.reject(cert)
        cert = fixture(); cert['endpoints'][0]['rows'][0]['models'][1]['dual_constant_numerator'] = False; self.reject(cert)

    def test_solver_metadata_is_bounded_without_certifying_optimality(self):
        for field, value in (('status', 'proved_exact_optimum'), ('iterations', True),
                             ('iterations', -1), ('message', 'a'*10001)):
            cert = fixture(); cert['endpoints'][0]['rows'][0]['models'][1]['solver'][field] = value
            self.reject(cert)
        cert = fixture(); cert['endpoints'][0]['rows'][0]['models'][0]['solver']['iterations'] = 1
        self.reject(cert)
        # A failed proposal with a feasible rational replay remains a bound;
        # solver labels do not supply optimality or replace exact arithmetic.
        cert = fixture(); cert['endpoints'][0]['rows'][0]['models'][1]['solver']['status'] = 'failed_zero_fallback'
        accept(cert)

    def test_selection_ties_and_changed_scores_require_declared_selection(self):
        cert = fixture()
        row = cert['endpoints'][0]['rows'][0]
        self.assertGreater(len(row['models']), 1)
        row['selected_model'] = (row['selected_model']+1) % len(row['models'])
        self.reject(cert)
        # Duplicate realized dictionary models are forbidden, even if every
        # duplicated cost is internally consistent.
        cert = fixture()
        row = cert['endpoints'][0]['rows'][0]
        row['models'].append(copy.deepcopy(row['models'][-1]))
        self.reject(cert)

    def test_unsigned_squarefree_and_actual_mu_are_distinct_checks(self):
        c = context()
        mask, mu = C._squarefree(300, c), C._ordinary_mu(300, c)
        self.assertEqual(mask[1], 1)
        self.assertEqual(mu[1], 1)
        for n in range(1, 301):
            self.assertEqual(mu[n], trial_mu(n))
            self.assertEqual(mask[n], abs(trial_mu(n)))
        self.assertEqual([mask[n] for n in (4, 8, 9, 12, 18, 25, 27, 36)], [0]*8)

    def test_quotient_events_against_independent_scalar_floor(self):
        c = context()
        for length in (1, 2, 7, 29):
            horizons, values = [2, 3, 10, 31], [19, -7, 0, -13]
            expected = [0]+[sum(v*(X//n) for X, v in zip(horizons, values))
                            for n in range(1, length+1)]
            self.assertEqual(C._floor_events(horizons, values, length, c), expected)
        self.assertEqual(C._floor_events([], [], 5, c), [0]*6)

    def test_actual_joined_source_barrier_family(self):
        # The review's N=15t,y=16t family has two disjoint signed intervals.
        for t in range(1, 8):
            for ratio in (Q(3, 5), Q(1)):
                f, g, floors, steps = C._source(15*t, 16*t, 20*t, 3, 5, ratio, context())
                den = ratio.denominator
                self.assertEqual(steps, [16*t, 20*t])
                self.assertEqual(floors.get(1, 0), 0)
                k = [0]+[g[n]-(g[2*n] if 2*n <= 20*t else 0)
                         for n in range(1, 20*t+1)]
                expected = [0]+[den*(int(8*t < n <= 10*t)-int(16*t < n <= 20*t))
                                 for n in range(1, 20*t+1)]
                self.assertEqual(k, expected)
                for n in range(1, 20*t+1):
                    self.assertEqual(f[n], den*(W(15*t, 3, n)-ratio*W(15*t, 5, n))
                                     if n <= 16*t else 0)

    def test_full_source_direct_atoms_against_actual_inversion(self):
        for N in (2, 7, 15):
            for p, q in ((2, 3), (3, 5)):
                D = 4*N//p
                for ratio in (Q(p, q), Q(1)):
                    den = ratio.denominator
                    _, _, atoms, _ = C._source(N, 1, D, p, q, ratio, context())
                    full = lambda d: den*(W(N, p, d)-ratio*W(N, q, d)) if d <= D else 0
                    for j in range(1, D+1):
                        direct = sum(trial_mu(n)*(full(j*n)-full((j+1)*n))
                                     for n in range(1, D//j+1))
                        self.assertEqual(direct, atoms.get(j, 0))

    def test_boxed_dual_penalty_is_required_and_negative_is_valid(self):
        # A witness violating the unboxed equality constraints is still valid
        # when the finite box penalty is retained; here its lower value is -4.
        mask = C._squarefree(3, context())
        costs = C._boxed_costs([0, 0, 1, 0], 0, 1, [2], [0],
                              C.GRID, [0, 0], mask, context())
        self.assertEqual(costs['upper'], 1)
        self.assertEqual(costs['lower'], -4)
        self.assertEqual(costs['gap'], 5)
        # Fractional witness and rational primal must replay without tolerance.
        costs = C._boxed_costs([0, 2, -3, 5], -1, 5, [2, 3],
                              [C.GRID//2, -C.GRID//4], C.GRID//2,
                              [-C.GRID//4, C.GRID//8], mask, context())
        self.assertEqual(costs['center'], Q(1, 5))
        self.assertEqual(costs['upper'], Q(19, 10))
        self.assertLessEqual(costs['lower'], costs['upper'])

    def test_unit_squareful_and_clipped_coordinates_are_not_free(self):
        mask = C._squarefree(4, context())
        base = dict(k=[0, 7, 2, -3, 999], direct=-2, den=1,
                    horizons=[], x=[], eps=0, z=[0, 0], mask=mask, c=context())
        self.assertEqual(C._boxed_costs(**base)['upper'], 10)
        for field, value in (('x', [0]), ('z', [0]), ('z', [0, 0, 0]),
                             ('eps', C.GRID+1), ('eps', True), ('z', [True, 0])):
            args = dict(base); args[field] = value
            with self.assertRaises(ValueError):
                C._boxed_costs(**args)
        args = dict(base, horizons=[2], x=[4*C.GRID+1])
        with self.assertRaises(ValueError):
            C._boxed_costs(**args)

    def test_arbitrary_rational_theta_and_power_bit_guards(self):
        for N in (2, 12, 81):
            for theta in ('0', '1', '1/2', '2/7', '1/257', '1/1025'):
                fraction = Q(theta)
                expected = max(v for v in range(1, N+1)
                               if v**fraction.denominator <= N**fraction.numerator)
                self.assertEqual(C._power_floor(N, theta, context()), expected)
        for text in ('2/4', '0.5', '-1', '2', '1/0', ''):
            with self.assertRaises(ValueError):
                C._power_floor(12, text, context())
        with self.assertRaises(OverflowError):
            C._power_floor(12, '1/100001', context())

    def test_capacity_and_canonical_rational_gates(self):
        for text in ('2/2', '0.5', ' 1', '1/0', '', str(1 << 4096)):
            with self.assertRaises((ValueError, OverflowError)):
                context().q(text)
        with self.assertRaises(OverflowError):
            C._Context(C.Meter(cap=0)).charge()
        with mock.patch.object(C, 'MAX_MEMORY_BYTES', 8192):
            with self.assertRaises(MemoryError):
                context().reserve(1)
        with mock.patch.object(C, 'MAX_ENTRIES', 0):
            with self.assertRaises(OverflowError):
                context().reserve(1)
        with mock.patch.object(C, 'MAX_WORK', 0):
            with self.assertRaises(OverflowError):
                context().charge()


if __name__ == '__main__':
    started = time.monotonic()
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(Tests)
    test_ids = [test.id() for test in suite]
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    attempt = dict(tests_run=result.testsRun, test_ids=test_ids,
        failures=[dict(test=test.id(), traceback=trace) for test, trace in result.failures],
        errors=[dict(test=test.id(), traceback=trace) for test, trace in result.errors],
        successful=result.wasSuccessful(), charged_work_units=METER.operations,
        wall_seconds=time.monotonic()-started,
        peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
    path = Path(__file__).with_name('mobius_floor_control_checker_068_development.json')
    report = json.loads(path.read_text()) if path.exists() else dict(
        schema='mobius-floor-control-checker-development-v1', synthetic_only=True, attempts=[])
    report['attempts'].append(attempt)
    report['successful'] = result.wasSuccessful()
    report['total_test_invocations'] = sum(a['tests_run'] for a in report['attempts'])
    report['charged_work_units'] = sum(a['charged_work_units'] for a in report['attempts'])
    report['wall_seconds'] = sum(a['wall_seconds'] for a in report['attempts'])
    report['peak_rss_kib'] = max(a['peak_rss_kib'] for a in report['attempts'])
    report['old_suites_replayed'] = False
    path.write_text(json.dumps(report, indent=2, sort_keys=True)+'\n')
    print(json.dumps(attempt, sort_keys=True))
    raise SystemExit(0 if result.wasSuccessful() else 1)
