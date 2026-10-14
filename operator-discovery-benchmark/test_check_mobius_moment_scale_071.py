"""New synthetic mathematics/security checks; no scientific artifacts imported."""
import copy
from fractions import Fraction as Q
import unittest

import check_mobius_moment_scale_071 as c

METERS = []


def meter(**kwargs):
    value = c.Meter(**kwargs)
    METERS.append(value)
    return value


def optimal(system, primal, dual, objective):
    return dict(system=system, result=dict(status='optimal', primal=list(map(str, primal)),
                dual=list(map(str, dual)), objective=str(objective), solver={'synthetic': True}))


def fixture(rho=Q(3, 4)):
    sigma = Q(1, 2)
    kappa = max(Q(1, 2)-rho, Q(-1, 4))
    primary = c.primary_system(sigma, rho, None)
    pd = [0]*12
    if rho >= Q(3, 4):
        pd[7] = pd[9] = 1
    else:
        for i in (4, 5, 6, 8):
            pd[i] = 1
    # For rho>3/4, a valid secondary optimum chooses gammas=3/4.
    exposure = min(rho, Q(3, 4))
    sd = [0]*18
    for i in (6, 8, 13, 14, 15):
        sd[i] = Q(1, 2)
    short = optimal(c.short_system(sigma), [Q(1, 3), Q(2, 3)],
                    [0, 0, Q(2, 3), Q(1, 3), 0], Q(2, 3))
    secondary = optimal(c.secondary_system(primary, 2*kappa),
        [Q(1, 2), exposure, exposure, kappa, kappa, exposure], sd, exposure)
    derivation = dict(theta='1/2', gamma_u=str(exposure), gamma_v=str(exposure),
        kappa_u=str(kappa), kappa_v=str(kappa), exposure=str(exposure), alpha=str(1+2*kappa),
        reciprocal_A='3', head_C_polynomial=list(map(str, [8/(1+2*kappa), 48/(1+2*kappa), 72/(1+2*kappa)])),
        short_exponent='2/3', short_split='1/3', short_C_exponent='2/3',
        short_per_branch_constant='9', sufficient_base_log2=4 if exposure == Q(3, 4) else 3)
    return dict(schema='mobius-moment-scale-program-v1', sigma='1/2', rho=str(rho), fixed_theta=None,
        primary=optimal(primary, [Q(1, 2), rho, rho, kappa, kappa], pd, 2*kappa),
        secondary=secondary, short=short, derivation=derivation, **{f: False for f in c.FLAGS})


def infeasible_fixture():
    program = fixture()
    program['rho'] = '2/5'
    expected = c.primary_system(Q(1, 2), Q(2, 5), None)
    dual = [0]*12
    for i in (2, 3, 4, 5):
        dual[i] = 5
    program['primary'] = dict(system=expected, result=dict(status='infeasible',
        dual=list(map(str, dual)), solver={}))
    program['secondary'] = program['derivation'] = None
    return program


def fixed_fixture():
    program = fixture()
    program['fixed_theta'] = '2/5'
    primary = c.primary_system(Q(1, 2), Q(3, 4), Q(2, 5))
    x = [Q(2, 5), Q(3, 5), Q(3, 4), Q(-1, 5), Q(-3, 20)]
    pd = [0]*14
    pd[7] = pd[8] = pd[5] = 1
    pd[13] = Q(3, 2)
    program['primary'] = optimal(primary, x, pd, Q(-7, 20))
    secondary = c.secondary_system(primary, Q(-7, 20))
    sd = [0]*20
    for i in (7, 8, 15, 17):
        sd[i] = 1
    sd[13] = Q(3, 2)
    program['secondary'] = optimal(secondary, x+[Q(3, 4)], sd, Q(3, 4))
    program['derivation'].update(theta='2/5', gamma_u='3/5', gamma_v='3/4',
        kappa_u='-1/5', kappa_v='-3/20', alpha='13/20',
        head_C_polynomial=['160/13', '960/13', '1440/13'])
    return program


def source_fixture(N=15, y=16, max_j=5, programs=None):
    programs = [fixture()] if programs is None else programs
    p, q, D = 3, 5, 4*N//3
    endpoints = []
    for ratio in (Q(p, q), Q(1)):
        den, num = ratio.denominator, ratio.numerator
        def W(b, d):
            return sum(weight*(factor*N//(b*d)) for factor, weight in ((4, 1), (2, -3), (1, 2)))
        g = {d: -(den*W(p, d)-num*W(q, d)) if y < d <= D else 0 for d in range(1, D+2)}
        steps = [[t, g[t]-g[t+1]] for t in range(1, D+1) if g[t] != g[t+1]]
        atoms = {}
        for b, scale in ((p, den), (q, -num)):
            for factor, weight in ((4, 1), (2, -3), (1, 2)):
                z = factor*N//b
                atoms[z] = atoms.get(z, 0)+weight*scale
        rows = []
        for j in range(1, max_j+1):
            R, h = D//j, {}
            for t, a in steps:
                for A, sign in ((t//j, 1), (t//(j+1), -1)):
                    if A:
                        h[A] = h.get(A, 0)+sign*a
            prefix = [[A, value] for A, value in sorted(h.items()) if value]
            plans = []
            for i, program in enumerate(programs):
                d = program['derivation']
                if d is None:
                    continue
                # Independent brute force exact rational powers on small synthetic radii.
                def floor(exp):
                    exp = Q(exp)
                    return max(n for n in range(1, R+1) if n**exp.denominator <= R**exp.numerator)
                def ceil(exp):
                    exp = Q(exp)
                    return min(n for n in range(1, R+1) if n**exp.denominator >= R**exp.numerator)
                u, v = floor(d['theta']), floor(1-Q(d['theta']))
                Tu, Tv = ceil(d['gamma_u']), ceil(d['gamma_v'])
                beta = 1-Q(d['exposure'])
                plans.append(dict(program_index=i, u=u, v=v, T_u=Tu, T_v=Tv,
                    strict_rank=max(Tu, Tv) < R,
                    universal_base_gate=R >= 3 and R**beta.numerator >= 2**beta.denominator,
                    short_zero_support=(j+1)*max(u, v) <= y))
            rows.append(dict(j=j, R=R, direct_scaled=atoms.get(j, 0), prefix_steps=prefix,
                             b_scaled=sum(A*value for A, value in prefix), V_scaled=sum(abs(v) for _, v in prefix), plans=plans))
        endpoints.append(dict(ratio=str(ratio), denominator=den, steps=steps,
            M1_scaled=sum(t*abs(a) for t, a in steps), rows=rows))
    return dict(schema='mobius-moment-scale-source-v1', N=N, y=y, max_j=max_j,
        parameters=dict(primes=[3, 5], p=3, q=5, alpha='1/2', gamma='1'),
        programs=programs, endpoints=endpoints, **{f: False for f in c.FLAGS})


class CheckerTests(unittest.TestCase):
    def reject(self, cert, source=False):
        with self.assertRaises(ValueError):
            (c.verify_source if source else c.verify_program)(cert, meter())

    def test_exact_optima_on_both_active_facet_regimes(self):
        for rho in (Q(3, 5), Q(3, 4), Q(7, 8)):
            self.assertEqual(c.verify_program(fixture(rho), meter())['status'], 'optimal')

    def test_normalized_farkas_and_false_infeasibility(self):
        cert = infeasible_fixture()
        self.assertEqual(c.verify_program(cert, meter())['status'], 'infeasible')
        cert['primary']['result']['dual'][2] = '4'
        self.reject(cert)
        cert = infeasible_fixture()
        cert['primary']['result']['dual'] = [str(Q(x)/5) for x in cert['primary']['result']['dual']]
        self.reject(cert)

    def test_unresolved_is_observational_and_has_no_derived_claim(self):
        cert = fixture()
        cert['primary']['result'] = dict(status='unresolved', reason='synthetic cap', solver={'success': True})
        cert['secondary'] = cert['derivation'] = None
        self.assertEqual(c.verify_program(cert, meter())['status'], 'unresolved')
        cert['RH_proved'] = True
        self.reject(cert)

    def test_feasible_nonoptimal_and_dual_stationarity_rejected(self):
        cert = fixture()
        cert['primary']['result']['primal'][-2:] = ['0', '0']
        cert['primary']['result']['objective'] = '0'
        self.reject(cert)
        cert = fixture()
        cert['primary']['result']['dual'][7] = '0'
        self.reject(cert)

    def test_exact_feasibility_and_literal_system_are_both_checked(self):
        cert = fixture()
        cert['primary']['result']['primal'][1] = '1/2'
        self.reject(cert)
        cert = fixture()
        cert['primary']['system']['rows'][7]['a'][0] = '0'
        self.reject(cert)

    def test_secondary_optimum_and_complete_C_polynomial(self):
        cert = fixture(Q(7, 8))
        cert['secondary']['result']['primal'][1:3] = ['7/8', '7/8']
        cert['secondary']['result']['primal'][-1] = '7/8'
        cert['secondary']['result']['objective'] = '7/8'
        self.reject(cert)
        cert = fixture()
        cert['derivation']['head_C_polynomial'][2] = '0'
        self.reject(cert)

    def test_short_cost_is_exact_and_not_promoted_to_remainder(self):
        cert = fixture()
        cert['short']['result']['primal'] = ['1/2', '3/4']
        cert['short']['result']['objective'] = '3/4'
        self.reject(cert)
        cert = fixture()
        cert['derivation']['short_C_exponent'] = '1/2'
        self.reject(cert)

    def test_canonical_4096bit_rationals_and_power_resource_gate(self):
        value = Q(2**4095-1, 2**4095)
        self.assertEqual(c.rational(str(value)), value)
        with self.assertRaises(ValueError):
            c.floor_power(3, value, meter())
        self.assertEqual(c.floor_power(1, value, meter()), 1)
        for text in ('2/4', '-0', '01', '1/-2', str(2**4096)):
            with self.assertRaises(ValueError):
                c.rational(text)

    def test_floor_ceiling_and_explicit_integer_base_gate(self):
        for R in (1, 2, 3, 8, 16, 17):
            self.assertEqual(c.floor_power(R, Q(1, 2), meter()), __import__('math').isqrt(R))
            floor = __import__('math').isqrt(R)
            self.assertEqual(c.ceil_power(R, Q(1, 2), meter()), floor+(floor*floor != R))
        cert = source_fixture(N=12, y=10, max_j=1)
        result = c.verify_source(cert, meter())
        self.assertTrue(result['verified'])
        self.assertTrue(cert['endpoints'][0]['rows'][0]['plans'][0]['universal_base_gate'])

    def test_joined_source_residual_and_unscaled_moments(self):
        cert = source_fixture()
        result = c.verify_source(cert, meter())
        ev = result['endpoints'][1]['rows'][0]['evaluations'][0]
        self.assertEqual(ev['H_u'], '1/6')  # u=4, ordinary mu(4)=0
        self.assertEqual(ev['L_u'], '0')
        self.assertEqual(ev['L_v'], '0')
        self.assertEqual(Q(ev['J']), -Q(ev['E']))
        self.assertEqual(Q(ev['actual_coefficient']), Q(ev['direct'])+Q(ev['separable'])+Q(ev['J']))
        scaled = result['endpoints'][0]['rows'][0]['evaluations'][0]
        self.assertEqual(scaled['H_u'], '1/6')

    def test_complete_pairs_include_common_primes_and_ab_above_radius(self):
        mu = [0, 1, -1, -1, 0]
        h, b, R, u, v = [[2, 1], [4, -1]], -2, 4, 3, 3
        ev = c.evaluate(h, b, 0, 1, R, u, v, mu, meter())
        def residual(t):
            return sum(value*(A//t) for A, value in h)-Q(b, t)
        full = sum(mu[a]*mu[z]*residual(a*z) for a in range(1, u+1) for z in range(1, v+1))
        truncated = sum(mu[a]*mu[z]*residual(a*z) for a in range(1, u+1) for z in range(1, v+1) if a*z <= R)
        coprime = sum(mu[a]*mu[z]*residual(a*z) for a in range(1, u+1) for z in range(1, v+1)
                      if __import__('math').gcd(a, z) == 1)
        self.assertEqual(Q(ev['E']), full)
        self.assertNotEqual(full, truncated)
        self.assertNotEqual(full, coprime)

    def test_unit_and_failed_rank_base_rows_retained_truthfully(self):
        cert = source_fixture(N=6, y=3, max_j=8)
        result = c.verify_source(cert, meter())
        self.assertEqual(len(result['endpoints'][0]['rows']), 8)
        plan = cert['endpoints'][0]['rows'][-1]['plans'][0]
        self.assertFalse(plan['strict_rank'])
        self.assertFalse(plan['universal_base_gate'])
        plan['strict_rank'] = True
        self.reject(cert, source=True)

    def test_repeated_plans_deduplicate_evaluation_and_keep_programs(self):
        cert = source_fixture(programs=[fixture(), fixture(), infeasible_fixture()])
        result = c.verify_source(cert, meter())
        self.assertEqual(len(cert['programs']), 3)
        self.assertEqual(len(cert['endpoints'][0]['rows'][0]['plans']), 2)
        self.assertEqual(len(result['endpoints'][0]['rows'][0]['evaluations']), 1)
        cert['endpoints'][0]['rows'][0]['plans'].pop()
        self.reject(cert, source=True)

    def test_fixed_theta_facets_and_distinct_evaluation_order(self):
        cert = source_fixture(programs=[fixture(), fixed_fixture(), fixture()])
        result = c.verify_source(cert, meter())
        evaluations = result['endpoints'][0]['rows'][0]['evaluations']
        self.assertEqual([(e['u'], e['v']) for e in evaluations], [(4, 4), (3, 6)])
        bad = fixed_fixture()
        bad['primary']['system']['rows'].pop()
        self.reject(bad)

    def test_no_derived_plan_still_retains_actual_joined_rows(self):
        result = c.verify_source(source_fixture(programs=[infeasible_fixture()]), meter())
        self.assertEqual(len(result['endpoints'][0]['rows']), 5)
        self.assertTrue(all(row['evaluations'] == [] for endpoint in result['endpoints'] for row in endpoint['rows']))
        self.assertTrue(all(type(row['actual_coefficient']) is str for endpoint in result['endpoints'] for row in endpoint['rows']))

    def test_geometry_tampering_cannot_change_joined_kernel_or_direct(self):
        cert = source_fixture(N=6, y=3, max_j=8)
        for field in ('direct_scaled', 'b_scaled', 'V_scaled'):
            bad = copy.deepcopy(cert)
            bad['endpoints'][0]['rows'][0][field] += 1
            self.reject(bad, source=True)
        bad = copy.deepcopy(cert)
        bad['endpoints'][0]['steps'][0][1] *= -1
        self.reject(bad, source=True)
        bad = copy.deepcopy(cert)
        bad['endpoints'][0]['rows'][0]['prefix_steps'].pop()
        self.reject(bad, source=True)

    def test_work_and_prospective_memory_limits_fail_closed(self):
        with self.assertRaises(ValueError):
            c.verify_program(fixture(), meter(limit=10))
        with self.assertRaises(ValueError):
            c.verify_program(fixture(), meter(seconds=-1))
        old = c.MAX_BYTES
        try:
            c.MAX_BYTES = 1000
            self.reject(source_fixture(), source=True)
        finally:
            c.MAX_BYTES = old


if __name__ == '__main__':
    unittest.main()
