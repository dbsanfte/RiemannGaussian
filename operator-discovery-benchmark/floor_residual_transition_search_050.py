"""Exact structural adversaries and direct moving-prime states.

The adversary reads profile syntax and integer scale maps, never norm scores.
The state compiler is separate from the independent050 source checker.
"""
from copy import deepcopy
from fractions import Fraction as Q
import math
import time

import floor_residual_drift_045 as DRIFT
from floor_residual_global_rate_guard_046 import ROUNDING

MAX_INDEX = 5000
MAX_SUPPORT = 4096
INPUT_BITS = 4096
WORKING_BITS = 16384


class Meter:
    def __init__(self, cap=6_000_000_000, seconds=7200):
        self.cap, self.operations = cap, 0
        self.deadline = time.monotonic()+seconds

    def charge(self, amount=1):
        if type(amount) is not int or amount < 0 or amount > self.cap-self.operations:
            raise OverflowError('transition work budget')
        self.operations += amount
        if time.monotonic() > self.deadline:
            raise TimeoutError('transition time budget')

    def rational(self, value):
        bits = max(abs(value.numerator).bit_length(), value.denominator.bit_length())
        if bits > WORKING_BITS:
            raise OverflowError('transition intermediate rational budget')
        self.charge(1+2*bits)
        return value


def _prime(p):
    if type(p) is not int or not 2 <= p <= MAX_INDEX:
        raise ValueError('bounded ordinary prime')
    if any(p % d == 0 for d in range(2, math.isqrt(p)+1)):
        raise ValueError('ordinary prime required')
    return p


def validate_request(request):
    if type(request) is not dict or set(request) != {'source_recipe', 'prime', 'parent_support', 'd', 'rounding'}:
        raise ValueError('exact transition source request')
    recipe = request['source_recipe']
    if type(recipe) is not dict or set(recipe) != {'id', 'base', 'auxiliary'} or recipe['auxiliary'] is not None:
        raise ValueError('bare moving profile recipe')
    if type(recipe['id']) is not str or not 1 <= len(recipe['id']) <= 250:
        raise ValueError('bounded source identifier')
    DRIFT._spec(recipe['base'])
    p, N = _prime(request['prime']), request['parent_support']
    if type(N) is not int or not 2 <= N <= MAX_INDEX//p:
        raise ValueError('source support within index budget')
    d = DRIFT.rational(request['d'])
    if type(request['rounding']) is not dict or request['rounding'] != ROUNDING or any(type(request['rounding'][k]) is not type(v) for k, v in ROUNDING.items()):
        raise ValueError('exact inherited atom rounding')
    return recipe, p, N, d


def source_request(selected, N):
    return dict(source_recipe=deepcopy(selected['request']['source_recipe']),
        prime=selected['prime'], parent_support=N, d=selected['d'],
        rounding=deepcopy(selected['request']['rounding']))


def _mu_sieve(limit, meter):
    mu, primes, composite = [1]*(limit+1), [], bytearray(limit+1)
    mu[0] = 0
    for n in range(2, limit+1):
        if not composite[n]:
            primes.append(n); mu[n] = -1
        for p in primes:
            meter.charge()
            if n*p > limit:
                break
            composite[n*p] = 1
            if n % p == 0:
                mu[n*p] = 0
                break
            mu[n*p] = -mu[n]
    return mu


def _program(identifier, constant, coeff, steps):
    def text(value):
        if max(abs(value.numerator).bit_length(), value.denominator.bit_length()) > INPUT_BITS:
            raise OverflowError('emitted coefficient input budget')
        return str(value)
    rows = [dict(n=n, value=text(v)) for n, v in sorted(coeff.items()) if v]
    indicators = [dict(q=n, value=text(v)) for n, v in sorted(steps.items()) if v]
    if len(rows)+len(indicators) > MAX_SUPPORT:
        raise OverflowError('emitted support budget')
    if any(r['n'] > MAX_INDEX for r in rows) or any(r['q'] > MAX_INDEX for r in indicators):
        raise OverflowError('emitted index budget')
    return dict(id=identifier, constant=text(Q(constant)), coefficients=rows, steps=indicators)


def semantic_key(program):
    return (program['constant'], tuple((r['n'], r['value']) for r in program['coefficients']),
            tuple((r['q'], r['value']) for r in program['steps']))


class StateCompiler:
    def __init__(self, meter=None, drift_meter=None):
        self.meter = meter or Meter()
        self.drift_meter = drift_meter or DRIFT.Meter(cap=20_000_000_000, seconds=7200)
        self.drift = DRIFT.DriftCompiler(self.drift_meter)
        self.profiles = {}
        self.mu = _mu_sieve(MAX_INDEX, self.meter)

    def profile(self, spec, N):
        key = (spec['a'], spec['theta'], tuple((t['rate'], t['weight']) for t in spec['terms']), N)
        if key not in self.profiles:
            context = self.drift.context(spec, N)
            values = []
            for n in range(1, N+1):
                values.append(context.value(n))
                # Keep the functional atom cache, not every verbose witness.
                context.cache.clear()
            self.profiles[key] = tuple(values)
        return self.profiles[key]

    def compile(self, request):
        recipe, p, N, d = validate_request(request)
        U, V = self.profile(recipe['base'], N), self.profile(recipe['base'], p*N)
        m = self.meter
        # Convention: C*chi - sum c_n*f_n - sum d_q*I_q.
        h = {n: m.rational(-self.mu[n]*V[n-1]) for n in range(2, p*N+1) if self.mu[n]}
        A = {}
        for n in range(2, N+1):
            if not self.mu[n]:
                continue
            c = m.rational(-self.mu[n]*U[n-1])
            h[p*n] = m.rational(h.get(p*n, Q(0))+c)
            h[p] = m.rational(h.get(p, Q(0))-c/n)
            a = m.rational(-self.mu[n]*(U[n-1]-V[p*n-1]))
            A[p*n] = m.rational(A.get(p*n, Q(0))+a)
            A[p] = m.rational(A.get(p, Q(0))-a/n)
        h_steps, A_steps = {p: Q(-1)}, {p: m.rational(V[p-1]-1)}
        v = {n: m.rational(h.get(n, Q(0))-d*A.get(n, Q(0))) for n in h.keys() | A.keys()}
        v_steps = {p: m.rational(h_steps[p]-d*A_steps[p])}
        prefix = 'prime_transition_%d_%d' % (p, N)
        programs = dict(h=_program(prefix+'_h', 1, h, h_steps),
                        A=_program(prefix+'_A', 0, A, A_steps),
                        v=_program(prefix+'_v', 1, v, v_steps))
        return dict(schema='floor-prime-transition-state-v1', request=deepcopy(request),
            parent_values=[str(x) for x in U], child_values=[str(x) for x in V],
            programs=programs, identity_only=True, uniform_bound_proved=False, rh_claim=False)


def profile_parameters(spec, support, meter):
    bc = DRIFT.beta_certificate(spec['a'], spec['theta'], support, meter)
    return dict(support=support, level=bc['L'], ceiling=bc['ceiling'], beta=bc['beta'],
                precision_bits=4*(support-1).bit_length())


def transition_cases(spec, prime, minimum=32, maximum_index=5000, neighborhood=1):
    """Propose both-parity tests around every exact metadata transition.

    Order: upward ceiling events, larger reachable boundary, child roles,
    level before precision, exact crossing before neighbors, N, parity.
    This order depends on no coefficient arrays or observed norm.
    """
    DRIFT._spec(spec); p = _prime(prime)
    if type(minimum) is not int or minimum < 2 or type(maximum_index) is not int or not 2 <= maximum_index <= MAX_INDEX:
        raise ValueError('bounded transition domain')
    if type(neighborhood) is not int or not 0 <= neighborhood <= 3:
        raise ValueError('bounded structural neighborhood')
    maximum = (maximum_index//p-1)//2  # Both parities fit the common domain.
    if maximum < minimum:
        raise ValueError('empty structural search domain')
    meter = DRIFT.Meter()
    proposals = {}
    roles = ('child_prime', 'child', 'parent_prime', 'parent')
    for r in (0, 1):
        maps = {'parent': (1, 0), 'parent_prime': (p, 0),
                'child': (2, r), 'child_prime': (2*p, p*r)}
        for role, (scale, shift) in maps.items():
            for power in range(1, maximum_index.bit_length()):
                for kind, boundary in (('level', 1 << power), ('precision', (1 << power)+1)):
                    crossing = (boundary-shift+scale-1)//scale
                    if not minimum <= crossing <= maximum:
                        continue
                    before_support, after_support = scale*(crossing-1)+shift, scale*crossing+shift
                    before = profile_parameters(spec, before_support, meter)
                    after = profile_parameters(spec, after_support, meter)
                    upward = int(Q(after['ceiling']) > Q(before['ceiling']))
                    # A level/precision boundary can have the same integer
                    # preimage; retain both provenance records, price once.
                    for offset in range(-neighborhood, neighborhood+1):
                        N = crossing+offset
                        if not minimum <= N <= maximum:
                            continue
                        event = dict(role=role, kind=kind, boundary=boundary, crossing_parent=crossing,
                            offset=offset, before=before, after=after, ceiling_increases=bool(upward))
                        rank = (-upward, -boundary, roles.index(role), int(kind == 'precision'),
                                abs(offset), offset, N, r)
                        key = (N, r)
                        if key not in proposals:
                            proposals[key] = dict(N=N, r=r, child=2*N+r, rank=rank, events=[])
                        proposals[key]['rank'] = min(proposals[key]['rank'], rank)
                        proposals[key]['events'].append(event)
    rows = sorted(proposals.values(), key=lambda row: row['rank'])
    for row in rows:
        row['rank'] = list(row['rank'])
        row['source_parameters'] = {role: profile_parameters(spec, scale*row['N']+shift, meter)
            for role, (scale, shift) in {'parent': (1, 0), 'parent_prime': (p, 0),
                'child': (2, row['r']), 'child_prime': (2*p, p*row['r'])}.items()}
    return dict(schema='floor-structural-transition-cases-v1', minimum=minimum, maximum=maximum,
        maximum_source_index=maximum_index, neighborhood=neighborhood, cases=rows,
        scores_used=False, actual_source_arrays_evaluated=False, metadata_counts=meter.counts())
