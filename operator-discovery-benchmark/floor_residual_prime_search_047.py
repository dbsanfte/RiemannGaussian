"""Discover source-bound prime auxiliaries and candidate energy recurrences.

Exact identities and necessary proof gates precede numerical selection.
Finite recurrence observations do not discharge a uniform arithmetic lemma.
"""
from copy import deepcopy
from fractions import Fraction as Q
import importlib.util
from pathlib import Path

import floor_residual_search_045 as S
import floor_residual_global_rate_guard_046 as G
import check_floor_residual_global_rate_guard_046 as GC

ROOT = Path(__file__).resolve().parent
TRAIN_PARENTS = (32, 47, 63)
FINAL_PARENTS = (131, 167, 199)
PRIMES = (2, 3, 5)
TRAIN_H = 65536
FINAL_H = 1048576
BASE_MINIMUM = 32


def levels(parents):
    return sorted(set(parents) | {2*N+r for N in parents for r in (0, 1)})


def grammar(meter=None):
    meter = meter or S.DRIFT.Meter()
    # A finite complexity budget, not a whitelist in the expression language.
    pool = {Q(n, d) for d in range(2, 12) for n in range(1, d)
            if Q(1, 2) < Q(n, d) <= Q(2, 3)}
    theta = sorted(pool, key=lambda x: (x.numerator+x.denominator, x))[:6]
    recipes = []
    for t in theta:
        for order in range(1, 5):
            spec = S.DRIFT.synthesize_mixture([str(j) for j in range(1, order+1)],
                                            '1', str(t), meter)
            recipes.append(dict(id='prime_profile_%03d' % (len(recipes)+1),
                                base=spec, auxiliary=None))
    return dict(schema='prime-energy-search-047-v1', recipes=recipes,
        primes=list(PRIMES), theta_values=[str(t) for t in theta],
        positive_exponent_factors=['1', '1/2'],
        bound_constants=['1/4', '1', '4'],
        tau_values=['1/4', '1'], d_values=['-1', '1/2', '1', '2'],
        recurrence_rho_values=['1/4', '1/2', '3/4'],
        recurrence_C_over_A_values=['1/8', '1/4', '1/2'],
        control=dict(tau='0', d='0'),
        training_parents=list(TRAIN_PARENTS), final_parents=list(FINAL_PARENTS),
        parities=[0, 1], base_minimum=BASE_MINIMUM,
        base_probes=list(TRAIN_PARENTS), whole_base_interval=[32, 63],
        target='original h=e_(pN)+D_p e_N; full signed auxiliary retained',
        potential='P=||h||^2+tau*||h-d*A_prime||^2',
        recurrence='P_(2N+r)<=rho*P_N+C/L(N)^eta, r=0,1',
        root_denominators_whitelisted=False, fitted_per_N=False,
        uniform_arithmetic_recurrence_proved=False, anticipated_winner=None,
        generation_counts=meter.counts())


def gram(tau, d):
    tau, d = Q(tau), Q(d)
    if tau < 0 or (tau > 0 and d == 0):
        raise ValueError('positive auxiliary weight and noncollinear direction')
    # State is (H,A), h=H+A. This Gram minus (1,1)(1,1)^T is PSD.
    v = 1-d
    return [[str(1+tau), str(1+tau*v)],
            [str(1+tau*v), str(1+tau*v*v)]]


def argument_request(recipe, prime, tau, d, bound, rho, fraction):
    return dict(source_recipe=deepcopy(recipe), rounding=deepcopy(G.ROUNDING),
        prime=prime, original_forcing_b='-1', target=deepcopy(bound),
        argument=dict(state='prime_split_H_A', gram=gram(tau, d),
            recurrence=dict(rho=rho, C=str(Q(bound['A'])*Q(fraction)),
                            forcing='L_parent^-eta', parities=[0, 1]),
            base=dict(minimum=BASE_MINIMUM)))


def proof_gates(frozen, progress=None):
    """Fresh typed proposals; all old necessary guards plus whole-norm046."""
    meter = S.RATE.Meter(cap=150_000_000, seconds=3600)
    checker = S.DRIFT_CHECK.Meter(cap=300_000_000)
    drift = S.DRIFT.Meter(cap=100_000_000, seconds=3600)
    cutoff = S.CUTOFF.Meter(max_operations=10_000_000, seconds=3600)
    cutoff_check = S.CUTOFF.Meter(max_operations=10_000_000, seconds=3600)
    global_meter = G.Meter(cap=10_000_000, seconds=3600)
    global_check = GC.Meter(cap=10_000_000)
    witnesses, cache, families, admissions = {}, {}, [], []
    for recipe in frozen['recipes']:
        node = recipe['base']
        key = S.OLD.ast_key(node)
        if key not in cache:
            cert = S.DRIFT.mixture_certificate(node, drift)
            S.DRIFT_CHECK.verify_certificate(node, cert, meter=checker)
            cache[key] = cert
        rows = S.candidate_rows(recipe, witnesses, cache, meter, checker)
        families.append(dict(recipe=recipe, local_obstructions=rows,
                             moment_certificate=cache[key]))
        # Include the now-refuted eta1 as an explicit gate regression/control.
        etas = sorted({Q(1)} | {(1-Q(node['theta']))*Q(f)
            for f in frozen['positive_exponent_factors']}, reverse=True)
        for prime in frozen['primes']:
            eligible = S.forcing_witnesses(rows, prime, '-1')
            req = dict(recipe=recipe, q=prime, b='-1',
                domain=dict(kind='all_integer', minimum=BASE_MINIMUM),
                rounding=deepcopy(G.ROUNDING))
            cut = S.CUTOFF.build_guard(req, meter=cutoff)
            cut_checked = (S.CUTOFF.verify_guard(req, cut, meter=cutoff_check)
                           if cut['status'] == S.CUTOFF.REFUTED else None)
            accepted, rejected = [], []
            for eta in etas:
                for A in frozen['bound_constants']:
                    bound = dict(A=A, eta=str(eta))
                    g_request = dict(**deepcopy(req), bound=bound)
                    cert = G.build_guard(g_request, meter=global_meter)
                    checked = GC.verify_guard(g_request, cert, meter=global_check)
                    if not checked['verified']:
                        raise ValueError('independent global guard replay')
                    why = S.reject_bound(eligible, A, str(eta))
                    if cut['status'] == S.CUTOFF.REFUTED:
                        why = dict(reason='fixed_cutoff_obstruction')
                    if cert['status'] == G.REFUTED:
                        why = dict(reason='whole_norm_global_rate_obstruction')
                    row = dict(bound=bound, global_certificate=cert,
                               global_verification=checked, rejection=why)
                    (rejected if why else accepted).append(row)
            admissions.append(dict(family=recipe['id'], prime=prime,
                accepted=accepted, rejected=rejected, cutoff_certificate=cut,
                cutoff_verification=cut_checked, upper_bound_proved=False))
        if progress:
            progress('proof_gate_family', family=recipe['id'])
    return dict(schema='prime-presearch-gates-047-v1', families=families,
        admissions=admissions, before_new_scores=True,
        operations=dict(local=meter.operations, local_checker=checker.operations,
            drift=drift.operations, cutoff=cutoff.operations,
            cutoff_checker=cutoff_check.operations, global_rule=global_meter.operations,
            global_checker=global_check.operations),
        rejected_bounds=sum(len(a['rejected']) for a in admissions),
        admitted_bounds=sum(len(a['accepted']) for a in admissions),
        whole_bound_proved=False)


def direction(h, auxiliary, d, identifier):
    d = Q(d)
    c, steps = {}, {}
    for multiplier, p in ((Q(1), h), (-d, auxiliary)):
        for row in p['coefficients']:
            c[row['n']] = c.get(row['n'], Q(0))+multiplier*Q(row['value'])
        for row in p['steps']:
            steps[row['q']] = steps.get(row['q'], Q(0))+multiplier*Q(row['value'])
    return S.OLD.program(identifier, c, steps, Q(h['constant'])-d*Q(auxiliary['constant']))


def interval_combination(coefficients, intervals):
    lo = hi = 0
    for c, (a, b) in zip(coefficients, intervals):
        lo += c*(a if c >= 0 else b)
        hi += c*(b if c >= 0 else a)
    return lo, hi


def potential_interval(tau, d, norms):
    """Use h,H,A norm intervals, including the full signed covariance."""
    tau, d = Q(tau), Q(d)
    weights = [1+tau*(1-d), tau*d, tau*(d*d-d)]
    return interval_combination(weights, [norms[k] for k in ('h', 'H', 'A')])


def training_backend(maximum, meter):
    # The unchanged generic Gram implementation has a declared step-index list.
    # An isolated instance extends only that list to this pilot's actual primes.
    spec = importlib.util.spec_from_file_location('prime_training_047', ROOT/'floor_residual_search_044.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    module.MULTIPLIERS = PRIMES
    return module.TrainingNorms(maximum, TRAIN_H, meter)


def select(rows, limit=2):
    """Rank entire arguments; distinct source families avoid cosmetic variants."""
    if any(r.get('training_parents') != list(TRAIN_PARENTS) or
           r.get('final_observations_used') is not False for r in rows):
        raise ValueError('selection accepts only the registered training partition')
    def key(r):
        return (r['finite_failure_count'] != 0, r['finite_failure_count'],
            -float(Q(r['request']['target']['eta'])),
            float(Q(r['request']['argument']['recurrence']['rho'])),
            -r['helpful_auxiliary_count'], r['complexity'],
            float(Q(r['request']['target']['A'])), r['id'])
    selected, used = [], set()
    for row in sorted((r for r in rows if r['tau'] != '0'), key=key):
        source = row['family']
        if source in used:
            continue
        selected.append(deepcopy(row)); used.add(source)
        if len(selected) == limit:
            break
    return selected


def induction_possible(request):
    """Exact prospective test; authoritative proof is argument047 replay."""
    eta = Q(request['target']['eta'])
    r = request['argument']['recurrence']
    combined = Q(r['rho'])+Q(r['C'])/Q(request['target']['A'])
    L = request['argument']['base']['minimum'].bit_length()
    return combined**eta.denominator <= Q(L, L+1)**eta.numerator


def argument_catalog(frozen, gates):
    recipes = {r['id']: r for r in frozen['recipes']}
    rows, rejected = [], 0
    potentials = [(t, d) for t in frozen['tau_values'] for d in frozen['d_values']]+[('0', '0')]
    for admission in gates['admissions']:
        recipe, prime = recipes[admission['family']], admission['prime']
        for accepted in admission['accepted']:
            for tau, d in potentials:
                for rho in frozen['recurrence_rho_values']:
                    for fraction in frozen['recurrence_C_over_A_values']:
                        req = argument_request(recipe, prime, tau, d,
                            accepted['bound'], rho, fraction)
                        if not induction_possible(req):
                            rejected += 1
                            continue
                        rows.append(dict(id='prime_argument_%06d' % (len(rows)+1),
                            family=recipe['id'], prime=prime, tau=tau, d=d,
                            request=req, target_collinear_control=tau=='0'))
    return dict(rows=rows, invalid_induction_parameters=rejected,
                scores_evaluated=False, uniform_recurrence_proved=False)


def source_request(compiler, recipe, prime, N):
    return dict(prime=prime, parent_support=N,
        parent_values=['1']+[str(v) for v in compiler.weights_at(recipe['base'], N)],
        child_values=['1']+[str(v) for v in compiler.weights_at(recipe['base'], prime*N)])


def training_observations(row, values):
    bound = row['request']['target']
    eta, A = float(Q(bound['eta'])), float(Q(bound['A']))
    recurrence = row['request']['argument']['recurrence']
    rho, C = float(Q(recurrence['rho'])), float(Q(recurrence['C']))
    potentials = {N: potential_interval(row['tau'], row['d'], norms)
                  for N, norms in values.items()}
    bases, recurrences = [], []
    for N in TRAIN_PARENTS:
        lo, hi = potentials[N]
        threshold = A/N.bit_length()**eta
        bases.append(dict(N=N, lower_proxy=lo, upper_proxy=hi,
            threshold=threshold, passes_proxy=hi<=threshold))
        for parity in (0, 1):
            child = 2*N+parity
            lower = potentials[child][0]-rho*hi
            upper = potentials[child][1]-rho*lo
            raw_upper = values[child]['h'][1]-rho*values[N]['h'][0]
            threshold = C/N.bit_length()**eta
            recurrences.append(dict(N=N, child=child, parity=parity,
                increment_lower_proxy=lower, increment_upper_proxy=upper,
                forcing_threshold=threshold, passes_proxy=upper<=threshold,
                auxiliary_improves_increment_proxy=upper<raw_upper,
                h_only_increment_upper_proxy=raw_upper,
                full_signed_energy_retained=True))
    return dict(base_probes=bases, recurrence_probes=recurrences,
        finite_failure_count=sum(not r['passes_proxy'] for r in bases+recurrences),
        helpful_auxiliary_count=sum(r['auxiliary_improves_increment_proxy'] for r in recurrences),
        negative_increment_count=sum(r['increment_upper_proxy']<0 for r in recurrences))


def search(frozen, catalog, progress=None):
    import floor_residual_prime_047 as PRIME
    maximum = max(levels(TRAIN_PARENTS))*max(PRIMES)
    meter = S.OLD.Meter(cap=150_000_000_000, seconds=7200)
    compiler = S.Compiler(maximum, meter=meter, retain_compilation_certificates=False)
    norms = S.CachedNorms(training_backend(maximum, meter))
    prime_meter = PRIME.Meter(cap=2_000_000_000, seconds=7200)
    by_source = {}
    for row in catalog['rows']:
        by_source.setdefault((row['family'], row['prime']), []).append(row)
    results, observations = [], []
    for recipe in frozen['recipes']:
        for prime in PRIMES:
            programs, keys = [], []
            for N in levels(TRAIN_PARENTS):
                request = source_request(compiler, recipe, prime, N)
                cert = PRIME.build_prime_construction(request, meter=prime_meter)
                values = dict(h=cert['original_forcing'], H=cert['matched']['program'],
                              A=cert['matched']['conversion_auxiliary'])
                for role, program in values.items():
                    programs.append(program); keys.append((N, role))
            priced = norms.price(programs)
            intervals = {N: {} for N in levels(TRAIN_PARENTS)}
            for (N, role), value in zip(keys, priced):
                intervals[N][role] = (value['ranking_lower_proxy'], value['ranking_upper_proxy'])
            observations.append(dict(family=recipe['id'], prime=prime,
                values=[dict(N=N, norms={role:list(interval) for role, interval in values.items()})
                        for N, values in intervals.items()], rigorous=False))
            for row in by_source.get((recipe['id'], prime), []):
                finite = training_observations(row, intervals)
                tau, d = Q(row['tau']), Q(row['d'])
                results.append(dict(**row, **finite,
                    complexity=sum(abs(q.numerator)+q.denominator for q in (tau, d)),
                    training_parents=list(TRAIN_PARENTS), final_observations_used=False,
                    uniform_recurrence_proved=False))
        if progress:
            progress('training_family', family=recipe['id'],
                     norm_vectors=norms.misses, exact_cache_hits=norms.hits)
    return dict(schema='prime-energy-candidate-search-v1', rows=results,
        observations=observations, selections=select(results),
        finite_argument_matches=sum(r['finite_failure_count']==0 for r in results),
        noncollinear_finite_matches=sum(r['tau']!='0' and r['finite_failure_count']==0 for r in results),
        distinct_numerical_vectors=norms.misses, exact_vector_cache_hits=norms.hits,
        training_counts=meter.counts(), drift_counts=compiler.drift_meter.counts(),
        prime_counts=prime_meter.counts(), final_observations_used=False,
        uniform_arithmetic_bound_proved=False, RH_proved=False)
