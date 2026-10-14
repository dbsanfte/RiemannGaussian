"""Learn auxiliary states from observations, then synthesize a prefix bound.

No target-specific companion state or invariant is supplied. Observation fits
only propose identities. A separate universal closure oracle must justify
them before a certificate can assert a theorem. The finite section grammar is
deliberately explicit: it cannot express arbitrary arithmetic proof mechanisms.
"""
from fractions import Fraction as F
import time

import numpy as np
import sympy as sp


DEFAULT_SPEC = dict(
    initial_indices=list(range(8)),
    validation_indices=[8, 13, 21, 34, 55, 89, 144, 233],
    max_states=10, max_depth=8, max_rounds=16,
    max_queries=30000, max_source_index=2000000,
    rational_denominator=256, numeric_tolerance=1e-10,
    exponents=['0', '1/6', '1/3', '1/2', '2/3', '5/6', '1'],
    gram_lengths=[1, 2, 3, 4, 6, 8],
    operation_cap=100000000, seconds=600,
)


class Budget:
    def __init__(self, spec):
        self.cap = spec['operation_cap']
        self.operations = 0
        self.deadline = time.monotonic() + spec['seconds']

    def charge(self, n=1):
        self.operations += n
        if self.operations > self.cap or time.monotonic() > self.deadline:
            raise RuntimeError('synthesis resource limit')


def rational_matrix(rows):
    return sp.Matrix([[sp.Rational(str(x)) for x in row] for row in rows])


def encode_matrix(matrix):
    return [[str(matrix[i, j]) for j in range(matrix.cols)]
            for i in range(matrix.rows)]


def exact_psd(matrix, strict=False):
    """Rational symmetric elimination; zero pivot requires a zero row."""
    if matrix.rows != matrix.cols or matrix != matrix.T:
        return False
    a = matrix.copy()
    for i in range(a.rows):
        p = a[i, i]
        if p < 0 or (strict and p == 0):
            return False
        if p == 0:
            if any(a[i, j] != 0 for j in range(i + 1, a.cols)):
                return False
            continue
        for j in range(i + 1, a.rows):
            for k in range(j, a.cols):
                value = a[j, k] - a[i, j] * a[i, k] / p
                a[j, k] = a[k, j] = value
    return True


def _solution(matrix, rhs):
    """One rational solution, with free parameters set to zero."""
    try:
        value, parameters = matrix.gauss_jordan_solve(rhs)
    except ValueError:
        return None
    return value.subs({s: 0 for s in parameters})


def infer_relation(columns, target, exact, spec, meter):
    if not columns:
        return [] if not any(target) else None
    meter.charge(len(target) * (len(columns) + 1) ** 3)
    if exact:
        matrix = sp.Matrix(len(target), len(columns),
                           lambda i, j: sp.Rational(columns[j][i]))
        solution = _solution(matrix, sp.Matrix(target))
        return None if solution is None else [str(x) for x in solution]
    matrix = np.asarray(columns, dtype=float).T
    rhs = np.asarray(target, dtype=float)
    fitted, _, _, _ = np.linalg.lstsq(matrix, rhs, rcond=None)
    rationals = [F(float(x)).limit_denominator(spec['rational_denominator']) for x in fitted]
    residual = matrix @ np.array(list(map(float, rationals))) - rhs
    scale = max(1.0, float(np.max(np.abs(rhs))), float(np.max(np.abs(matrix))))
    if not np.all(np.isfinite(residual)) or np.max(np.abs(residual)) > spec['numeric_tolerance'] * scale:
        return None
    return list(map(str, rationals))


def observable_block_space(A, meter):
    """Discover the row space seen by the target's block sums.

    An auxiliary state can have large prefixes without contributing to the
    target prefix. Exact row closure keeps that distinction and its recovery.
    """
    first = sp.zeros(1, A.rows)
    first[0, 0] = 1
    rows = [first]
    cursor, transitions = 0, []
    while cursor < len(rows):
        matrix = sp.Matrix.vstack(*rows)
        child = rows[cursor] * A
        meter.charge(20 * A.rows ** 3)
        coefficients = _solution(matrix.T, child.T)
        if coefficients is None:
            rows.append(child)
            coefficients = sp.zeros(len(rows), 1)
            coefficients[-1] = 1
        transitions.append(list(coefficients))
        cursor += 1
    h = len(rows)
    reduced = sp.Matrix([row + [0] * (h - len(row)) for row in transitions])
    projection = sp.Matrix.vstack(*rows)
    if projection * A != reduced * projection:
        raise ArithmeticError('exact observable block recovery')
    return projection, reduced


def synthesize_invariant(base, transitions, spec, meter):
    """Search exact exponents and construct metrics, not fitted growth slopes.

    The finite Gram sum and Stein equation are generic metric constructors.
    Their outputs are admitted only by rational matrix inequalities. Testing
    powers gives square, cube, sixth, and arbitrary configured rational roots
    without rounding irrational spectral radii into a proof.
    """
    source_dimension = len(transitions[0])
    full = sum((rational_matrix(m) for m in transitions), sp.zeros(source_dimension))
    projection, A = observable_block_space(full, meter)
    d = A.rows
    def certificate(alpha, metric):
        return dict(alpha=str(alpha), Q=encode_matrix(metric),
                    projection=encode_matrix(projection), block_transition=encode_matrix(A))
    trials = []
    for alpha in sorted(set(map(F, spec['exponents']))):
        if not 0 <= alpha <= 1:
            raise ValueError('prefix exponents must lie in [0,1]')
        p, q = alpha.numerator, alpha.denominator
        if q > 24:
            raise ValueError('rational exponent denominator cap24')
        T, multiplier = A ** q, sp.Integer(base) ** (2 * p)
        # A necessary trace test cheaply rejects many impossible metric goals.
        if (sp.trace(T) ** 2 > d * d * multiplier):
            trials.append(dict(alpha=str(alpha), status='trace_obstruction'))
            continue
        for length in spec['gram_lengths']:
            metric, power = sp.zeros(d), sp.eye(d)
            for j in range(length):
                meter.charge(20 * d ** 3)
                metric += multiplier ** (length - 1 - j) * power.T * power
                power = T * power
            residual = multiplier * metric - T.T * metric * T
            if exact_psd(metric, strict=True) and exact_psd(residual):
                trials.append(dict(alpha=str(alpha), status='exact_invariant', constructor='gram_sum', length=length))
                return certificate(alpha, metric), trials
        # Solve multiplier Q - T^t Q T = I over the symmetric matrices.
        # Indefinite solutions are rejected; no numerical positivity test is used.
        pairs = [(i, j) for i in range(d) for j in range(i, d)]
        basis = []
        for i, j in pairs:
            e = sp.zeros(d)
            e[i, j] = e[j, i] = 1
            basis.append(e)
        transformed = [multiplier * e - T.T * e * T for e in basis]
        equations = sp.Matrix([[e[i, j] for e in transformed] for i, j in pairs])
        rhs = sp.Matrix([int(i == j) for i, j in pairs])
        meter.charge(20 * len(pairs) ** 3)
        coefficients = _solution(equations, rhs)
        if coefficients is not None:
            metric = sum((c * e for c, e in zip(coefficients, basis)), sp.zeros(d))
            if exact_psd(metric, strict=True) and exact_psd(multiplier * metric - T.T * metric * T):
                trials.append(dict(alpha=str(alpha), status='exact_invariant', constructor='stein_equation'))
                return certificate(alpha, metric), trials
        trials.append(dict(alpha=str(alpha), status='no_metric_in_declared_search'))
    return None, trials


def discover(observe, base, spec=None, closure_oracle=None):
    """Search on a black-box sequence; optional oracle checks proposed laws.

    Oracle takes (states, transitions) and returns {verified: bool, ...}; a
    failed proposal may return counterexample_n. It never supplies a state,
    transition, metric, or desired exponent. Its verdict remains independently
    checkable; this routine itself is not the proof admission boundary.
    """
    spec = dict(DEFAULT_SPEC if spec is None else spec)
    if type(base) is not int or not 2 <= base <= 8:
        raise ValueError('integer base2..8')
    for field in ('max_states', 'max_depth', 'max_rounds', 'max_queries'):
        if type(spec[field]) is not int or spec[field] < 1:
            raise ValueError('positive finite synthesis limits')
    meter, cache, trace = Budget(spec), {}, []
    indices = list(spec['initial_indices'])
    if not indices or any(type(n) is not int or n < 0 for n in indices):
        raise ValueError('nonnegative observation indices including unit0')
    if 0 not in indices:
        raise ValueError('unit observation required')
    exact = None
    states = [[1, 0]]

    def value(term, n):
        nonlocal exact
        index = term[0] * n + term[1]
        if index > spec['max_source_index']:
            raise RuntimeError('source index limit')
        if index not in cache:
            if len(cache) >= spec['max_queries']:
                raise RuntimeError('observation query limit')
            meter.charge()
            raw = observe(index)
            is_exact = isinstance(raw, (int, F, sp.Rational))
            if exact is None:
                exact = is_exact
            if exact != is_exact:
                raise ValueError('mixed observation number types')
            cache[index] = F(raw) if is_exact else float(raw)
            if not is_exact and not np.isfinite(cache[index]):
                raise ValueError('finite observations required')
        return cache[index]

    def residual(term, coefficients, n):
        y = value(term, n)
        x = [value(s, n) for s in states]
        if exact:
            return y != sum((F(c) * z for c, z in zip(coefficients, x)), F(0))
        gap = abs(y - sum(float(F(c)) * z for c, z in zip(coefficients, x)))
        return gap > spec['numeric_tolerance'] * max(1.0, abs(y), *(abs(z) for z in x))

    def finish(status, certificate=None, **details):
        return dict(schema='multiscale-bound-search-v1', status=status, base=base,
            states=states, certificate=certificate, trace=trace,
            training_indices=indices, operations=meter.operations,
            source_queries=len(cache), exact_observations=bool(exact),
            observations=[dict(n=n, value=str(cache[n])) for n in sorted(cache)],
            bound_proved=False, whole_signed_bound_proved=False, RH_proved=False,
            **details)

    try:
        for round_id in range(spec['max_rounds']):
            states = [[1, 0]]
            rows = [[] for _ in range(base)]
            cursor = 0
            while cursor < len(states):
                a, c = states[cursor]
                for digit in range(base):
                    term = [base * a, a * digit + c]
                    if term[0] > base ** spec['max_depth']:
                        return finish('state_depth_limit', unresolved_section=term)
                    while True:
                        columns = [[value(s, n) for n in indices] for s in states]
                        target = [value(term, n) for n in indices]
                        relation = infer_relation(columns, target, exact, spec, meter)
                        if relation is None:
                            break
                        witness = next((n for n in spec['validation_indices']
                                        if residual(term, relation, n)), None)
                        if witness is None:
                            break
                        trace.append(dict(event='finite_counterexample', section=term,
                                          n=witness, rejected_coefficients=relation))
                        if witness in indices:
                            relation = None
                            break
                        indices.append(witness)
                    if relation is None:
                        if len(states) >= spec['max_states']:
                            trace.append(dict(event='unrepresented_section', section=term))
                            return finish('state_dimension_limit', unresolved_section=term)
                        states.append(term)
                        relation = ['0'] * (len(states) - 1) + ['1']
                        trace.append(dict(event='new_auxiliary_state', section=term,
                                          round=round_id, state=len(states) - 1))
                    rows[digit].append(relation)
                cursor += 1
            d = len(states)
            transitions = [[row + ['0'] * (d - len(row)) for row in branch] for branch in rows]
            certificate = dict(base=base, states=states, transitions=transitions, bound=None)
            closure = (dict(verified=False, status='unproved_arithmetic_identity')
                       if closure_oracle is None else closure_oracle(states, transitions))
            trace.append(dict(event='universal_closure_attempt', result=closure))
            if not closure.get('verified') and 'counterexample_n' in closure:
                n = closure['counterexample_n']
                if n in indices:
                    return finish('unresolved_closure_counterexample', certificate, closure=closure)
                indices.append(n)
                continue
            bound, trials = synthesize_invariant(base, transitions, spec, meter)
            certificate['bound'] = bound
            status = ('certificate_proposed' if closure.get('verified') and bound is not None
                      else 'open_closure_lemma' if not closure.get('verified')
                      else 'no_bound_certificate_in_grammar')
            return finish(status, certificate, closure=closure, invariant_trials=trials)
        return finish('counterexample_round_limit')
    except RuntimeError as error:
        return finish('resource_limit', reason=str(error))


def no_state_expansion(spec=None):
    return dict(DEFAULT_SPEC if spec is None else spec, max_states=1)
