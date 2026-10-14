"""Searchable bounds and small, explicit certificate backends.

An estimate is a target plus a domain, parameter cost and proof obligations.
Finite observations do not discharge those obligations. The positive-energy
backend imports a named rough-number theorem; the cancellation backend uses
the classical Euler factors of the inverse of the constant-one function.
"""

from fractions import Fraction as Q
from math import gcd
from functools import lru_cache
import flint
import sympy as sp


def real(x):
    x = Q(x)
    return flint.arb(x.numerator) / x.denominator


def positive_integer(x, name, minimum=1):
    if type(x) is not int or x < minimum:
        raise ValueError(name + ' must be an integer >= ' + str(minimum))
    return x


def polynomial_kernel(coefficients):
    if not isinstance(coefficients, (list, tuple)) or len(coefficients) < 2:
        raise ValueError('A polynomial smoothing kernel requires coefficients')
    c = tuple(Q(x) for x in coefficients)
    while len(c) > 2 and c[-1] == 0:
        c = c[:-1]
    if c[0] != 1 or sum(c) != 0:
        raise ValueError('The kernel must have W(0)=1 and W(1)=0')
    return c


def inverse_one_prefix(N):
    """Dirichlet inversion using every divisor row, with no prime labels."""
    positive_integer(N, 'Cutoff')
    q = [0] * (N + 1)
    accum = q.copy()
    q[1] = 1
    for n in range(1, N + 1):
        if n > 1:
            q[n] = -accum[n]
        if q[n]:
            for multiple in range(2*n, N+1, n):
                accum[multiple] += q[n]
    return q


def prefix_moments(values, scales, degree):
    if not isinstance(values, (list, tuple)) or len(values) < 2:
        raise ValueError('A complete integer coefficient prefix is required')
    if values[0] != 0 or any(type(a) is not int for a in values):
        raise ValueError('Integer coefficients and unused index zero are required')
    positive_integer(degree, 'Polynomial degree')
    requested = set(scales)
    for X in requested:
        positive_integer(X, 'Scale')
        if X >= len(values):
            raise ValueError('The scale exceeds the complete coefficient prefix')
    sums = [0] * (degree+1)
    output = {}
    for n in range(1, max(requested, default=0)+1):
        power = 1
        for j in range(degree+1):
            sums[j] += values[n] * power
            power *= n
        if n in requested:
            output[n] = tuple(sums)
    return output


def smoothed_from_moments(c, X, sums):
    return sum((a * Q(sums[j], X**j) for j, a in enumerate(c)), Q(0))


def smoothed_sum(values, coefficients, X):
    c = polynomial_kernel(coefficients)
    moments = prefix_moments(values, [X], len(c)-1)
    return smoothed_from_moments(c, X, moments[X])


def growth_bound(C, theta, log_power, X):
    C, theta, log_power = map(Q, (C, theta, log_power))
    positive_integer(X, 'Scale', 2)
    if C < 0 or theta < 0:
        raise ValueError('Nonnegative constant and growth exponent are required')
    return real(C) * real(X)**real(theta) * real(X).log()**real(log_power)


def fit_constant(observations, theta, log_power, margin=Q(5,4), denominator=1024):
    """Round a training constant upward; this is explicitly not a proof."""
    if not observations:
        raise ValueError('At least one training observation is required')
    if Q(margin) < 1:
        raise ValueError('Training margin must be >= 1')
    positive_integer(denominator, 'Rounding denominator')
    ratios = [real(abs(Q(S))) / growth_bound(1, theta, log_power, X)
              for X, S in observations]
    upper = max(a.upper() for a in ratios) * real(margin) * denominator
    rounded = upper.ceil()
    if not rounded.is_exact():
        raise ArithmeticError('The integer rounding was not certified')
    return Q(int(rounded.fmpz()), denominator)


def mellin_certificate(coefficients):
    """An exact Mellin transform and a sufficient nonvanishing test.

Hurwitz positivity only proves absence of numerator roots in Re(s)>=0.
A failed sufficient test is an unresolved gate, not a numerator zero.
"""
    c = polynomial_kernel(coefficients)
    s = sp.Symbol('s')
    transform = sp.cancel(sum(sp.Rational(a.numerator, a.denominator)/(s+j)
                              for j, a in enumerate(c)))
    num, den = map(lambda x: sp.Poly(x, s), sp.fraction(transform))
    a = num.all_coeffs()
    if a[0] < 0:
        a = [-x for x in a]
    degree = len(a)-1
    minors = []
    for size in range(1, degree+1):
        matrix = sp.Matrix(size, size, lambda i, j:
                           a[2*(j+1)-(i+1)] if 0 <= 2*(j+1)-(i+1) <= degree else 0)
        minors.append(matrix.det())
    stable = degree == 0 or (all(x > 0 for x in a) and all(x > 0 for x in minors))
    return {'transform': str(transform),
            'numerator_coefficients_descending': list(map(str, num.all_coeffs())),
            'denominator_coefficients_descending': list(map(str, den.all_coeffs())),
            'Hurwitz_leading_minors': list(map(str, minors)),
            'nonvanishing_Re_s_ge_zero_certified': bool(stable),
            'failed_Hurwitz_test_means_zero_claimed': False,
            'identity': 'integral_1^infinity S_W(X) X^(-s-1)dX = Mellin(W)(s)/zeta(s), initially Re(s)>1'}


def trivial_cancellation_certificate(coefficients):
    c = polynomial_kernel(coefficients)
    # Each Bernstein basis vector is nonnegative and the basis sums to one.
    # Conversion from monomials gives a much tighter bound than sum |c_j|.
    from math import comb
    d = len(c)-1
    bernstein = [sum((c[j] * Q(comb(k,j), comb(d,j)) for j in range(k+1)), Q(0))
                 for k in range(d+1)]
    C = max(map(abs, bernstein))
    return {'backend': 'absolute_sum_and_Bernstein_convex_hull',
            'constant': str(C), 'theta': '1', 'log_power': '0',
            'Bernstein_coefficients': list(map(str, bernstein)),
            'domain': 'every real X >= 1; coefficients are the inverse of constant one',
            'status': 'proved_all_scale_classical_consequence',
            'new_cancellation_estimate': False}


def dilation_candidates(values, multipliers=range(2,21), training_end=64):
    """Learn a local row law; a composite row is not a full partition."""
    rows = []
    for k in multipliers:
        for lam in (-2,-1,0,1,2):
            def fits(indices):
                return all(values[k*n] == (lam*values[n] if gcd(k,n)==1 else 0)
                           for n in indices)
            end = (len(values)-1)//k
            training = fits(range(1, min(end, training_end)+1))
            if training:
                rows.append({'multiplier': k, 'lambda': lam,
                             'training_end': min(end,training_end),
                             'held_out_passed': fits(range(training_end+1,end+1)),
                             'held_out_end': end})
    return rows


def dilation_cancellation_certificate(p):
    positive_integer(p, 'Prime multiplier', 2)
    if not flint.fmpz(p).is_prime():
        raise ValueError('A prime is required to partition all multiples into two rows')
    slope = Q((p-1)**2, p*p)
    # At X=p^2*a+r and r=p*b+c, the residual count is
    # -b/p + (2p-1)c/p^2. Its maximum is at b=0,c=p-1.
    costs = [Q(r-2*(r//p)) - slope*r for r in range(p*p)] if p<=31 else []
    boundary = Q((2*p-1)*(p-1),p*p)
    return {'backend': 'learned_prime_dilation_then_exact_interval_count',
            'prime': p, 'lambda': -1,
            'identity': 'M(X)=sum_(X/p<n<=X,p does not divide n) mu(n)',
            'exact_count': 'X-2*floor(X/p)+floor(X/p^2)',
            'linear_constant': str(slope), 'boundary_cost': str(boundary),
            'residue_costs': list(map(str,costs)),
            'symbolic_residue_cost': '-b/p+(2*p-1)*c/p^2, 0<=b,c<p',
            'domain': 'every integer X >= 1',
            'status': 'proved_all_scale_classical_consequence',
            'new_cancellation_estimate': False}


def atoms(rows):
    if not isinstance(rows, (list, tuple)) or not rows:
        raise ValueError('A nonempty positive finite mixture is required')
    result = []
    for row in rows:
        if not isinstance(row, dict) or set(row) != {'weight','v'}:
            raise ValueError('A mixture atom requires exactly weight and v')
        w,v = Q(row['weight']),Q(row['v'])
        if w<=0 or not 0<v<=1:
            raise ValueError('Positive weights and 0<v<=1 are required')
        result.append((w,v))
    if sum((w for w,v in result), Q(0)) != 1:
        raise ValueError('Weights must sum exactly to one')
    return tuple(result)


@lru_cache(maxsize=None)
def _positive_envelope_certificate(atom_tuple, order, theorem):
    if theorem != 'Fan_Pomerance_Theorem_A':
        raise ValueError('The imported uniform rough-number theorem must be declared')
    positive_integer(order, 'Moment order')
    t = sp.Symbol('t', positive=True)
    h = sum(sp.Rational(w.numerator,w.denominator)*t /
            (sp.Rational(v.numerator,v.denominator)+(1-sp.Rational(v.numerator,v.denominator))*t)
            for w,v in atom_tuple)
    h = sp.cancel(h)
    origin_order = order  # every atom has a simple zero and positive slope
    premises = ['certified score envelope |B(n)| <= h(log(Pmin(n))/log(n))',
                'Fan/Pomerance Phi(x,y)<x/log(y), x>=y>=2; trivial extension 1<y<2']
    if origin_order <= 1:
        return {'backend': 'positive_layercake', 'moment_order': order,
                'envelope': str(h), 'origin_valuation': origin_order,
                'status': 'fixed_X_over_logX_constant_not_certified_by_this_envelope',
                'obligations': ['Retain the truncated integral and its loglog(X) cost; this does not rule out a stronger bound by another method'],
                'premises': premises}
    integrand = sp.cancel(sp.diff(h**order,t)/t)
    primitive = sp.integrate(integrand,t)
    if primitive.has(sp.Integral) or sp.cancel(sp.diff(primitive,t)-integrand) != 0:
        raise ArithmeticError('The synthesized integral certificate failed')
    C = sp.simplify(2*(sp.limit(primitive,t,1,dir='-')-sp.limit(primitive,t,0,dir='+')))
    return {'backend': 'positive_layercake', 'moment_order': order,
            'mixture': [{'weight':str(w),'v':str(v)} for w,v in atom_tuple],
            'envelope': str(h), 'origin_valuation': origin_order,
            'positive_integrand': str(integrand), 'antiderivative': str(primitive),
            'constant_expression': str(C), 'constant_approximation': float(C),
            'bound': 'sum_(X<=n<=2X)|B(n)|^q <= C_q X/log(X)',
            'domain': 'every integer X >= 2', 'parameter_uniformity': 'every declared finite positive rational mixture; constant retains all atom parameters',
            'premises': premises,
            'imported_theorem': {'id': theorem, 'url': 'https://math.dartmouth.edu/~carlp/erat060523rev.pdf',
                                 'external_full_sieve_proof_independently_verified': False},
            'status': 'proved_all_scale_given_named_classical_theorem',
            'constant_synthesized_from_kernel_not_training_target': True,
            'new_independent_prime_distribution_estimate': False}


def positive_envelope_certificate(rows, order, theorem):
    # bool compares and hashes like int in Python; validate before caching.
    positive_integer(order, 'Moment order')
    return _positive_envelope_certificate(atoms(rows), order, theorem).copy()


def envelope_constant_ball(rows, order):
    A = atoms(rows)
    positive_integer(order, 'Moment order', 2)
    def integrand(t, analytic):
        # Remove the zero at t=0 before division: h=t*a.
        a = sum((real(w)/(real(v)+real(1-v)*t) for w,v in A), flint.acb(0))
        derivative = sum((real(w*v)/(real(v)+real(1-v)*t)**2 for w,v in A), flint.acb(0))
        return 2*order*t**(order-2)*a**(order-1)*derivative
    C = flint.acb.integral(integrand,0,1,abs_tol=flint.arb('1e-35'),
                           rel_tol=flint.arb('1e-35'),depth_limit=30,eval_limit=40000)
    if not C.is_finite() or not C.imag.contains(0) or not C.real > 0:
        raise ArithmeticError('Positive envelope integral did not certify a finite constant')
    return C.real


def rational_upper(value, denominator=2**32):
    positive_integer(denominator, 'Rounding denominator')
    rounded = (value.upper()*denominator).ceil()
    if not rounded.is_exact():
        raise ArithmeticError('The upper rounding was not certified')
    return Q(int(rounded.fmpz()),denominator)


def program_value(program, inputs):
    family = program['family']
    if family == 'smoothed_coefficient_sum':
        return smoothed_sum(inputs[program['input']],program['kernel'],program['X'])
    if family == 'candidate_growth_bound':
        return growth_bound(program['constant'],program['theta'],program['log_power'],program['X'])
    if family == 'positive_envelope_moment_certificate':
        return positive_envelope_certificate(program['mixture'],program['moment_order'],program['imported_theorem'])
    if family == 'prime_dilation_cancellation_certificate':
        return dilation_cancellation_certificate(program['prime'])
    if family == 'polynomial_Mellin_certificate':
        return mellin_certificate(program['kernel'])
    raise ValueError('Unknown estimate production ' + family)


PRODUCTION_CATALOGUE = {
    'kind': 'estimate_program',
    'families': ['smoothed_coefficient_sum','candidate_growth_bound',
                 'positive_envelope_moment_certificate',
                 'prime_dilation_cancellation_certificate','polynomial_Mellin_certificate'],
    'estimate_fields': ['target','domain','constant','growth_exponent','log_cost','parameter_cost','certificate','obligations'],
    'certificate_backends': ['absolute_sum_and_Bernstein_convex_hull',
                             'learned_prime_dilation_then_exact_interval_count',
                             'positive_layercake_with_named_classical_theorem',
                             'Mellin_nonvanishing_and_known_zero_obstruction'],
    'finite_fit_is_global_proof': False,
    'new_RH_cancellation_backend_available': False,
    'new_independent_prime_distribution_theorem_available': False,
}
