"""Construct conditional certificates; uniform drift is an explicit OPEN leaf."""
from fractions import Fraction as Q
from math import prod


def energy_request(alpha, features, row):
    return {'alpha': alpha, 'features': features, 'coefficients': row['form']['coefficients'],
        'lambda': row['form']['lambda'], 'delta': row['delta'], 'C': row['C']}


def energy_certificate(request):
    alpha, weight, delta, C = (Q(request[k]) for k in ('alpha', 'lambda', 'delta', 'C'))
    coefficients = request['coefficients']
    terms = []
    for i, a in enumerate(coefficients):
        for j in range(i, len(coefficients)):
            c = weight*a*coefficients[j]*(1 if i == j else 2)+int(i == j == 0)
            if c: terms.append({'i': i, 'j': j, 'coefficient': str(c)})
    base = 108/alpha**2*(1+weight*sum(abs(c) for c in coefficients)**2)
    return {'schema': 'prime-insertion-energy-recovery-v1', 'request': request,
        'matrix_terms': terms, 'base_upper': str(base),
        'recurrence': {'minimum': 2, 'children': [0, 1],
            'formula': 'F(2N+r)<=F(N)+C/N^delta', 'status': 'OPEN'},
        'recovery': {'kind': 'bounded' if delta > 0 else 'logarithmic',
            'constant': str(base+2*C/delta if delta > 0 else base),
            'log_coefficient': '0' if delta > 0 else str(C), 'logarithm_base': 2},
        'uniform_drift_proved': False, 'uniform_target_bound_proved': False, 'RH_proved': False}


def pointwise_proof_attempt(request):
    """Apply paid pointwise insertion control, retaining its actual scale cost.

    For the fixed quadratic filter, |t_i(N)|<=2N log(4N)^alpha/alpha.
    The full F is therefore bounded by the displayed majorant. It has a
    positive power of N and cannot license the requested decaying drift.
    """
    alpha, weight = Q(request['alpha']), Q(request['lambda'])
    factor = 4*(1+weight*sum(abs(c) for c in request['coefficients'])**2)/alpha**2
    return {'status': 'OPEN_JOINT_CORRELATION_REQUIRED',
        'paid_input': '0<=D_S K(n)<=K(n)<=(log n)^alpha, n>=2',
        'paid_F_upper': {'coefficient': str(factor), 'N_power': '1',
            'log_argument': '4N', 'log_power': str(2*alpha)},
        'paid_drift_upper': 'paid_F_upper evaluated at2N+r, sinceF(N)>=0',
        'requested_drift_N_power': str(-Q(request['delta'])),
        'leaf': 'the full signed parent/child correlation, with all cross terms retained',
        'assumed_companion_arithmetic_bound': False,
        'uniform_drift_proved': False, 'uniform_target_bound_proved': False, 'RH_proved': False}


def tail_certificate(request):
    """A genuinely uniform component bound, retaining the unbounded-scale core."""
    tau, primes = request['tau'], request['primes']
    if type(tau) is not int or not 2 <= tau <= 256:
        raise ValueError('integer Laplace cutoff2..256')
    R = prod(primes)
    bound = Q(18, 2**tau) if not primes else Q(12*2**len(primes), R**tau)
    return {'schema': 'prime-insertion-laplace-tail-v1', 'request': request, 'product': R,
        'integer_N_minimum': 2, 'filter': {'q': 2, 'coefficients': [2, -3, 1],
            'normalization': 'divide_by_alpha'},
        'integrand': 'R^-t*sum_(d<=4N,gcd(d,R)=1)mu(d)*d^-t*sum_(e|R)mu(e)*W(N/(d*e))',
        'W': 'floor(4y)-3floor(2y)+2floor(y)', 'normalizer': '1/(alpha*I_alpha)',
        'uniform_absolute_upper': str(bound), 'unpaid_core': '0<t<tau',
        'tail_bound_proved': True, 'complete_target_bound_proved': False, 'RH_proved': False}
