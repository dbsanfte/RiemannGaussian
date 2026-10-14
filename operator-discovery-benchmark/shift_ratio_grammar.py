"""Unequal-shift logarithms on complete arithmetic-function prefixes.

The coefficient engine uses divisors and triangular inversion, not primes.
The separate sieve bound imports the published rough-number theorem.
"""

from fractions import Fraction as Q
from functools import lru_cache
import flint

from fractional_prime_grammar import complete_prefix, proper_divisors, power_placement, real


def parameter(value):
    v = Q(value)
    if not 0 < v <= 1:
        raise ValueError('The certified shift-ratio production requires 0 < v <= 1')
    return v


def mixture_parameters(rows):
    if not isinstance(rows, (list, tuple)) or not rows:
        raise ValueError('A finite positive mixture must have at least one atom')
    atoms = []
    for row in rows:
        if not isinstance(row, dict) or set(row) != {'weight', 'v'}:
            raise ValueError('Each mixture atom requires exactly a weight and v')
        w = Q(row['weight'])
        if w <= 0:
            raise ValueError('Mixture weights must be positive')
        atoms.append((w, parameter(row['v'])))
    if sum((w for w, _ in atoms), Q(0)) != 1:
        raise ValueError('Mixture weights must sum exactly to one')
    return tuple(atoms)


@lru_cache(maxsize=None)
def log(n):
    return flint.arb(n).log() if n > 1 else flint.arb(0)


def weight(a, b, v):
    if isinstance(v, tuple):
        return sum((real(w) * weight(a, b, atom) for w, atom in v), flint.arb(0))
    return log(b) / (log(b) + real(v) * log(a))


def forward(values, v):
    inverse = [flint.arb(0)] * len(values)
    inverse[1] = flint.arb(1)
    result = [flint.arb(0)] * len(values)
    for n, ds in enumerate(proper_divisors(len(values) - 1)):
        if n < 2:
            continue
        result[n] = values[n] + sum(
            (inverse[a] * values[n // a] * weight(a, n // a, v) for a in ds), flint.arb(0))
        inverse[n] = -values[n] - sum(
            (values[a] * inverse[n // a] for a in ds), flint.arb(0))
    return result


def recover(decoder, v):
    R = power_placement(decoder, False)
    values = [flint.arb(0)] * len(R)
    inverse = values.copy()
    values[1] = inverse[1] = flint.arb(1)
    for n, ds in enumerate(proper_divisors(len(R) - 1)):
        if n < 2:
            continue
        values[n] = R[n] - sum(
            (inverse[a] * values[n // a] * weight(a, n // a, v) for a in ds), flint.arb(0))
        inverse[n] = -values[n] - sum(
            (values[a] * inverse[n // a] for a in ds), flint.arb(0))
    return values


def sieve_second_moment_bound(v, X, H=None):
    if isinstance(v, tuple):
        v = mixture_parameters([{'weight': w, 'v': atom} for w, atom in v])
        constant = sum((w * 2 * (1 + atom) / atom for w, atom in v), Q(0))
    else:
        v = parameter(v)
        constant = 2 * (1 + v) / v
    if not isinstance(X, int) or isinstance(X, bool) or X < 2:
        raise ValueError('The doubling interval requires an integer X >= 2')
    if H is not None and (not isinstance(H, int) or isinstance(H, bool) or H <= X):
        raise ValueError('Fourier rows require an integer H >= X+1')
    bound = real(constant) * X / log(X)
    return bound if H is None else H * bound


def program_value(program, inputs):
    family = program['family']
    if 'mixture' in program:
        if 'v' in program:
            raise ValueError('Declare one scalar shift or a positive mixture, not both')
        v = mixture_parameters(program['mixture'])
    else:
        v = parameter(program['v'])
    if family == 'shift_ratio_sieve_second_moment_bound':
        return sieve_second_moment_bound(v, program['X'], program.get('H'))
    if family not in ('shift_ratio_log', 'shift_ratio_prime_decoder',
                      'shift_ratio_prime_decoder_inverse'):
        raise ValueError('Unknown shift-ratio production ' + family)
    inverse = family == 'shift_ratio_prime_decoder_inverse'
    values = complete_prefix(inputs[program['input']], normalized=not inverse)
    if inverse:
        return recover(values, v)
    R = forward(values, v)
    return R if family == 'shift_ratio_log' else power_placement(R, True)


PRODUCTION_CATALOGUE = {
    'sort': 'complete ball-valued arithmetic-function prefix',
    'families': ['shift_ratio_log', 'shift_ratio_prime_decoder',
                 'shift_ratio_prime_decoder_inverse', 'shift_ratio_sieve_second_moment_bound'],
    'parameters': 'rational 0 < v <= 1, or arbitrary finite rational positive mixtures with exact weight sum one; v=1 is the classical logarithm',
    'kernel': 'log(b)/(log(b)+v*log(a)) at a*b=n',
    'universal_laws': ['triangular bijection', 'perfect-power placement inverse'],
    'zeta_laws': ['prime value one', 'sharp composite bound (1-v)/(1+v)',
                 'strict factor-count sign for 0<v<1',
                 'least-prime envelope t/(v+(1-v)*g*t)',
                 'sieve-imported M2 <= 2*(1+v)/v * X/log(X)'],
    'zero_signature': 'zero order m gives nonzero logarithmic coefficient m/v**m',
    'zero_signature_domain': 'locally uniform defining integral tail and zero-free rightward corridor; scaled terms require their separate regularity gate',
    'positive_mixture_laws': ['same triangular inverse with averaged kernel',
                             'sharp composite gap sum w*(1-v)/(1+v)',
                             'M2 <= 2*(1+sum w/v)*X/log(X)',
                             'zero coefficient m*sum w/v**m is positive for every m'],
    'positive_mixture_RH_gate': 'B_mixture + log(s-1)*sum w*v*(1/zeta)_prime(v+(1-v)*s) continues holomorphically to Re(s)>1/2 iff RH',
    'historical_novelty_established': False,
    'new_independent_prime_distribution_estimate_proved': False,
    'new_RH_estimate_proved': False,
}
