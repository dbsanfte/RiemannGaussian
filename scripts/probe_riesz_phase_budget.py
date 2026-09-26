#!/usr/bin/env python3
"""Optional analytic quadrature budget for single beta Fourier moments.

This evaluates the classical Gauss error formula (DLMF 3.5.19--20) in
ball arithmetic. It is NOT a Lean theorem, full varying-amplitude quadrature
bound, continuum packet enclosure, or literal prime-sum estimate. Keep it
out of ordinary CI and the numerical zero-count certificate workflow.

For the probability Beta(a,b), the monic orthogonal norm is the product
of the positive squared Jacobi recurrence coefficients. Applying the real
Gauss error to cos and sin separately gives the safe complex bound
2 * norm * frequency^(2q)/(2q)!. Rounding of computed nodes/weights remains
in their balls and must be included separately when using the bound.
"""
import argparse
from fractions import Fraction
import hashlib
import importlib.metadata
import json
import math
from pathlib import Path

from flint import arb, ctx


def ratio(a, b, j, scalar=arb):
    """Squared off-diagonal coefficient for monic shifted Jacobi polynomials."""
    s = a+b-2
    return (scalar(j)*(j+a-1)*(j+b-1)*(j+s)
            / ((2*j+s)**2*(2*j+s-1)*(2*j+s+1)))


def norm_closed(a, b, q):
    """Independent exact factorial formula, for integer a,b>=1 and q>=1."""
    return Fraction(math.factorial(q)*math.factorial(q+a-1)
                    * math.factorial(q+b-1)*math.factorial(a+b-1)
                    * math.factorial(q+a+b-2),
                    (2*q+a+b-1)*math.factorial(2*q+a+b-2)**2
                    * math.factorial(a-1)*math.factorial(b-1))


def regression_checks():
    checks = 0
    for a, b in [(1, 1), (1, 4), (2, 3), (17, 39)]:
        norm = Fraction(1)
        for q in range(1, 17):
            norm *= ratio(a, b, q, Fraction)
            assert norm == norm_closed(a, b, q)
            checks += 1
        # For q=1 the monic polynomial is x-E[x], so its norm is Var[x].
        assert ratio(a, b, 1, Fraction) == Fraction(a*b, (a+b)**2*(a+b+1))
        checks += 1
    return checks


def bound_at(a, b, frequency, q):
    norm = arb(1)
    for j in range(1, q+1):
        norm *= ratio(a, b, j)
    return 2*norm*frequency**(2*q)/arb.fac_ui(2*q)


def budget(n, face, harmonic, tolerance, max_nodes):
    h = (n+99)//100-2 if face == 'lower' else n//25-1
    a, b = h+1, n-h+1
    assert a >= 1 and b >= 1
    # Audit the whole core radial interval, not just T=(N+1)/u.
    tmax = arb(203)*n/100
    frequency = 3*harmonic*tmax/500
    norm = arb(1)
    samples = []
    first = None
    first_bound = None
    for q in range(1, max_nodes+1):
        norm *= ratio(a, b, q)
        bound = 2*norm*frequency**(2*q)/arb.fac_ui(2*q)
        assert bound.is_finite() and bound > 0
        if q in (8, 32, 64, 128, 256, 512, 1024, 2048, 4096):
            samples.append({'nodes': q, 'error_budget': str(bound)})
        if bound < tolerance:
            first, first_bound = q, str(bound)
            break
    return {'N': n, 'face': face, 'beta_parameters': [a, b],
            'harmonic': harmonic, 'radial_endpoint': '203N/100',
            'frequency_bound': str(frequency), 'tested_nodes': samples,
            'fixed_node_budgets': [
                {'nodes': q, 'error_budget': str(bound_at(a, b, frequency, q))}
                for q in (128, 256, 512) if q <= max_nodes],
            'first_passing_nodes': first, 'first_passing_bound': first_bound}


def check_prior_moments(root):
    """The reference enclosure must meet the quadrature enlarged by its budget."""
    from flint import acb
    def parse_complex(text):
        real, imag = text.removesuffix('j').split(' + ')
        return acb(arb(real), arb(imag))
    reports = []
    for name in ('riesz-beta-phase-65536-probe.json', 'riesz-beta-phase-probe.json'):
        path = root/'docs'/name
        data = json.loads(path.read_text())
        for source, digest in data['source_sha256'].items():
            assert hashlib.sha256((root/'scripts'/source).read_bytes()).hexdigest() == digest
        a, b = data['beta_parameters']
        t = (data['N']+1)/(arb(10001)/20000)
        checks = 0
        for row in data['rows']:
            frequency = 3*row['harmonic']*t/500
            reference = parse_complex(row['reference_enclosure'])
            for test in row['quadrature']:
                bound = bound_at(a, b, frequency, test['nodes'])
                computed = parse_complex(test['value'])
                enlarged = computed + acb(arb(0, bound.upper()), arb(0, bound.upper()))
                assert enlarged.overlaps(reference), (name, row['harmonic'], test['nodes'])
                checks += 1
        reports.append({'report': name, 'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
                        'independent_reference_consistency_checks': checks})
    return reports


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders', type=int, nargs='+', default=[65536, 262144, 1048576])
    parser.add_argument('--tolerance', default='1e-30')
    parser.add_argument('--max-nodes', type=int, default=8192)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    ctx.prec = 512
    tolerance = arb(args.tolerance)
    if min(args.orders) < 10000 or not 0 < tolerance < 1 or args.max_nodes < 1:
        parser.error('require N>=10000, 0<tolerance<1, positive node limit')
    root = Path(__file__).resolve().parents[1]
    out = {
        'scope': 'Analytic error budgets for single beta Fourier moments only; not a '
                 'coupled varying-amplitude, continuum, arithmetic, or Lean certificate.',
        'reference': 'https://dlmf.nist.gov/3.5.E19',
        'complex_bound': '2*monic_norm(q)*abs(frequency)^(2*q)/(2*q)!',
        'tolerance': args.tolerance,
        'normalization_checks': regression_checks(),
        'prior_reference_checks': check_prior_moments(root),
        'rows': [budget(n, face, harmonic, tolerance, args.max_nodes)
                 for n in args.orders for face, harmonic in [('lower', 54), ('upper', 12)]],
        'harmonic_scope': '54 and 12 are stress frequencies motivated by the respective '
                          'count caps. This does not identify or bound the frequency '
                          'spectrum or derivatives of the complete coupled integrand.',
        'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'python_flint': importlib.metadata.version('python-flint'),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=2)+'\n')
    print(json.dumps(out, indent=2))


if __name__ == '__main__':
    main()
