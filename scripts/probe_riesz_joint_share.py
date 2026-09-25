#!/usr/bin/env python3
"""Optional signed joint-share probe; finite synthetic modes, not zeta zeros.

The largest share is integrated exactly BEFORE the radial integration. All
cofactor pole residues, including the cutoff-zero boundary, are retained.
An internal share seam is tested against its two adjacent signed pieces.
No assertion of a literal-prime packet transfer is made.
"""
import argparse
import hashlib
import json
from pathlib import Path

import mpmath as mp


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    mp.mp.dps = 130
    u = mp.mpf(10001)/20000
    beta, height = mp.mpf(3)/2-u, mp.mpf(55)
    lower, seam, upper = mp.mpf(21)/40, mp.mpf(43)/80, mp.mpf(9)/16
    pole = -1j*height
    # The seam resonance is exact: -gamma+q*(gamma-gamma_other)=0.
    other = height-height/seam
    zeros = [b+1j*g for b in (beta, 1-beta)
             for g in (height, -height, other, -other)]
    modes = [zero-1-1j*height for zero in zeros]
    marked = [(mp.mpf(1), pole)]+[(-mp.mpf(1), a) for a in modes]
    cofactor = [(-mp.mpf(1), mp.mpf(0))]
    numerator = mp.fprod(pole-a for a in modes)
    for i, a in enumerate(modes):
        z = a-pole
        residue = -numerator/(z*mp.fprod(a-b for j, b in enumerate(modes) if i != j))
        cofactor.append((residue, z))

    def normalized_response(n, left, right):
        # Exact floor length, with inexpensive approximation only at huge N.
        log_k = -n*mp.log(u)-mp.log(n+1)
        length = (2*mp.log(20000**n//(10001**n*(n+1))+2)
                  if n <= 8192 else 2*log_k)
        lo, hi = mp.mpf(39)*n/20, mp.mpf(203)*n/100
        assert 0 < length-upper*hi and length < lo
        length_error = mp.mpf(0) if n <= 8192 else 4*mp.exp(-log_k)
        total, omitted, length_effect = mp.mpc(0), mp.mpf(0), mp.mpf(0)

        def term(coeff, z, rate, order):
            nonlocal omitted, length_effect
            if coeff == 0:
                return mp.mpc(0)
            peak = min(hi, max(lo, order/rate.real)) if rate.real > 0 else hi
            bound = (mp.log(abs(coeff))+z.real*length+(n+1)*mp.log(u)
                     +mp.log(hi-lo)+order*mp.log(peak)-rate.real*peak
                     -mp.loggamma(n+1))
            length_effect += abs(z)*length_error*mp.exp(abs(z)*length_error+bound)
            if bound < -500:
                omitted += mp.exp(bound)
                return mp.mpc(0)
            if rate.real <= 0 and abs(rate.imag) < 1:
                peak_log = order*mp.log(peak)-rate.real*peak
                integral = mp.exp(peak_log)*mp.quad(
                    lambda x: mp.exp(order*mp.log(x)-rate*x-peak_log), [lo, hi])
            elif rate.real <= 0:
                # Exact terminating antiderivative, avoiding mpmath's
                # recursive complex-gamma continuation at negative Re.
                def endpoint(x):
                    summand = x**order/rate
                    terms = [summand]
                    for j in range(1, order+1):
                        summand *= (order-j+1)/(rate*x)
                        terms.append(summand)
                    return mp.exp(-rate*x)*mp.fsum(terms)
                integral = endpoint(lo)-endpoint(hi)
            else:
                integral = mp.gammainc(order+1, rate*lo, rate*hi)/rate**(order+1)
            return coeff*mp.exp(z*length+(n+1)*mp.log(u)-mp.loggamma(n+1))*integral

        for cm, a in marked:
            for cr, z in cofactor:
                slope = a-pole-z
                if slope == 0:
                    total += term(cm*cr*(right-left), z, mp.mpf(1)/2-pole, n)
                else:
                    # Integrating exp((pole+q*slope)T) in q costs one
                    # power of T. Its two endpoints stay SIGNED.
                    for endpoint, sign in ((right, 1), (left, -1)):
                        total += term(sign*cm*cr/slope, z,
                                      mp.mpf(1)/2-pole-endpoint*slope, n-1)
        return total, omitted, length_error, length_effect

    rows = []
    for n in (256, 640, 1536, 4096, 8192, 65536, 262144, 1048576):
        pieces = {}
        values = []
        for name, left, right in [('packet', seam, upper),
                                  ('adjacent', lower, seam),
                                  ('joint', lower, upper)]:
            value, error, length_error, length_effect = normalized_response(n, left, right)
            with mp.workdps(190):
                check, _, _, _ = normalized_response(n, left, right)
                relative = abs(value-check)/max(abs(check), mp.mpf('1e-200'))
            assert relative < mp.mpf('1e-70'), (n, name, relative)
            values.append(value)
            pieces[name] = {
                'log10_source_normalized': mp.nstr(mp.log10(abs(value)), 25),
                'log10_raw_response': mp.nstr(mp.log10(abs(value))-(n+1)*mp.log10(u), 25),
                'phase': mp.nstr(mp.arg(value), 20),
                'discarded_absolute_envelope': mp.nstr(error, 8),
                'precision_relative_error': mp.nstr(relative, 8),
                'length_approximation_response_error': mp.nstr(length_effect, 8),
            }
        cancellation_error = abs(values[0]+values[1]-values[2])
        rows.append({'N': n, 'pieces': pieces,
                     'joint_identity_absolute_error': mp.nstr(cancellation_error, 8),
                     'log10_length_error_bound': mp.nstr(mp.log10(length_error), 15)})

    # The two-variable pole quotient of the ACTUAL shifted-center affine
    # substitution differs from the common-clock product used in old probes.
    center = mp.mpf(3)/2+1j*height
    c, ratio = center-1, center/(center-1)
    w, z = mp.mpc('1.7', '.2'), mp.mpc('.4', '.1')
    direct_pole = (w+z-pole)/(w-pole)
    shifted_pole = (ratio*(w-pole)+z)/(ratio*(w-pole))
    quotient = direct_pole/shifted_pole
    expected = ratio*(w-pole+z)/(ratio*(w-pole)+z)
    assert abs(quotient-expected) < mp.mpf('1e-120')
    original = direct_pole*mp.fprod((w-a)/(w+z-a) for a in modes)
    shifted_modes = [pole+(zero-1)/ratio for zero in zeros]
    shifted_factor = shifted_pole*mp.fprod(
        (w-a)/(w+z/ratio-a) for a in shifted_modes)
    filtered = original/shifted_factor
    joint_count = (1-filtered)/z**2+filtered*(1-shifted_factor)/z**2
    original_count = (1-original)/z**2
    assert abs(joint_count-original_count) < mp.mpf('1e-120')
    cutoff_partial_fractions = mp.fsum(cr/(z-zi) for cr, zi in cofactor)
    pole_residue = -mp.fprod((pole-a)/(pole+z-a) for a in modes)/z
    assert abs(cutoff_partial_fractions-pole_residue) < mp.mpf('1e-120')
    # Control: merely moving an exterior edge cannot guarantee a gap for
    # every possible divisor. Retune the synthetic mode to the NEW edge.
    retuned_other = height-height/lower
    retuned_zeros = [b+1j*g for b in (beta, 1-beta)
                    for g in (height, -height, retuned_other, -retuned_other)]
    original_data = modes, marked, cofactor
    modes = [zero-1-1j*height for zero in retuned_zeros]
    marked = [(mp.mpf(1), pole)]+[(-mp.mpf(1), a) for a in modes]
    numerator = mp.fprod(pole-a for a in modes)
    cofactor = [(-mp.mpf(1), mp.mpf(0))]
    for i, a in enumerate(modes):
        zi = a-pole
        cr = -numerator/(zi*mp.fprod(a-b for j,b in enumerate(modes) if i != j))
        cofactor.append((cr, zi))
    retuned = []
    for n in (262144, 1048576):
        value, omitted, _, length_effect = normalized_response(n, lower, upper)
        with mp.workdps(190):
            check, _, _, _ = normalized_response(n, lower, upper)
            rel = abs(value-check)/abs(check)
        assert rel < mp.mpf('1e-70')
        retuned.append({'N': n, 'log10_source_normalized': mp.nstr(mp.log10(abs(value)),25),
                        'discarded_absolute_envelope': mp.nstr(omitted,8),
                        'length_approximation_response_error': mp.nstr(length_effect,8),
                        'precision_relative_error': mp.nstr(rel,8)})
    modes, marked, cofactor = original_data
    report = {
        'scope': 'Synthetic finite all-count rational model, not actual zeros or a literal packet bound.',
        'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'mpmath': mp.__version__, 'precision': 130, 'crosscheck_precision': 190,
        'u': '10001/20000', 'selected_beta': '19999/20000', 'height': 55,
        'other_height_ratio': '-37/43',
        'symmetry': 'Conjugation and beta -> 1-beta retained for all eight synthetic zeros.',
        'cofactor_transform': '(1-(w+z-pole)/(w-pole)*prod((w-a)/(w+z-a)))/z^2',
        'cofactor_below_cone': 'exp(pole*s)*(-1+sum_i residue_i*exp((a_i-pole)*d))',
        'marked_largest_density': 'exp(pole*p*T)-sum_i exp(a_i*p*T)',
        'share_measure': 'dp; no claim that this is the literal factorial/Riesz packet weight.',
        'intervals': {'packet': ['43/80', '9/16'], 'adjacent': ['21/40', '43/80'],
                      'joint': ['21/40', '9/16']},
        'radial_window': '39*N/20 < T <= 203*N/100',
        'moving_length': 'exact floor through N=8192; thereafter approximation with stated error bound',
        'seam_resonant_exponent': mp.nstr(mp.log(2*u)-2*(beta-1)*mp.log(u), 30),
        'two_clock_pole_quotient': 'C*(w-pole+z)/(C*(w-pole)+z), NOT 1',
        'two_clock_regression_error': mp.nstr(abs(quotient-expected), 8),
        'joint_count_error': mp.nstr(abs(joint_count-original_count), 8),
        'cutoff_partial_fraction_error': mp.nstr(abs(cutoff_partial_fractions-pole_residue), 8),
        'joint_count_identity': 'R(P/H)+(P/H)*R(H)=R(P), retaining the original pole',
        'radial_endpoint_rates': {
            str(t): mp.nstr(u*t*mp.exp(1-t/2), 30)
            for t in (mp.mpf(39)/20, mp.mpf(203)/100)},
        'retuned_outer_edge_control': {'other_height_ratio': '-19/21',
                                       'scope': 'The exterior gap is an additional hypothesis, not automatic.',
                                       'rows': retuned},
        'rows': rows,
    }
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True)+'\n')
    print(json.dumps({'output': str(args.output), 'last_row': rows[-1]}, indent=2))


if __name__ == '__main__':
    main()
