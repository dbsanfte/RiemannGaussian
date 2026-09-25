#!/usr/bin/env python3
"""Optional finite-mode audit of real shifted-center contraction.

Synthetic divisor data, never asserted zeta zeros. This probes the joint
rational count inverse and retains its cutoff-zero residue and the selected
largest-prime source. It is not a literal finite-prime packet calculation.
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
    mp.mp.dps = 75
    u, share, scale = mp.mpf(10001)/20000, mp.mpf(11)/20, mp.mpf(1)/2
    beta, height = mp.mpf(3)/2-u, mp.mpf(55)
    center = mp.mpf(3)/2+1j*height
    shifted = 1+scale*(center-1)
    base = [beta+1j*height, mp.mpf(99999)/100000+10j*height,
            mp.mpf(99999)/100000+1j*mp.mpf(119)/40*height]
    models = {
        'selected_pair': [base[0], mp.conj(base[0])],
        'three_pairs': base+[mp.conj(z) for z in base],
        'three_full_quartets': base+[mp.conj(z) for z in base]
                              +[1-z for z in base]+[1-mp.conj(z) for z in base],
    }
    rows = []
    for name, zeros in models.items():
        negatives = [z-1-1j*height for z in zeros]
        positives = [mp.mpf(1)/2-(shifted-z)/scale for z in zeros]
        for slope in (mp.mpf(1), 1/scale):
            terms = []
            for j, xi in enumerate(positives):
                rest = positives[:j]+positives[j+1:]
                prefactor = -slope*mp.fprod(xi-a for a in negatives)/mp.fprod(xi-b for b in rest)
                terms.append((-slope, mp.mpf(0), xi))
                for i, a in enumerate(negatives):
                    z = a-xi
                    residue = (prefactor*mp.fprod(xi+slope*z-b for b in rest)
                               /(z*mp.fprod(a-b for k,b in enumerate(negatives) if k != i)))
                    terms.append((residue,z,xi))
            for n in (640, 4096, 16384, 65536, 262144):
                # K=u**(-N)/(N+1); floor(K)+2 is between K+1 and K+2.
                # Hence 0<L_N-2*log(K)<4/K. This error is recorded below.
                log_k = -n*mp.log(u)-mp.log(n+1)
                length = 2*log_k
                lo, hi = mp.mpf(39)*n/20, mp.mpf(203)*n/100

                def response():
                    total, discarded, discarded_count = 0, mp.mpf(0), 0
                    for residue,z,xi in terms:
                        if residue == 0:
                            continue
                        rate = mp.mpf(1)/2-(beta-1)*share-xi*(1-share)+share*z
                        peak = min(hi,max(lo,n/rate.real)) if rate.real > 0 else hi
                        # Absolute bound only for numerically negligible individual
                        # terms, with the entire discarded envelope retained.
                        bound = (mp.log(abs(residue))+z.real*length+(n+1)*mp.log(u)
                                 +mp.log(hi-lo)+n*mp.log(peak)-rate.real*peak-mp.loggamma(n+1))
                        if bound < -90:
                            discarded += mp.exp(bound)
                            discarded_count += 1
                            continue
                        total += (residue*mp.exp(z*length)
                                  *mp.gammainc(n+1,rate*lo,rate*hi)
                                  /(rate**(n+1)*mp.factorial(n)))
                    return total, discarded, discarded_count

                value, discarded, dropped = response()
                with mp.workdps(110):
                    check, _, _ = response()
                    precision_error = abs(value-check)/abs(check)
                assert precision_error < mp.mpf('1e-45')
                log_norm = mp.log10(abs(value))+(n+1)*mp.log10(u)
                rows.append({
                    'model': name, 'cutoff_slope': mp.nstr(slope), 'N': n,
                    'log10_source_normalized': mp.nstr(log_norm,25),
                    'log_source_normalized_over_N': mp.nstr(log_norm*mp.log(10)/n,25),
                    'precision_crosscheck_relative_error': mp.nstr(precision_error,8),
                    'discarded_term_count': dropped,
                    'source_normalized_discarded_envelope': mp.nstr(discarded,8),
                    'log10_moving_length_error_upper': mp.nstr((mp.log(4)-log_k)/mp.log(10),20),
                })
    report = {
        'scope': 'Synthetic finite rational count models, not zeta zeros or a literal packet estimate.',
        'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'mpmath': mp.__version__, 'decimal_precision': 75, 'crosscheck_precision': 110,
        'u': '10001/20000', 'largest_share': '11/20', 'real_scale': '1/2',
        'selected_beta': '19999/20000', 'selected_height': 55,
        'rightward_beta': '99999/100000', 'rightward_height_ratios': ['10','119/40'],
        'count_factor': 'prod_a((w-a)/(w+z-a))*prod_xi((w+h*z-xi)/(w-xi))',
        'cutoff_slopes': {'1': 'Common modal clock', '2': 'Unscaled cutoff relative to the contracted clock'},
        'literal_transfer': 'Neither clock model is asserted to be the literal prime carrier.',
        'radial_window': '39*N/20 < T <= 203*N/100',
        'selected_largest_leg': 'exp((beta-1)*largest_share*T) included',
        'moving_length': '2*log(u**(-N)/(N+1)); error relative to the floor length bounded above by 4*(N+1)*u**N',
        'radial_resonance': '2*(119/40*gamma)-gamma-(11/20)*(10*gamma-gamma)=0 exactly',
        'compiled_resonant_exponent': 'log(10001/20000)-log(250021/500000)-log(10001/20000)/50000 > 1/40000',
        'rows': rows,
    }
    args.output.write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'output':str(args.output),'last_row':rows[-1]},indent=2))


if __name__ == '__main__':
    main()
