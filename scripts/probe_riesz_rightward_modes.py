#!/usr/bin/env python3
"""Optional rightward-mode/filter audit; no actual zeros are asserted.

All displayed witnesses have real parts of zero-like coordinates in (0,1),
denominators outside the exposed source disk and inside R=3/4, and modal
shares realized by a five-prime share vector in the literal largest/least
box. Optimization does not claim that zeta has any of these zeros.
"""
import argparse
import hashlib
import itertools
import json
from pathlib import Path

import numpy as np
import scipy
from scipy.optimize import minimize

U = 10001/20000
R = 3/4
Q = 43/80


def isolator(nodes):
    # Evaluate in factored form, preserving exact roots and avoiding
    # cancellation of large coefficients near the pole at y=0.
    roots=1/np.asarray(nodes,dtype=complex)
    assert np.all(roots != 1/U)
    return lambda x:np.prod([(x-root)/(1/U-root) for root in roots],axis=0)


def witness(m, delta):
    shares = {2:[Q,1-Q],3:[Q,.3,.1625],4:[Q,.23,.18,.0525]}[m]
    heights = {2:[.1,-43/370],3:[.1,-.08,-119/650],
               4:[.1,-.1,-.1,-17/70]}[m]
    # Each modal vector is realizable with five positive prime shares.
    prime_shares = {2:[Q,.2,.15,.1,.0125],3:[Q,.15,.15,.15,.0125],
                    4:[Q,.23,.18,.04,.0125]}[m]
    q,b = np.asarray(shares),np.asarray(heights)
    z = (U-delta)+1j*b
    mixed = q@z
    reflected = R*R/np.conj(z)
    polynomial = isolator(z)
    variance = q@(b-(q@b))**2
    return {'mode_count':m,'gain_each':delta,'shares':shares,
            'prime_shares':prime_shares,'ordinate_offsets':heights,
            'weighted_ordinate':float(q@b),
            'direct_norms':list(np.abs(z)),
            'reflected_real_parts':list(reflected.real),
            'mixed_real':float(mixed.real),'mixed_imag':float(mixed.imag),
            'mixed_norm':float(abs(mixed)),
            'global_norm_lower_bound':float(U-delta),
            'weighted_ordinate_variance':float(variance),
            'variance_div_gain':float(variance/delta),
            'min_individual_squared_offset_div_gain':float(np.min(b*b)/delta),
            'isolator_at_selected':[float(polynomial(1/U).real),float(polynomial(1/U).imag)],
            'maximum_isolator_at_individual_modes':float(np.max(np.abs(polynomial(1/z)))),
            'isolator_at_mixed':[float(polynomial(1/mixed).real),float(polynomial(1/mixed).imag)],
            'warning':'Synthetic denominator geometry, not actual zeta-zero data. The common real-part lower bound applies to every reflected/direct choice; the balanced direct witness attains it.'}


def optimize(m,delta):
    row=witness(m,delta)
    q=np.asarray(row['shares']);initial=np.asarray(row['ordinate_offsets'])
    a=U-delta
    bound=np.sqrt(R*R-a*a)-1e-8
    minimum_height_sq=U*U-a*a
    rows=[]
    for flags in itertools.product((False,True),repeat=m):
        flags=np.asarray(flags)
        def value(b):
            z=a+1j*b
            modes=np.where(flags,R*R/np.conj(z),z)
            return abs(q@modes)**2
        result=minimize(value,initial,method='SLSQP',bounds=[(-bound,bound)]*m,
                        constraints=[{'type':'ineq','fun':lambda b:b*b-minimum_height_sq}],
                        options={'ftol':1e-13,'maxiter':500})
        valid=bool(np.all(result.x**2>=minimum_height_sq-1e-10))
        rows.append({'reflected':flags.tolist(),'success':bool(result.success),
                     'feasible_to_1e-10':valid,'norm':float(np.sqrt(result.fun)),
                     'ordinate_offsets':result.x.tolist()})
    return {'mode_count':m,'gain_each':delta,'runs':rows,
            'global_lower_bound':a,
            'balanced_direct_norm':row['mixed_norm'],
            'note':'The explicit direct witness attains the real-part lower bound. Other optimizer runs are local diagnostics, not certified optima.'}


def pole_zero(y):
    pole=.5+1j*y
    zero=U-1j*Q*y/(1-Q)
    mixed=Q*pole+(1-Q)*zero
    jet=isolator([pole,pole])
    isolated=isolator([pole,pole,zero]) if y else None
    return {'evaluation_height':y,'actual_pole_denominator':[.5,y],
            'required_zero_denominator':[float(zero.real),float(zero.imag)],
            'required_zero_height':float(y/(1-Q)),
            'mixed_denominator':[float(mixed.real),float(mixed.imag)],
            'growth_exponent':float(np.log(U/abs(mixed))),
            'pole_jet_at_pole':[float(jet(1/pole).real),float(jet(1/pole).imag)],
            'pole_jet_at_mixture':[float(jet(1/mixed).real),float(jet(1/mixed).imag)],
            'zero_and_pole_isolator_at_mixture':
                [float(isolated(1/mixed).real),float(isolated(1/mixed).imag)] if isolated else None,
            'warning':'No existence of the required same-real-part zero or exact ordinate relation is asserted. y=0 is only the zero-height algebraic illustration, not a nontrivial zeta zero.'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    rows=[witness(m,d) for m in (2,3,4) for d in (1e-5,1e-7,1e-9,1e-11)]
    for row in rows:
        assert abs(row['weighted_ordinate'])<1e-14
        assert abs(row['mixed_norm']-row['global_norm_lower_bound'])<1e-14
        assert all(U<v<R for v in row['direct_norms'])
        assert 3/250<=min(row['prime_shares'])<=7/250
        assert 43/80<=max(row['prime_shares'])<=9/16
        assert abs(sum(row['prime_shares'])-1)<1e-14
    report={'status':'Exploratory synthetic mode audit, not arithmetic or zeta-zero data.',
            'numpy':np.__version__,'scipy':scipy.__version__,
            'input_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'radius':U,'canonical_radius':R,'witnesses':rows,
            'optimizations':[optimize(m,1e-5) for m in (2,3,4)],
            'pole_zero':[pole_zero(y) for y in (0.,20.,100.)]}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(report,indent=2)+'\n')
    for row in rows:
        print(row['mode_count'],row['gain_each'],row['mixed_norm'],
              row['variance_div_gain'],row['isolator_at_mixed'])


if __name__=='__main__':
    main()
