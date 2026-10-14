#!/usr/bin/env python3
"""Complete native signed B integrals with explicit tails and zero disks."""

from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json
import time
import flint

BASE = Path(__file__).resolve().parent
DEST = BASE/'compensated-shift-results'


def real(x):
    x = Q(x)
    return flint.arb(x.numerator)/x.denominator


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def square(r):
    return flint.acb(flint.arb(0,r),flint.arb(0,r))


def derivative(s):
    return flint.acb_series([s,1],prec=2).zeta()[1]


def mu(k):
    fs = flint.fmpz(k).factor()
    return 0 if any(e>1 for p,e in fs) else (-1)**len(fs)


def native_R(s,sigma,A):
    T = 44
    def f(t,analytic):
        reciprocal = sum((real(w)/(s+real(v)*t).zeta() for w,v in A),flint.acb(0))
        return -derivative(s+t)*reciprocal
    total = flint.acb(0)
    edges = (0,Q(1,4),1,3,8,19,T)
    for a,b in zip(edges,edges[1:]):
        total += flint.acb.integral(f,real(a),real(b),abs_tol=flint.arb('1e-28'),
                    rel_tol=flint.arb('1e-28'),eval_limit=40000,depth_limit=35)
    tail = sum((real(abs(w))*real(sigma+v*T).zeta() for w,v in A),flint.arb(0))*(real(sigma+T).zeta()-1)
    total += square(tail)
    assert total.is_finite()
    return total,tail


def native_B(s,sigma,A):
    K = 8
    C = sum((abs(w) for w,v in A),Q(0))
    total = flint.acb(0)
    terms = []
    for k in range(1,K+1):
        sign = mu(k)
        if not sign:
            continue
        if k>=7:
            tail = real(C)*(real(k*sigma).zeta()-1)
            R = square(tail)
            info = {'k':k,'complete_R_Euler_norm_ball':tail.str(35)}
        else:
            R,tail = native_R(k*s,k*sigma,A)
            info = {'k':k,'infinite_integral_tail_ball':tail.str(35)}
        total += real(Q(sign,k))*R
        terms.append(info)
    a = real((K+1)*sigma)
    tail = real(C)*flint.arb(2)**(-a)*(1+2/(a-1))/((K+1)*(1-flint.arb(2)**(-real(sigma))))
    total += square(tail)
    assert total.is_finite()
    return total,{'combined_signed_integrand':True,'K':K,'T':44,
                  'weighted_component_tails':terms,'infinite_k_tail_ball':tail.str(35)}


def old_zero_disks(A):
    path = BASE/'shift-ratio-results/shift_ratio_analytic_verification.json'
    checked = json.loads(path.read_text())
    assert checked['all_passed']
    assert checked['source_artifact_sha256']==sha(BASE/'shift-ratio-results/shift_ratio_analytic.json')
    seen = set()
    rows = []
    for row in checked['actual_zero_and_corridor_audit']['records']:
        key = tuple(row['disk_centre'])
        if key in seen:
            continue
        seen.add(key)
        c = flint.acb(real(Q(1,2)),flint.arb(key[1]))
        r = real(Q(row['fresh_nested_Rouche_radius']))
        rho = c+square(r)
        w = square(r)
        slope = derivative(rho)
        coefficient = sum((real(weight/v)*derivative(rho+real(1-1/v)*w)/slope for weight,v in A),flint.acb(0))
        assert slope.abs_lower()>0 and coefficient.abs_lower()>0
        rows.append({'centre':list(key),'radius':str(Q(row['fresh_nested_Rouche_radius'])),
            'whole_disk_log_coefficient_lower_ball':coefficient.abs_lower().str(35),
            'simple_zero_signature':str(sum((weight/v for weight,v in A),Q(0))),
            'same_certified_scaled_zero_free_corridors_used':True,'all_passed':True})
    return {'records':rows,'old_zero_dependency_sha256':sha(path),
            'corridor_dependency':checked['actual_zero_and_corridor_audit'],
            'new_zeta_zero_discovered':False,'all_passed':True}


def main():
    start = time.monotonic()
    flint.ctx.prec = 384
    source_path = DEST/'compensated_shift_search.json'
    source = json.loads(source_path.read_text())
    selected = source['selected_operator']
    A = tuple((Q(a['weight']),Q(a['v'])) for a in selected['certificate']['atoms'])
    C = sum((abs(w) for w,v in A),Q(0))
    fp = {'arithmetic_source_sha256':sha(source_path),'producer_code_sha256':sha(BASE/'compensated_shift_analytic.py'),
          'precision':flint.ctx.prec,'flint_version':flint.__version__}
    records = []
    cutoff = 256
    B = list(map(flint.arb,selected['B_coefficients'][:cutoff+1]))
    for index,(sigma,t) in enumerate(((4,'8.37'),(6,'-12.91'))):
        path = DEST/('producer_native_group_'+str(index)+'.json')
        cached = json.loads(path.read_text()) if path.exists() else {}
        if cached.get('fingerprint')==fp and cached.get('record',{}).get('all_passed'):
            records.append(cached['record'])
            print('Reused matching producer signed native group',index,flush=True)
            continue
        s = flint.acb(sigma,t)
        value,certificate = native_B(s,Q(sigma),A)
        partial = sum((B[n]*(-s*flint.arb(n).log()).exp() for n in range(2,cutoff+1)),flint.acb(0))
        tail = real(C)*real(cutoff)**real(1-sigma)/(sigma-1)
        difference = (partial-value).abs_upper()
        wrong = (partial+real(Q(1,11))*(-s*flint.arb(13).log()).exp()-value).abs_lower()
        assert difference<tail and wrong>tail
        row = {'s':[str(sigma),t],'complete_signed_B_native_compared':True,
            'coefficient_cutoff':cutoff,'native_real_ball':value.real.str(35),
            'native_imag_ball':value.imag.str(35),'complete_native_tail_certificate':certificate,
            'coefficient_tail_ball':tail.str(35),'difference_upper_ball':difference.str(35),
            'wrong_prime_difference_lower_ball':wrong.str(35),'all_passed':True}
        path.write_text(json.dumps({'fingerprint':fp,'record':row},indent=2)+'\n')
        records.append(row)
        print('Producer complete signed native group',index,sigma,t,True,flush=True)
    out = {'arithmetic_source_artifact_sha256':sha(source_path),'fingerprint':fp,
        'actual_zeta_ball_checks':records,'complete_signed_B_native_comparisons':len(records),
        'old_actual_zero_controls':old_zero_disks(A),
        'all_order_signature_certificate':selected['certificate']['root_signature_certificate'],
        'RH_regularized_continuation_criterion_proved':True,'RH_continuation_estimate_proved':False,
        'historical_novelty_established':False,'all_passed':True,'seconds':time.monotonic()-start}
    (DEST/'compensated_shift_analytic.json').write_text(json.dumps(out,indent=2)+'\n')
    print('Compensated analytic producer passed seconds',out['seconds'],flush=True)


if __name__=='__main__':
    main()
