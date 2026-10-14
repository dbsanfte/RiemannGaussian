#!/usr/bin/env python3
"""Attempt the empirically proposed global gap with rational Pólya certificates.

This is a guided proof backend for a previously recorded numerical lead, not
the frozen autonomous discovery runner. It never treats a finite fit as proof.
"""
from fractions import Fraction as Q
from itertools import combinations
from math import factorial, gcd
from pathlib import Path
import hashlib
import json
import time
import sympy as sp

BASE = Path(__file__).resolve().parent
DEST = BASE / 'compensated-shift-results/gap-certificates'


def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()


def multiply(a,b):
    out = {}
    for m,c in a.items():
        for n,d in b.items():
            k = tuple(x+y for x,y in zip(m,n)); out[k] = out.get(k,0)+c*d
    return {k:c for k,c in out.items() if c}


def linear_step(poly):
    dim = len(next(iter(poly))); out = {}
    for m,c in poly.items():
        for j in range(dim):
            n = tuple(x+int(i==j) for i,x in enumerate(m)); out[n] = out.get(n,0)+c
    return {k:c for k,c in out.items() if c}


def signed_homogeneous(variables, shares, g, atoms):
    T = sum(variables); m = len(shares)
    numerator = {}; denominator = {(0,)*len(variables):1}
    # Construct the rational expression directly in homogeneous barycentric
    # variables. Every denominator linear factor has nonnegative coefficients
    # and is strictly positive when T>0 and sum(shares)<=T.
    terms = []
    for k in sp.divisors(g):
        mu = int(sp.mobius(k))
        if not mu: continue
        for r in range(m+1):
            for subset in combinations(range(m),r):
                S = sum((shares[i] for i in subset), sp.Integer(0))*sp.Rational(k,g)
                t = T-S
                factor = sp.Rational(mu*(-1)**r,k)
                if not subset:
                    terms.append((factor, sp.Integer(1), sp.Integer(1)))
                else:
                    factors=[v*T+(1-v)*t for w,v in atoms]
                    den=sp.expand(sp.prod(factors))
                    num=sp.expand(sum(w*t*sp.prod(factors[:j]+factors[j+1:]) for j,(w,v) in enumerate(atoms)))
                    terms.append((factor,num,den))
    den_product = sp.prod(d for c,n,d in terms)
    D = sp.Poly(sp.expand(den_product),*variables)
    H = sp.Poly(0,*variables)
    for c,n,d in terms:
        quotient = D.exquo(sp.Poly(d,*variables))
        H += c*sp.Poly(n,*variables)*quotient
    return H,D


def polya(poly,max_elevations=72):
    coeffs = {m:Q(int(c.p),int(c.q)) for m,c in poly.terms()}
    denominator = sp.ilcm(*(c.denominator for c in coeffs.values()))
    integer = {m:int(c*denominator) for m,c in coeffs.items()}
    common = 0
    for c in integer.values(): common=gcd(common,abs(c))
    integer = {m:c//common for m,c in integer.items()}
    initial = integer
    degree = poly.total_degree()
    for elevation in range(max_elevations+1):
        smallest = min(integer.values())
        negative = sum(c<0 for c in integer.values())
        if not negative:
            return {'status':'universal_nonnegative_polynomial_certified',
                    'initial_degree':degree,'elevation':elevation,'dimension':len(poly.gens),
                    'primitive_initial_integer_coefficients':[[list(m),str(c)] for m,c in sorted(initial.items())],
                    'final_coefficient_count':len(integer),'minimum_nonzero_integer_coefficient':str(smallest),
                    'zero_polynomial':False,'strict_on_positive_barycentric_interior':smallest>0}
        if elevation in (0,4,12,24,48,72):
            print('Pólya progress',len(poly.gens),'degree',degree,'elevation',elevation,'negative',negative,'terms',len(integer),flush=True)
        integer = linear_step(integer)
    return {'status':'unsupported_by_bounded_polya_search','initial_degree':degree,
            'elevations_attempted':max_elevations,'negative_final_coefficients':negative,
            'minimum_final_integer_coefficient':str(smallest),
            'primitive_initial_integer_coefficients':[[list(m),str(c)] for m,c in sorted(initial.items())]}


def main():
    started=time.monotonic()
    path=BASE/'compensated-shift-results/compensated_shift_search.json'
    source=json.loads(path.read_text()); row=source['selected_operator']
    bound=sp.Rational(row['fitted_global_gap'])
    atoms=[(sp.Rational(a['weight']),sp.Rational(a['v'])) for a in row['certificate']['atoms']]
    assert sum(w for w,v in atoms)==1 and all(0<v<1 for w,v in atoms)
    # All small-dimensional regions follow from the integer exponent split.
    x,y,z,s=sp.symbols('x y z slack',nonnegative=True)
    groups=[('omega_two_g_one_repeated', (x,y,s), (x/2,y),1)]
    groups += [('omega_two_g_'+str(g),(x,y,s),(x,y),g) for g in (2,3,4)]
    groups += [('omega_three_g_one',(x,y,z,s),(x,y,z),1)]
    DEST.mkdir(parents=True,exist_ok=True)
    fp={'arithmetic_source_sha256':sha(path),'probe_code_sha256':sha(Path(__file__)),
        'sympy_version':sp.__version__,'proposed_bound':str(bound)}
    records=[]
    for name,variables,shares,g in groups:
        saved=DEST/(name+'.json')
        if saved.exists():
            old=json.loads(saved.read_text())
            if old.get('fingerprint')==fp:
                records.append(old['record']); print('Reuse',name,flush=True); continue
        H,D=signed_homogeneous(variables,shares,g,atoms)
        row={'region':name,'omega':len(shares),'common_exponent_gcd':g,
             'shares':[str(a) for a in shares],'barycentric_variables':list(map(str,variables)),
             'denominator_degree':D.total_degree(),'denominator_has_only_nonnegative_coefficients':all(c>=0 for m,c in D.terms()),
             'denominator_positive_for_T_gt_zero':True,'bound':str(bound),'sides':[]}
        for sign in (1,-1):
            P=bound*D+sign*H
            cert=polya(P)
            row['sides'].append({'sign':sign,'certificate':cert})
        row['all_sides_certified']=all(a['certificate']['status']=='universal_nonnegative_polynomial_certified' for a in row['sides'])
        saved.write_text(json.dumps({'fingerprint':fp,'record':row},indent=2)+'\n')
        records.append(row); print('Region',name,'certified',row['all_sides_certified'],flush=True)
    out={'fingerprint':fp,'records':records,'all_small_regions_certified':all(r['all_sides_certified'] for r in records),
         'global_all_composite_theorem_proved':False,
         'missing_proof_obligations':['uniform tail across unbounded omega','gcd/exponent tail partitions','independent polynomial and arithmetic audit'],
         'historical_novelty_established':False,'seconds':time.monotonic()-started}
    (DEST/'gap_probe.json').write_text(json.dumps(out,indent=2)+'\n')
    print('Gap probe small regions passed',out['all_small_regions_certified'],'seconds',out['seconds'],flush=True)


if __name__=='__main__': main()
