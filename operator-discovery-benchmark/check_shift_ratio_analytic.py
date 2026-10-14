#!/usr/bin/env python3
"""Independent rescaled full integrals, CAS residues and nested zero disks."""

from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
from pathlib import Path
import argparse
import hashlib
import json
import time
import flint
import sympy as sp

BASE=Path(__file__).resolve().parent
DEST=BASE/'shift-ratio-results'


def real(x):
    x=Q(x);return flint.arb(x.numerator)/x.denominator
def square(r):return flint.acb(flint.arb(0,r),flint.arb(0,r))
def short(x):return x.str(30)
def derivative(s,k=1):return flint.acb_series([s,1],prec=k+1).zeta()[k]*(2 if k==2 else 1)


@lru_cache(maxsize=None)
def log(n):return flint.arb(n).log() if n>1 else flint.arb(0)


@lru_cache(maxsize=None)
def factors(n):
    fs={}
    for p,e in flint.fmpz(n).factor():fs[int(p)]=fs.get(int(p),0)+int(e)
    val=1
    for p,e in fs.items():val*=p**e
    assert val==n
    return fs


def divisors(n):
    ds=[1]
    for p,e in factors(n).items():ds=[d*p**k for d in ds for k in range(e+1)]
    return ds


def mu(n):
    fs=factors(n);return 0 if any(e>1 for e in fs.values()) else (-1)**len(fs)


def product_int(xs):
    a=1
    for x in xs:a*=x
    return a


def coefficients(N,v):
    R=[flint.arb(0)]*(N+1);B=R.copy()
    for n in range(2,N+1):
        ps=list(factors(n));ln=log(n)
        for bits in product((0,1),repeat=len(ps)):
            d=product_int(p for p,b in zip(ps,bits) if b)
            if n!=d:
                # A different but algebraically equivalent rational kernel.
                S=log(d)/ln
                R[n]+=(-1)**sum(bits)*(1-S)/(1-real(1-v)*S)
        fs=factors(n);g=sp.igcd(*fs.values()) if len(fs)>1 else next(iter(fs.values()))
        B[n]=sum((real(Q(mu(k),k))*R[product_int(p**(e//k) for p,e in fs.items())]
                  for k in divisors(int(g)) if mu(k)),flint.arb(0))
    return B


def rescaled_R(s,sigma,v):
    T=Q(48);U=v*T
    def f(u,analytic):return -derivative(s+u/real(v))/(real(v)*(s+u).zeta())
    edges=tuple(v*t for t in (Q(0),Q(1,13),Q(1,3),Q(3,2),Q(5),Q(13),Q(29),T))
    result=flint.acb(0)
    for a,b in zip(edges,edges[1:]):
        result+=flint.acb.integral(f,real(a),real(b),abs_tol=flint.arb('1e-28'),
                                  rel_tol=flint.arb('1e-28'),eval_limit=40000,depth_limit=35)
    tail=real(sigma+U).zeta()*(real(sigma+T).zeta()-1)
    result+=square(tail)
    assert result.is_finite()
    return result,tail


def complete_B(s,sigma,v):
    K=11;result=flint.acb(0);tails=[]
    for k in range(1,K+1):
        sign=mu(k)
        if not sign:continue
        if k>=10:
            # Complete Euler-series norm rather than unnecessary quadrature
            # of a term already far below the changed coefficient tail.
            tail=real(k*sigma).zeta()-1
            value=square(tail)
            tails.append({'k':k,'complete_R_Euler_norm_ball':short(tail),'whole_term_enclosed':True})
            result+=real(Q(sign,k))*value
            continue
        value,tail=rescaled_R(k*s,k*sigma,v)
        result+=real(Q(sign,k))*value;tails.append({'k':k,'infinite_integral_tail_ball':short(tail)})
    a=real((K+1)*sigma)
    tail=flint.arb(2)**(-a)*(1+2/(a-1))/((K+1)*(1-flint.arb(2)**(-real(sigma))))
    result+=square(tail)
    assert result.is_finite()
    return result,{'formula':'-1/v integral_0^infinity zeta_prime(s+u/v)/zeta(s+u)du; then full Mobius k-sum',
                   'K':K,'T':'48','U':str(48*v),'changed_infinite_integral_tails':tails,
                   'k_sum_infinite_tail_ball':short(tail),'all_passed':True}


def native_groups(source,fingerprint,selected=None):
    cutoff=512;records=[];cache={}
    for index,row in enumerate(source['actual_zeta_ball_checks']):
        if selected is not None and index!=selected:continue
        component=DEST/('independent_native_group_'+str(index)+'.json')
        if component.is_file():
            previous=json.loads(component.read_text())
            if previous['fingerprint']==fingerprint:
                record=previous['record'];assert record['all_passed']
                records.append(record)
                print('Reused matching independent native group',index,flush=True)
                continue
        v=Q(row['v']);sigma=Q(row['s'][0]);s=flint.acb(real(sigma),row['s'][1])
        if v not in cache:cache[v]=coefficients(cutoff,v)
        whole,cert=complete_B(s,sigma,v)
        recorded=flint.acb(flint.arb(row['native_real_ball']),flint.arb(row['native_imag_ball']))
        assert whole.overlaps(recorded)
        partial=sum((cache[v][n]*(-s*log(n)).exp() for n in range(2,cutoff+1)),flint.acb(0))
        tail=real(cutoff)**real(1-sigma)/real(sigma-1)
        difference=(partial-whole).abs_upper()
        wrong=(partial+real(Q(1,13))*(-s*log(17)).exp()-whole).abs_lower()
        assert difference<tail and wrong>tail
        record={'s':row['s'],'v':str(v),'coefficient_cutoff':cutoff,
                        'independent_coefficient_origin':'factor/subset kernel (1-S)/(1-(1-v)S)',
                        'native_rescaled_integral_certificate':cert,'source_native_overlap':True,
                        'difference_upper_ball':short(difference),'coefficient_tail_ball':short(tail),
                'wrong_prime_index':17,'wrong_difference_lower_ball':short(wrong),'all_passed':True}
        records.append(record)
        component.write_text(json.dumps({'fingerprint':fingerprint,'record':record,
                                        'component_only_not_complete_analytic_audit':True},indent=2)+'\n')
        print('Independent complete shift-ratio decoder',row['s'],'v',v,True,flush=True)
    return {'records':records,'all_passed':True}


def circle_residue(m,v,pole=False):
    r=real(Q(1,9))
    def integrand(theta,analytic):
        z=r*(flint.acb(0,1)*theta).exp()
        if pole:
            # Changed normalized toy F(z)=(1+3z)/(3z), pole residue 1/3.
            Fp=-1/(3*z*z);Fv=(1+3*real(v)*z)/(3*real(v)*z)
            return -Fp/Fv*z
        Fp=m*2**m*z**(m-1)/(1+2*z)**(m+1)
        Fv=(2*real(v)*z/(1+2*real(v)*z))**m
        return Fp/Fv*z
    result=flint.acb(0)
    edges=(Q(0),Q(1,5),Q(2,3),Q(7,6),Q(2))
    for a,b in zip(edges,edges[1:]):
        result+=flint.acb.integral(integrand,real(a)*flint.arb.pi(),real(b)*flint.arb.pi(),
                                  abs_tol=flint.arb('1e-27'),rel_tol=flint.arb('1e-27'),eval_limit=30000)
    result/=2*flint.arb.pi()
    return -result if pole else result


def residues(source):
    t=sp.Symbol('t');rows=[]
    for row in source['zero_signature_grammar']['records']:
        m=row['m'];v=Q(row['v']);sv=sp.Rational(v.numerator,v.denominator)
        # CAS differentiates a changed normalized toy independently.
        F=(2*t/(1+2*t))**m
        exact=sp.residue(sp.diff(F,t)/F.subs(t,sv*t),t,0)
        rational=Q(int(exact.p),int(exact.q));assert rational==Q(m)/v**m
        assert real(rational).overlaps(flint.arb(row['native_residue_real_ball']))
        rows.append({'m':m,'v':str(v),'independent_exact_CAS_residue':str(rational),'all_passed':True})
    fresh=[]
    for m,v in ((2,Q(3,7)),(5,Q(7,9)),(6,Q(2,5)),(8,Q(4,7))):
        value=circle_residue(m,v);assert value.real.overlaps(real(Q(m)/v**m)) and value.imag.contains(0)
        fresh.append({'m':m,'v':str(v),'native_circle_residue_real_ball':short(value.real),'all_passed':True})
    poles=[]
    for v in (Q(2,7),Q(5,8)):
        value=circle_residue(1,v,True)
        assert value.real.overlaps(real(-v)) and value.imag.contains(0)
        # For this changed toy G'(0)=3; the numerator principal part has
        # coefficient 1/3, yielding the product v, as the contour confirms.
        poles.append({'v':str(v),'native_log_pole_coefficient_ball':short(value.real),'all_passed':True})
    assert source['zero_signature_grammar']['survivors']==[{'powers':[1,-1,0],'training_passed':True,'held_out_passed':True}]
    return {'exact_CAS_records':rows,'fresh_native_circle_records':fresh,
            'changed_toy_pole_records':poles,'all_passed':True}


def zero_controls(source):
    # Reuse only previously passed independent corridor audits, with their
    # source hash checked. Re-evaluate the actual disks at fresh precision.
    path=BASE/'fractional-prime-results/fractional_prime_analytic_verification.json'
    oldcheck=json.loads(path.read_text());assert oldcheck['all_passed'] and not oldcheck['production_imports']
    oldsource=BASE/'fractional-prime-results/fractional_prime_analytic.json'
    assert oldcheck['source_artifact_sha256']==hashlib.sha256(oldsource.read_bytes()).hexdigest()
    rows=[];seen=set()
    for row in source['actual_zero_controls']['records']:
        r=Q(row['radius']);c=flint.acb(real(Q(1,2)),row['disk_centre'][1]);v=Q(row['v'])
        region=c+square(real(r/2));d=derivative(c)
        remainder=c.zeta().abs_upper()+real(r*r/8)*derivative(region,2).abs_upper()
        margin=real(r/2)*d.abs_lower()-remainder
        assert margin>0 and derivative(region).abs_lower()>0
        numerator=derivative(c+square(real((2/v-1)*r)))
        denominator=derivative(c+square(real(r)))
        lower=numerator.abs_lower()/(real(v)*denominator.abs_upper())
        assert lower>0
        rows.append({'disk_centre':row['disk_centre'],'v':str(v),'fresh_nested_Rouche_radius':str(r/2),
                     'Rouche_margin_lower_ball':short(margin),'whole_disk_log_coefficient_lower_ball':short(lower),
                     'nonzero_signature_at_zero':str(1/v),'all_passed':True})
        seen.add(tuple(row['disk_centre']))
    oldcentres={tuple(r['disk_centre']) for r in oldcheck['actual_zero_and_corridor_audit']['records']}
    assert seen==oldcentres
    return {'records':rows,'passed_independent_corridor_dependency':str(path.relative_to(BASE)),
            'corridor_verification_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
            'corridor_source_sha256':oldcheck['source_artifact_sha256'],
            'new_zeta_zero_located':False,'all_passed':True}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--reuse-native-groups',action='store_true',
                        help='Reuse a passed independent native component only with matching source, checker and precision')
    parser.add_argument('--native-group',type=int,choices=range(6),
                        help='Verify and checkpoint one complete native group; this is not the full analytic audit')
    args=parser.parse_args()
    start=time.monotonic();flint.ctx.prec=448;flint.ctx.cap=22
    sourcepath=DEST/'shift_ratio_analytic.json'
    source=json.loads(sourcepath.read_text());assert source['all_passed']
    fingerprint={'source_sha256':hashlib.sha256(sourcepath.read_bytes()).hexdigest(),
                 'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                 'precision':flint.ctx.prec,'series_cap':flint.ctx.cap,'flint_version':flint.__version__}
    checkpoint=DEST/'independent_native_groups_checkpoint.json'
    if args.native_group is not None:
        native_groups(source,fingerprint,selected=args.native_group)
        return
    if args.reuse_native_groups:
        previous=json.loads(checkpoint.read_text());assert previous['fingerprint']==fingerprint
        groups=previous['native_full_decoder_audit'];assert groups['all_passed']
        assert len(groups['records'])==6 and all(r['all_passed'] for r in groups['records'])
    else:
        groups=native_groups(source,fingerprint)
        checkpoint.write_text(json.dumps({'fingerprint':fingerprint,'native_full_decoder_audit':groups,
                                         'component_only_not_complete_analytic_audit':True},indent=2)+'\n')
    signatures=residues(source);zeros=zero_controls(source)
    checks={'independent_full_B_rescaled_native_integrals_and_k_tail':groups['all_passed'],
            'changed_complete_subset_coefficients_cutoff_and_wrong_prime_controls':groups['all_passed'],
            'independent_CAS_zero_orders_and_fresh_circle_residues':signatures['all_passed'],
            'pole_signature_and_regularization_sign_controls':signatures['all_passed'],
            'fresh_nested_actual_zero_disks_and_verified_corridor_dependencies':zeros['all_passed'],
            'RH_equivalence_and_estimate_historical_priority_scope_separated':True}
    assert not source['historical_novelty_established'] and not source['new_RH_estimate_proved']
    out={'checks':checks,'native_full_decoder_audit':groups,'zero_signature_audit':signatures,
         'actual_zero_and_corridor_audit':zeros,'source_artifact_sha256':hashlib.sha256(sourcepath.read_bytes()).hexdigest(),
         'fingerprint':fingerprint,'reused_matching_independent_native_groups':args.reuse_native_groups,
         'production_imports':False,'all_passed':all(checks.values()),'seconds':time.monotonic()-start}
    (DEST/'shift_ratio_analytic_verification.json').write_text(json.dumps(out,indent=2)+'\n')
    print('Independent shift-ratio analytic audit',sum(checks.values()),'/',len(checks),'seconds',out['seconds'],flush=True)


if __name__=='__main__':main()
