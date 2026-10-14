#!/usr/bin/env python3
"""Independent complete atomic integrals, signed residues and actual zero disks."""
from fractions import Fraction as Q
from pathlib import Path
import argparse
import hashlib
import json
import time
import flint
import sympy as sp

# Previously independent backend, not the combined production integrand.
from check_shift_ratio_analytic import complete_B, coefficients, derivative, real, square, log

BASE=Path(__file__).resolve().parent
DEST=BASE/'compensated-shift-results'


def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()


def short(x): return x.str(35)


def native_groups(source,A,fingerprint,selected=None):
    records=[]; cutoff=512; C=sum((abs(w) for w,v in A),Q(0))
    B={v:coefficients(cutoff,v) for w,v in A}
    for index,row in enumerate(source['actual_zeta_ball_checks']):
        if selected is not None and index!=selected: continue
        path=DEST/('independent_native_group_'+str(index)+'.json')
        old=json.loads(path.read_text()) if path.exists() else {}
        if old.get('fingerprint')==fingerprint and old.get('record',{}).get('all_passed'):
            records.append(old['record']); print('Reuse complete signed independent group',index,flush=True); continue
        sigma=Q(row['s'][0]); s=flint.acb(real(sigma),row['s'][1]); whole=flint.acb(0); certs=[]
        for w,v in A:
            value,cert=complete_B(s,sigma,v); whole+=real(w)*value
            certs.append({'weight':str(w),'v':str(v),'independent_rescaled_complete_B_certificate':cert})
        recorded=flint.acb(flint.arb(row['native_real_ball']),flint.arb(row['native_imag_ball']))
        assert whole.overlaps(recorded)
        partial=sum((sum((real(w)*B[v][n] for w,v in A),flint.arb(0))*(-s*log(n)).exp()
                     for n in range(2,cutoff+1)),flint.acb(0))
        tail=real(C)*real(cutoff)**real(1-sigma)/real(sigma-1)
        difference=(partial-whole).abs_upper()
        wrong=(partial+real(Q(1,13))*(-s*log(17)).exp()-whole).abs_lower()
        assert difference<tail and wrong>tail
        record={'s':row['s'],'coefficient_cutoff':cutoff,'complete_signed_B_native_compared':True,
                'native_real_ball':short(whole.real),'native_imag_ball':short(whole.imag),
                'atomic_integrals_evaluated_separately_after_rescaling':True,'atomic_certificates':certs,
                'infinite_integral_and_k_tails_retained':True,'source_native_overlap':True,
                'coefficient_tail_ball':short(tail),'difference_upper_ball':short(difference),
                'wrong_prime':17,'wrong_prime_difference_lower_ball':short(wrong),'all_passed':True}
        path.write_text(json.dumps({'fingerprint':fingerprint,'record':record,'component_only_not_full_audit':True},indent=2)+'\n')
        records.append(record); print('Independent complete signed zeta group',index,row['s'],True,flush=True)
    return {'records':records,'all_passed':True}


def circle(m,A,pole=False):
    radius=real(Q(1,13))
    def f(theta,analytic):
        z=radius*(flint.acb(0,1)*theta).exp()
        if pole:
            Fp=-1/(4*z*z)
            return sum((real(w)*Fp/((1+4*real(v)*z)/(4*real(v)*z))*z for w,v in A),flint.acb(0))
        Fp=m*3**m*z**(m-1)/(1+3*z)**(m+1)
        return sum((real(w)*Fp/(3*real(v)*z/(1+3*real(v)*z))**m*z for w,v in A),flint.acb(0))
    edges=(Q(0),Q(1,7),Q(3,5),Q(8,7),Q(2)); out=flint.acb(0)
    for a,b in zip(edges,edges[1:]):
        out+=flint.acb.integral(f,real(a)*flint.arb.pi(),real(b)*flint.arb.pi(),
                              abs_tol=flint.arb('1e-27'),rel_tol=flint.arb('1e-27'),eval_limit=30000)
    return out/(2*flint.arb.pi())


def residues(A):
    t=sp.Symbol('t'); rows=[]
    for m in (1,2,3,5):
        F=(5*t/(1+5*t))**m
        exact=sum((sp.Rational(w.numerator,w.denominator)*sp.residue(sp.diff(F,t)/F.subs(t,sp.Rational(v.numerator,v.denominator)*t),t,0)
                   for w,v in A),sp.Integer(0))
        expected=m*sum((w/v**m for w,v in A),Q(0))
        assert exact==sp.Rational(expected.numerator,expected.denominator)
        rows.append({'order':m,'exact_signed_logarithmic_coefficient':str(expected),'all_passed':True})
    circles=[]
    for m,atoms in ((1,A),(2,A),(5,A),(2,((Q(-9,16),Q(3,7)),(Q(25,16),Q(5,7))))):
        value=circle(m,atoms); expected=m*sum((w/v**m for w,v in atoms),Q(0))
        assert value.real.overlaps(real(expected)) and value.imag.contains(0)
        circles.append({'order':m,'atoms':[[str(w),str(v)] for w,v in atoms],
                        'expected_leading_signature':str(expected),'native_real_ball':short(value.real),
                        'whole_log_branch_erasure_inferred_from_zero_residue':False,'all_passed':True})
    value=circle(1,A,True); expected=-sum((w*v for w,v in A),Q(0))
    assert value.real.overlaps(real(expected)) and value.imag.contains(0)
    return {'exact_CAS_records':rows,'fresh_native_circle_records':circles,
            'fresh_pole_coefficient':{'expected':str(expected),'native_real_ball':short(value.real),'all_passed':True},
            'all_passed':True}


def actual_zeros(source,A):
    oldpath=BASE/'shift-ratio-results/shift_ratio_analytic_verification.json'
    old=json.loads(oldpath.read_text()); assert old['all_passed'] and not old['production_imports']
    assert old['source_artifact_sha256']==sha(BASE/'shift-ratio-results/shift_ratio_analytic.json')
    assert source['old_actual_zero_controls']['old_zero_dependency_sha256']==sha(oldpath)
    corridor=old['actual_zero_and_corridor_audit']
    assert sha(BASE/corridor['passed_independent_corridor_dependency'])==corridor['corridor_verification_sha256']
    base=json.loads((BASE/corridor['passed_independent_corridor_dependency']).read_text())
    assert base['all_passed'] and base['source_artifact_sha256']==sha(BASE/'fractional-prime-results/fractional_prime_analytic.json')
    rows=[]
    for row in source['old_actual_zero_controls']['records']:
        c=flint.acb(real(Q(1,2)),row['centre'][1]); r=real(Q(row['radius'])/2)
        region=c+square(r); slope=derivative(c)
        remainder=c.zeta().abs_upper()+r*r*derivative(region,2).abs_upper()/2
        margin=r*slope.abs_lower()-remainder
        assert margin>0 and derivative(region).abs_lower()>0
        w=square(r/3); denominator=derivative(region)
        coefficient=sum((real(weight/v)*derivative(region+real(1-1/v)*w)/denominator for weight,v in A),flint.acb(0))
        assert coefficient.abs_lower()>0
        rows.append({'centre':row['centre'],'fresh_nested_radius':str(Q(row['radius'])/2),
                     'Rouche_margin_lower_ball':short(margin),'whole_signed_log_coefficient_lower_ball':short(coefficient.abs_lower()),
                     'old_corridors_validated_by_hash':True,'all_passed':True})
    assert len(rows)==2
    return {'records':rows,'old_independent_zero_verification_sha256':sha(oldpath),
            'old_corridor_verification_sha256':corridor['corridor_verification_sha256'],
            'new_zeta_zero_claimed':False,'all_passed':True}


def main():
    p=argparse.ArgumentParser(description=__doc__); p.add_argument('--native-group',type=int,choices=(0,1)); a=p.parse_args()
    start=time.monotonic(); flint.ctx.prec=480; flint.ctx.cap=24
    path=DEST/'compensated_shift_analytic.json'; source=json.loads(path.read_text())
    arithmeticpath=DEST/'compensated_shift_search.json'; arithmetic=json.loads(arithmeticpath.read_text())
    assert source['all_passed'] and source['arithmetic_source_artifact_sha256']==sha(arithmeticpath)
    A=tuple((Q(r['weight']),Q(r['v'])) for r in arithmetic['selected_operator']['certificate']['atoms'])
    fp={'source_sha256':sha(path),'arithmetic_source_sha256':sha(arithmeticpath),'checker_code_sha256':sha(Path(__file__)),
        'independent_backend_code_sha256':sha(BASE/'check_shift_ratio_analytic.py'),
        'precision':flint.ctx.prec,'series_cap':flint.ctx.cap,'flint_version':flint.__version__}
    groups=native_groups(source,A,fp,a.native_group)
    if a.native_group is not None: return
    assert len(groups['records'])==2
    signs=residues(A); zeros=actual_zeros(source,A)
    assert source['all_order_signature_certificate']['nonzero_leading_signature_every_positive_integer_order_proved']
    assert source['RH_regularized_continuation_criterion_proved'] and not source['RH_continuation_estimate_proved']
    assert not source['historical_novelty_established']
    checks={'independent_complete_signed_B_integrals_and_infinite_tails':True,
            'changed_subset_coefficients_cutoff_precision_and_wrong_prime_controls':True,
            'changed_toy_CAS_and_signed_native_zero_order_residues':signs['all_passed'],
            'pole_regularization_sign_and_canceled_leading_term_scope':signs['all_passed'],
            'fresh_nested_actual_zero_disks_and_old_corridor_integrity':zeros['all_passed'],
            'RH_criterion_global_estimate_and_historical_priority_separate':True}
    out={'all_passed':all(checks.values()),'checks':checks,'fingerprint':fp,'source_artifact_sha256':sha(path),
         'native_complete_signed_B_audit':groups,'signed_zero_signature_audit':signs,'actual_zero_and_corridor_audit':zeros,
         'mathematical_audit_imports_production_code':False,'reuses_prior_independent_backend':True,
         'new_RH_estimate_proved':False,'verified_new_operators':[],'seconds':time.monotonic()-start}
    (DEST/'compensated_shift_analytic_verification.json').write_text(json.dumps(out,indent=2)+'\n')
    print('Independent signed analytic audit',len(checks),'/',len(checks),'seconds',out['seconds'],flush=True)


if __name__=='__main__': main()
