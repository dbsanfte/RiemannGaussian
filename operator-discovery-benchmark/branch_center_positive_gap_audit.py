#!/usr/bin/env python3
"""Independent positive-gap costs from the already frozen complete candidate set.

No producer math imports, new candidates, selection, fitted constants or cases.
The native derivatives use local Taylor composition; tail coefficients use
an independently formed differential polynomial. Core source/data stay frozen.
"""
from fractions import Fraction as Q
from math import factorial,comb,ceil,floor
from functools import lru_cache
from pathlib import Path
import argparse,flint
from stable_scale_report import BASE,read,sha,digest
from check_mellin_kernels import a,powq,put,tight_overlap
from check_branch_centers import scalar_c


@lru_cache(maxsize=None)
def continued(q):
    q=Q(q);flint.ctx.prec=768;s=flint.acb(a(Q(5,8)),16);N=128;M=24;L=a(N).log();old=flint.ctx.cap;flint.ctx.cap=2*M+1
    try:
        x=flint.acb_series([N,1],prec=2*M+1);logx=x.log();f=(-s*logx+a(q)*logx.log()).exp();der=[f[j]*factorial(j) for j in range(2*M+1)]
    finally:flint.ctx.cap=old
    value=sum((( -s*a(n).log()).exp()*powq(a(n).log(),q) for n in range(2,N+1)),flint.acb(0));value+=((s-1)*L).gamma_upper(a(q+1))*(s-1).pow(-a(q+1))-der[0]/2
    for k in range(1,M+1):value-=flint.arb.bernoulli(2*k)*der[2*k-1]/factorial(2*k)
    # product_(h=0..r-1)(z-s-h) acting on (log t)^q, rather
    # than the producer's joint recurrence for derivative coefficients.
    P=[flint.acb(1)]
    for h in range(2*M):
        new=[flint.acb(0) for _ in range(len(P)+1)]
        for j,c in enumerate(P):new[j]-=(s+h)*c;new[j+1]+=c
        P=new
    falling=Q(1);norm=flint.arb(0)
    for j,c in enumerate(P):
        norm+=abs(c)*a(abs(falling))/L**j;falling*=q-j
    rate=s.real+2*M-1;error=2*a(2*M).zeta()/(2*flint.arb.pi())**(2*M)*norm*(rate*L).gamma_upper(a(q+1))/powq(rate,q+1)
    return value+flint.acb(flint.arb(0,error.upper()),flint.arb(0,error.upper()))


def main(d):
    spec=read(d/'protocol.json');batch=read(d/'candidate_batch.json');validation=read(d/'validation.json');verification=read(d/'verification.json');assert verification['all_passed'];pids={p['id']:p['program'] for p in batch['programs']}
    for n,h in spec['code_sha256'].items():assert sha(BASE/n)==h
    pin={n:sha(d/n) for n in ['protocol.json','candidate_batch.json','validation.json','archive.json','seal.json','final_cases.json','final_constants.json','final_evaluation.json','verification.json','summary.json','report.txt']}
    q=max(spec['training_levels']);s=flint.acb(a(Q(5,8)),16);operator_cache={};counts={'independent_complete_Taylor_composition_profiles':0,'independent_positive_gap_validation_costs':0,'independent_positive_gap_promotion_scores':0};missing=0
    for pid,p in pids.items():
        atoms=[(Q(b),Q(w)) for b,w in p['atoms']]
        for m in range(len(atoms)):
            moment=sum((w*b**m for b,w in atoms),Q(0))
            if moment:break
        h=moment/Q(q)**m;F=sum((a(w)*continued(str(b/q)) for b,w in atoms),flint.acb(0))/a(h);D=2**160;mod=abs(F);low=floor(Q(mod.lower().str(250,radius=False))*D);high=floor(Q(mod.upper().str(250,radius=False))*D)
        assert low==high and low>1;lower=a(Q(low-1,D));K=sum((a(abs(w))*4*a(2).log()*scalar_c(b/q)/a(1-b/q) for b,w in atoms),flint.arb(0))/a(abs(h));operator_cache[pid]=(lower,K)
    counts['independent_complete_Taylor_composition_profiles']=continued.cache_info().currsize
    def cost(pid,hyp,record):
        lower,K=operator_cache[pid];theta=a(Q(hyp['eta']))+a(Q(hyp['epsilon']))/powq(a(q),Q(hyp['nu']));gap=s.real-theta
        if record['missing']:
            if record['reason']=='no_positive_mellin_gap':assert not gap>0
            return False
        assert gap>0;D=ceil(Q(hyp['log_degree']));base=(flint.arb.const_e()+1).log();I=sum((a(comb(D,j))*base**(D-j)*factorial(j)/gap**(j+1) for j in range(D+1)),flint.arb(0));C=a(Q(str(record['C_q'])));value=abs(s)*(K/(abs(s)*abs(s.imag))+C*I+K/s.real)/lower
        tight_overlap(record['gap_ball'],gap);tight_overlap(record['gap_integral_ball'],I);tight_overlap(record['value_ball'],value);assert abs(float(value.upper())-record['value'])<=1e-10*(1+record['value']);assert record['conditional_on_unproved_global_estimate'];return True
    for row in validation['estimates']:
        if cost(row['program_id'],row['hypothesis'],row['charged_observer_cost']):counts['independent_positive_gap_validation_costs']+=1
        else:missing+=1
    for row in batch['pre_promotion_scores']:
        if cost(row['program_id'],spec['promotion_score_target'],row['cost']):counts['independent_positive_gap_promotion_scores']+=1
    assert counts['independent_positive_gap_validation_costs']>0 and counts['independent_positive_gap_promotion_scores']>0
    for n,h in pin.items():assert sha(d/n)==h
    result={'all_passed':True,'run_directory':str(d),'source_sha256':pin,'auditor_sha256':sha(BASE/'branch_center_positive_gap_audit.py'),'native_counts':counts,'missing_or_nonpositive_gap_records':missing,
        'all_normalizations_cut_centers_real_scale_guards_and_gap_costs_included':True,'no_candidate_or_selection_changes':True,'no_new_case_or_fit_constant':True,'mathematical_audit_imports_production_code':False,'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False}
    destination=d/'positive_gap_observer_audit.json'
    if destination.exists():raise FileExistsError('Keep the completed audit')
    put(destination,result);print('Independent positive-gap observer audit passed',counts,flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--run-dir',type=Path,required=True);main(p.parse_args().run_dir.resolve())
