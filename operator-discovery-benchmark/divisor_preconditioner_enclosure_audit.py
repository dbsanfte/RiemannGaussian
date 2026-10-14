#!/usr/bin/env python3
"""Post-run enclosure strengthening, with no reselection or producer imports."""
import argparse,json
from fractions import Fraction as Q
from math import factorial,comb
from pathlib import Path
import flint
from stable_scale_report import BASE,read,sha
from check_mellin_kernels import a


def audit(directory):
    d=Path(directory).resolve();v=read(d/'verification.json');assert v['all_passed'] and not v['mathematical_audit_imports_production_code'];batch=read(d/'candidate_batch.json');spec=read(d/'protocol.json')
    for n,h in spec['code_sha256'].items():assert sha(BASE/n)==h
    flint.ctx.prec=1280;K=max(map(int,batch['completed_preconditioners']));eps=a(Q(1,2**440));corners=[flint.acb(a(Q(3,4)),a(Q(-1,4))),flint.acb(a(Q(5,4)),a(Q(-1,4))),flint.acb(a(Q(5,4)),a(Q(1,4))),flint.acb(a(Q(3,4)),a(Q(1,4)))];G=[]
    for j in range(K):
        value=flint.acb(0)
        for left,right in zip(corners,corners[1:]+corners[:1]):
            value+=flint.acb.integral(lambda z,analytic:(z.zeta()-1/(z-1))/(z-1)**(j+1),left,right,abs_tol=eps,rel_tol=eps,depth_limit=50,eval_limit=300000)
        value*=(-1)**j*factorial(j)/flint.acb(0,2*flint.arb.pi());assert value.is_finite() and value.imag.contains(0);G.append(value.real)
    records=[];counts={'harmonic_constant_enclosures':0,'polynomial_coefficient_enclosures':0,'constant_term_enclosures':0,'independent_global_guard_checks':0}
    for key,cert in batch['completed_preconditioners'].items():
        k=int(key)
        for saved,exact in zip(cert['gamma_constants'],G[:k]):assert flint.arb(saved).contains(exact);counts['harmonic_constant_enclosures']+=1
        # Principal part of (-1)^k*zeta^(k)/(s*zeta), computed by
        # independent Laurent inversion, not the harmonic constraint solver.
        Z=[flint.arb(1)]+[(-1)**j*G[j]/factorial(j) for j in range(k)];A=[Z[j]+(Z[j-1] if j else 0) for j in range(k)];inverse=[flint.arb(1)]
        for j in range(1,k):inverse.append(-sum((A[h]*inverse[j-h] for h in range(1,j+1)),flint.arb(0)))
        P=[factorial(k)*inverse[k-r-1]/factorial(r) for r in range(k)];b=a((-1)**k*factorial(k))-sum((P[r]*(-1)**r*G[r] for r in range(k)),flint.arb(0))
        for saved,exact in zip(cert['polynomial_coefficients'],P):assert flint.arb(saved).contains(exact);counts['polynomial_coefficient_enclosures']+=1
        assert flint.arb(cert['constant_term']).contains(b);counts['constant_term_enclosures']+=1
        B=[Q(2*factorial(j))*sum((Q(1,factorial(h)) for h in range(j+1)),Q(0)) for j in range(k)];C=[sum((comb(r,j)*B[j] for j in range(r+1)),Q(0)) for r in range(k)]
        guard=a(factorial(k)+1)+abs(b)+sum((abs(P[r])*a(C[r]) for r in range(k)),flint.arb(0));assert a(cert['residual_constant'])>guard;counts['independent_global_guard_checks']+=1
        records.append({'order':k,'exact_constraint_operator_recorded_enclosures_contain_sharper_independent_values':True,
            'polynomial_ball_radii':[str(p.rad()) for p in P],'constant_ball_radius':str(b.rad()),'all_scale_guard_verified':True})
    result={'phase':'post_run_independent_enclosure_strengthening','all_passed':True,'source_protocol_sha256':sha(d/'protocol.json'),'source_batch_sha256':sha(d/'candidate_batch.json'),
        'source_archive_sha256':sha(d/'archive.json'),'source_final_sha256':sha(d/'final_evaluation.json'),'source_verification_sha256':sha(d/'verification.json'),
        'auditor_sha256':sha(BASE/'divisor_preconditioner_enclosure_audit.py'),'mathematical_audit_imports_production_code':False,
        'native_precision':1280,'contour_tolerance_binary_power':440,'records':records,'counts':counts,
        'recorded_balls_are_enclosures_of_exact_constraint_defined_parameters':True,'selection_fitted_constants_and_final_cases_changed':False,'new_fresh_discovery_claim':False,
        'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False}
    output=d/'enclosure_strengthening.json'
    if output.exists():raise FileExistsError('Retain the existing strengthening audit')
    output.write_text(json.dumps(result,indent=2)+'\n');print('All exact completed-operator coefficient enclosures contain sharper independent contour/Laurent values.');print(counts)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--run-dir',type=Path,required=True);audit(p.parse_args().run_dir.resolve())
