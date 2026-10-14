#!/usr/bin/env python3
"""Frozen automatic certificate attempts for every recorded signed-gap estimate.

This extends a guided operator family. It is separate from the general frozen
autonomous discovery pilot. Case thresholds depend on proposed bounds; no
desired operator/estimate is asserted in this search path.
"""
from fractions import Fraction as Q
from math import factorial
from pathlib import Path
import hashlib
import json
import time
import flint
import sympy as sp

from compensated_global_gap_probe import signed_homogeneous, polya
from check_shift_ratio import B as independent_counterexample_value

BASE=Path(__file__).resolve().parent
DEST=BASE/'compensated-shift-results/family-gap-run-001'


def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()


def canonical(x): return json.dumps(x,sort_keys=True,separators=(',',':'))


def digest(x): return hashlib.sha256(canonical(x).encode()).hexdigest()


def write(p,x): p.write_text(json.dumps(x,indent=2)+'\n')


def real(q): q=Q(q); return flint.arb(q.numerator)/q.denominator


def uniform(v,m):
    denominator=Q(1); rho=v/(1-v)
    for j in range(1,m+1): denominator*=m*rho+j
    return Q(factorial(m))/(1-v)/denominator


def h(t,A): return sum((w*t/(v+(1-v)*t) for w,v in A),Q(0))


def mu(k): return int(sp.mobius(k))


def attempt(candidate,protocol,fingerprint):
    A=[(Q(w),Q(v)) for w,v in candidate['atoms']]; gamma=Q(candidate['proposed_gap'])
    # Verify any failure at the recorded peak by a fresh rigorous sparse query.
    n=candidate['finite_peak_index']
    actual=sum((real(w)*independent_counterexample_value(n,v) for w,v in A),flint.arb(0))
    if actual.abs_lower()>real(gamma):
        return {'candidate':candidate,'status':'counterexample_found','counterexample_index':n,
                'counterexample_ball':actual.str(35),'all_scale_bound_proved':False,
                'query_provenance':'independent factor/subset query; not a factor-free complete prefix claim'}
    tails=[]; g1=int(max(abs(w)*(1-v) for w,v in A)//gamma)+1
    tails.append({'omega':1,'g_at_least':g1,'bound':str(max(abs(w)*(1-v) for w,v in A)/g1)})
    powers=[]
    for e in range(2,g1):
        value=sum((Q(mu(k),k)*(1-h(1-Q(k,e),A)) for k in sp.divisors(e)),Q(0))
        powers.append({'exponent':e,'coefficient':str(value)})
        if abs(value)>gamma:
            return {'candidate':candidate,'status':'counterexample_found','counterexample_index':str(2**e),
                    'exact_prime_power_coefficient':str(value),'all_scale_bound_proved':False}
    max_m=protocol['resources']['maximum_factor_tail_search']
    m0=next((m for m in range(3,max_m+1) if max(abs(w)*uniform(v,m) for w,v in A)<gamma),None)
    if m0 is None:
        return {'candidate':candidate,'status':'numerical_lead','reason':'uniform factor-count tail not closed within resource limit',
                'all_scale_bound_proved':False}
    tails.append({'omega_at_least':m0,'g_at_least':1,'bound':str(max(abs(w)*uniform(v,m0) for w,v in A))})
    regions=[]
    for m in range(2,m0):
        weighted=max(abs(w)*uniform(v,m) for w,v in A)
        g0=int(weighted//gamma)+1
        tails.append({'omega':m,'g_at_least':g0,'bound':str(weighted/g0)})
        for g in range(1,g0):
            if m==2 and g==1:
                regions.append({'omega':2,'g':1,'repeated_exponent':False,
                                'status':'exact_two_prime_pair_certificate','bound':candidate['proposed_gap']})
                repeated=True
            else: repeated=False
            variables=sp.symbols(' '.join(['x'+str(i) for i in range(m)]+['slack']),nonnegative=True)
            shares=[variables[i]/2 if repeated and i==0 else variables[i] for i in range(m)]
            degree=2*(2**m-1)*sum(mu(k)!=0 for k in sp.divisors(g))
            region={'omega':m,'g':g,'repeated_exponent':repeated,'barycentric_variables':list(map(str,variables))}
            if len(variables)>protocol['resources']['maximum_barycentric_dimension'] or degree>protocol['resources']['maximum_denominator_degree']:
                regions.append({**region,'status':'unsupported_by_resource_budget','predicted_degree':degree}); continue
            name=candidate['id']+'_m'+str(m)+'_g'+str(g)+'_r'+str(int(repeated))+'.json'
            component=DEST/name
            old=json.loads(component.read_text()) if component.exists() else {}
            if old.get('fingerprint')==fingerprint:
                regions.append(old['region']); continue
            atoms=[(sp.Rational(w.numerator,w.denominator),sp.Rational(v.numerator,v.denominator)) for w,v in A]
            H,D=signed_homogeneous(variables,shares,g,atoms)
            sides=[]
            for sign in (1,-1):
                P=sp.Rational(gamma.numerator,gamma.denominator)*D+sign*H
                sides.append({'sign':sign,'certificate':polya(P,protocol['resources']['maximum_polya_elevations'])})
            ok=all(r['certificate']['status']=='universal_nonnegative_polynomial_certified' for r in sides)
            region.update({'status':'universal_simplex_bound_certified' if ok else 'unsupported_by_bounded_polya_search',
                           'sides':sides,'denominator_degree':D.total_degree(),
                           'component_file':name})
            write(component,{'fingerprint':fingerprint,'region':region}); regions.append(region)
    complete=all(r['status'] in ('universal_simplex_bound_certified','exact_two_prime_pair_certificate') for r in regions)
    return {'candidate':candidate,'status':'universal_arithmetic_theorem_proved' if complete else 'numerical_lead',
            'uniform_tails':tails,'prime_power_regions':powers,'finite_simplex_regions':regions,
            'all_scale_bound_proved':complete,'factor_count_tail':m0,
            'finite_peak_query_ball':actual.str(35),'case_partition_complete_if_all_regions_pass':True,
            'new_prime_distribution_or_RH_estimate_proved':False,'historical_novelty_established':False}


def main():
    started=time.monotonic(); flint.ctx.prec=384
    sourcepath=BASE/'compensated-shift-results/compensated_shift_search.json'; source=json.loads(sourcepath.read_text())
    DEST.mkdir(parents=True,exist_ok=True)
    protocol={'schema':1,'mode':'guided_family_automatic_certificate_search',
              'source_sha256':sha(sourcepath),'search_code_sha256':sha(Path(__file__)),
              'polynomial_backend_code_sha256':sha(BASE/'compensated_global_gap_probe.py'),
              'counterexample_backend_code_sha256':sha(BASE/'check_shift_ratio.py'),
              'resources':{'maximum_factor_tail_search':12,'maximum_barycentric_dimension':4,
                           'maximum_denominator_degree':30,'maximum_polya_elevations':24},
              'rules':'test every recorded estimate; derive omega/g thresholds from uniform atomic norms; certify all residual rational simplex cases or retain a lead',
              'input_filter':'all recorded pairs, including known finite-failure controls; no favored parameter',
              'novelty_and_RH_claims':'separate; no theorem count implies new operator or distribution estimate',
              'prime_oracle_access':'sparse factor/subset evaluator only for explicit counterexamples; operator producer itself has none',
              'model_or_literature_calls_during_attempts':False}
    path=DEST/'protocol.json'
    if path.exists():
        assert json.loads(path.read_text())==protocol,'use a new family run directory after changing the frozen rules'
    else: write(path,protocol)
    candidates=[]
    for row in source['pair_compensators']:
        c={'left':row['left'],'right':row['right'],'atoms':[[a['weight'],a['v']] for a in row['certificate']['atoms']],
           'proposed_gap':row['fitted_global_gap'],'finite_peak_index':row['maximum_index'],
           'ordinary_zero_all_order_gate':row['certificate']['root_signature_certificate']['nonzero_leading_signature_every_positive_integer_order_proved']}
        c['id']=digest(c)[:16]; candidates.append(c)
    batch={'protocol_sha256':digest(protocol),'candidates':candidates,'frozen_before_certificate_outcomes':True}
    path=DEST/'candidate_batch.json'
    if path.exists(): assert json.loads(path.read_text())==batch
    else: write(path,batch)
    fp={'protocol_sha256':digest(protocol),'candidate_batch_sha256':digest(batch),'flint_version':flint.__version__,'sympy_version':sp.__version__}
    rows=[]
    for c in candidates:
        path=DEST/(c['id']+'_result.json'); old=json.loads(path.read_text()) if path.exists() else {}
        if old.get('fingerprint')==fp:
            result=old['result']
        else:
            result=attempt(c,protocol,fp); write(path,{'fingerprint':fp,'result':result})
        rows.append(result); print('Automatic family bound',c['left'],c['right'],c['proposed_gap'],result['status'],flush=True)
    from collections import Counter
    proved=[r for r in rows if r['all_scale_bound_proved'] and r['candidate']['ordinary_zero_all_order_gate']]
    selected=min(proved,key=lambda r:Q(r['candidate']['proposed_gap'])) if proved else None
    out={'protocol':protocol,'fingerprint':fp,'records':rows,'status_counts':dict(Counter(r['status'] for r in rows)),
         'selection_rule':'smallest proved global composite gap among candidates with certified nonzero leading signature at every integer zero order',
         'selected_operator':selected,'all_scale_verified_candidates':len(proved),'independent_audit_required':True,
         'new_RH_estimate_proved':False,'historical_novelty_established':False,'verified_new_operators':[],
         'seconds':time.monotonic()-started}
    write(DEST/'family_gap_search.json',out)
    print('Family certificate search completed',out['status_counts'],'seconds',out['seconds'],flush=True)


if __name__=='__main__': main()
