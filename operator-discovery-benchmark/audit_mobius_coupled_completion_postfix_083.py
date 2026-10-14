"""Independent targeted post-fix integration audit; tiny synthetic geometry only."""
import json,time,traceback
from pathlib import Path
from fractions import Fraction as Q
import audit_mobius_coupled_completion_083 as A
import mobius_coupled_completion_083 as P
import check_mobius_coupled_completion_083 as C

def audit():
    cases=[]
    for memory in (1,2,3):
        for u in (1,2,6,23):
            p=A.fixture(memory,True);p['prime_anchor']=True
            model=P.build_model(p,u);cert,diag=P.upper_certificate(model)
            v=C.verify_certificate(p,u,cert);assert v['status']=='VERIFIED_FINITE_COUPLED_UPPER_BOUND',v
            n=model['price_dimension'];nu=[Q(1,3)if(g+h)%2 else Q(-2)for g in range(n)for h in range(g+1,n)]
            dual=P.dual_certificate(model,nu);v=C.verify_price_dual(p,u,dual);assert v['status']=='VERIFIED_FINITE_COUPLED_PRICE_LOWER_BOUND',v
            cases.append(dict(memory=memory,u=u,price=cert['price'],lower=dual['lower_bound'],effective_dimension=n))
    p=A.fixture(2,True);p['prime_anchor']=True
    size=len(p['coupled_terms'])+len(p['gram_weights'])
    rows=[['1','-1']+['0']*(size-2)];eq=dict(rows=rows,rhs=['1/3'])
    fit=P.optimize(p,23,time_limit=20,equalities=eq);assert fit['status']=='LP_PROPOSAL',fit
    params=[Q(t['theta'])for t in fit['program']['coupled_terms']]+list(map(Q,fit['program']['gram_weights']))
    assert params[0]-params[1]==Q(1,3)
    assert C.verify_certificate(fit['program'],23,fit['certificate'])['status']=='VERIFIED_FINITE_COUPLED_UPPER_BOUND'
    assert C.verify_price_dual(fit['program'],23,fit['dual'])['status']=='VERIFIED_FINITE_COUPLED_PRICE_LOWER_BOUND'
    # Public basis and native dual gates must sum resident and scratch before allocation.
    gates=[]
    for action in ('basis','dual'):
        model=P.build_model(p,23);model['extra_resident_bytes']=4*1024**3
        try:
            if action=='basis':P.coupled_basis(model,0)
            else:P.dual_certificate(model,[Q(0)]*(model['price_dimension']*(model['price_dimension']-1)//2))
        except ValueError:gates.append(action)
        else:raise AssertionError('resident gate absent: '+action)
    return dict(status='PASS',anchor_cases=cases,affine_exact_equation_verified=True,affine_price=fit['certificate']['price'],resident_gates=gates,unconstrained_dual_only=True,unknown_composite_signs_used=False,observed_full_source_values_used=False,scientific_source_queries=False,old_tests_run=False,hashes_used=False,uniform_full_price_proved=False,uniform_source_bound_proved=False,RH_proved=False)
if __name__=='__main__':
    started=time.monotonic()
    try:r=audit()
    except Exception:r=dict(status='FAIL',traceback=traceback.format_exc())
    r['elapsed_seconds']=time.monotonic()-started
    path=Path('mobius_coupled_completion_postfix_independent_review_083.json')
    if path.exists():path=Path('mobius_coupled_completion_postfix_independent_review_083_attempt_'+str(time.time_ns())+'.json')
    path.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n');print(path,r['status']);print(r.get('traceback',''))
