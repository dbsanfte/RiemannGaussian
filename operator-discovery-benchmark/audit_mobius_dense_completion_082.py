"""Independent082 pre-freeze producer audit on generic tiny geometry only.
No historical source/science data or frozen tests are queried. Imports producer
only in this external audit, never into the independent checker.
"""
from pathlib import Path
from fractions import Fraction as Q
import json,time,traceback
import mobius_dense_completion_082 as P
import check_mobius_dense_completion_082 as C

def fixture(memory,linear=False):
    return dict(schema='dense-divisor-completion-v1',kernel=[{'divisor':1,'weight':'1/3'},{'divisor':3,'weight':'-1/2'}],memory=memory,rays=[]if memory==1 else [{'a':['1']+['-1']*(memory-1),'weight':'1/4'}],drift_multiplier='3/2',profiles=[{'scale':'2/3','eta':'1'if linear else '17/31'}],theta=[['1/2']*(memory+1)],gram_weights=['1/4']*(memory+2))

def audit():
    cases=[]
    for depth in [1,2,3]:
        for linear in [False,True]:
            for u in [1,19,53]:
                p=fixture(depth,linear);model=P.build_model(p,u);ind=C.build_model(p,u)
                actual=[tuple(Q(int(v),model['denominator'])for v in row)for row in model['features']]
                assert actual==list(ind['features'])
                assert list(map(int,model['counts']))==list(ind['counts'])
                cert=P.upper_certificate(model);upper=C.verify_certificate(p,u,cert)
                assert upper['status']=='VERIFIED_FINITE_DENSE_UPPER_BOUND',upper
                G=model['group_count'];lam=[Q(1,2)]*G;nu=[Q(-1,3)if (g+h)%2 else Q(1,3)for g in range(G)for h in range(g+1,G)]
                dual=P.dual_certificate(model,lam,nu);lower=C.verify_price_dual(p,u,dual)
                assert lower['status']=='VERIFIED_FINITE_GRAMMAR_PRICE_LOWER_BOUND',lower
                assert Q(dual['lower_bound'])<=Q(cert['price'])
                cases.append(dict(memory=depth,linear=linear,u=u,groups=G,price=cert['price'],lower_bound=dual['lower_bound'],independent_upper_status=upper['status'],independent_dual_status=lower['status']))
    optimizations=[]
    for linear in [False,True]:
        p=fixture(2,linear);fit=P.optimize(p,37,time_limit=20)
        assert fit['status']=='LP_PROPOSAL',fit
        upper=C.verify_certificate(fit['program'],37,fit['certificate']);lower=C.verify_price_dual(fit['program'],37,fit['dual'])
        assert upper['status']=='VERIFIED_FINITE_DENSE_UPPER_BOUND',upper
        assert lower['status']=='VERIFIED_FINITE_GRAMMAR_PRICE_LOWER_BOUND',lower
        assert Q(fit['exact_gap'])==Q(fit['certificate']['price'])-Q(fit['dual']['lower_bound'])>=0
        optimizations.append(dict(linear=linear,solver_status=fit['solver_status'],price=fit['certificate']['price'],lower_bound=fit['dual']['lower_bound'],gap=fit['exact_gap']))
    return dict(status='PASS',tiny_group_upper_dual_cases=cases,synthetic_lp_proposals=optimizations,scientific_source_queries=False,old_tests_run=False,checker_frozen_tests_replayed=False,hashes_used=False,uniform_original_source_bound_proved=False,RH_proved=False,remaining_generic_resource_concerns=['Unchecked Fraction growth in producer drift_matrix','Fixed bytes per rational in small_dual_contraction/public dual inputs'],scope='Finite generic source algebra audit, not historical scientific outcomes or uniform obstruction certificate.')

def audit_postfix_resources():
    from unittest.mock import patch
    p=fixture(1);p['rays']=[{'a':['1'],'weight':str(Q(1,2**4000+2*i+1))}for i in range(8)]
    with patch.object(P.np,'ones',side_effect=AssertionError('source allocation must follow drift denominator gate'))as allocation:
        try:P.build_model(p,19)
        except P.ResourceLimit as e:drift_reason=str(e)
        else:raise AssertionError('unbounded drift denominator accepted')
        allocation.assert_not_called()
    model=P.build_model(fixture(2),53);G=model['group_count'];edges=G*(G-1)//2
    lam=[Q(1,2)]*G;nu=[Q(1,2**4000+2*i+1)for i in range(edges)]
    with patch.object(P,'fmpq_mat',side_effect=AssertionError('native matrix must follow aggregate dual gate'))as allocation:
        try:P.dual_certificate(model,lam,nu)
        except P.ResourceLimit as e:dual_reason=str(e)
        else:raise AssertionError('unbounded dual denominator accepted')
        allocation.assert_not_called()
    with patch.object(P,'fmpq_mat',side_effect=AssertionError('canonical dual admission must precede native matrix'))as allocation:
        try:P.dual_certificate(model,lam,['2/4']*edges)
        except ValueError as e:canonical_reason=str(e)
        else:raise AssertionError('noncanonical dual accepted')
        allocation.assert_not_called()
    return dict(status='PASS',scope='Targeted post-fix generic resource audit only; no repeated source science or prior mathematical tests.',drift_before_numpy_gate=drift_reason,dual_before_native_gate=dual_reason,canonical_dual_gate=canonical_reason,remaining_previously_reported_resource_blockers=[],scientific_source_queries=False,old_tests_run=False,hashes_used=False)

if __name__=='__main__':
    start=time.monotonic()
    import sys
    try:r=audit_postfix_resources()if '--postfix-resources'in sys.argv else audit()
    except Exception:r=dict(status='FAIL',traceback=traceback.format_exc())
    r.update(elapsed_seconds=time.monotonic()-start)
    p=Path('mobius_dense_completion_independent_review_082.json')
    if p.exists():p=Path('mobius_dense_completion_independent_review_082_attempt_'+str(time.time_ns())+'.json')
    with p.open('x')as f:json.dump(r,f,indent=2,sort_keys=True);f.write('\n')
    print(p,r['status']);print(r.get('traceback',''))
