"""Independent producer integration audit083, generic tiny geometry only.
Producer is imported in this external audit, never in independent checker.
No historical science/source signs, hashes, or old tests are replayed.
"""
from fractions import Fraction as Q
from pathlib import Path
import json,time,traceback
import mobius_coupled_completion_083 as P
import check_mobius_coupled_completion_083 as C

def fixture(memory,balance):
    def cut(a,eta,beta,comp=False):return dict(scale=a,n_exponent=eta,u_exponent=beta,complement=comp,unit_balance=balance)
    return dict(schema='coupled-divisor-completion-v1',kernel=[dict(divisor=1,weight='1/3'),dict(divisor=2,weight='-1/2')],memory=memory,rays=[]if memory==1 else [dict(a=['1']+['-1']*(memory-1),weight='1/4')],drift_multiplier='3/2',coupled_terms=[dict(cut=cut('1/2','17/31','0'),weight=dict(kind='one',arithmetic='all'),theta='-1/3'),dict(cut=cut('2/3','-1','1',True),weight=dict(kind='product',arithmetic='prime',i=0,j=memory),theta='1/2'),dict(cut=cut('1','0','1/2'),weight=dict(kind='band',arithmetic='composite',left='1/5',right='4/5'),theta='2/3')],gram_weights=['1/4']+['0']*memory)

def audit():
    cases=[]
    for memory in [1,2,3]:
        for balance in [False,True]:
            for u in [1,5,23]:
                p=fixture(memory,balance);model=P.build_model(p,u);ind=C.build_model(p,u);den=model['denominator']
                assert tuple(map(int,model['coordinates']))==ind['coordinates']
                assert [tuple(Q(int(x),den)for x in row)for row in model['features']]==list(ind['features'])
                assert [tuple(map(int,row))for row in model['cuts']]==list(ind['cuts'])
                assert [tuple(Q(int(x),den*den)for x in row)for row in model['weights']]==list(ind['weights'])
                cert,diag=P.upper_certificate(model);upper=C.verify_certificate(p,u,cert);assert upper['status']=='VERIFIED_FINITE_COUPLED_UPPER_BOUND',upper
                G=model['squarefree_count'];nu=[Q(-2)if (g+h)%2 else Q(1,3)for g in range(G)for h in range(g+1,G)]
                dual=P.dual_certificate(model,nu);lower=C.verify_price_dual(p,u,dual);assert lower['status']=='VERIFIED_FINITE_COUPLED_PRICE_LOWER_BOUND',lower
                assert Q(dual['lower_bound'])<=Q(cert['price'])
                cases.append(dict(memory=memory,unit_balance=balance,u=u,coordinates=G,price=cert['price'],lower_bound=dual['lower_bound'],diagnostics=diag,upper_status=upper['status'],dual_status=lower['status']))
    fits=[]
    for balance in [False,True]:
        p=fixture(2,balance);fit=P.optimize(p,23,time_limit=20);assert fit['status']=='LP_PROPOSAL',fit
        upper=C.verify_certificate(fit['program'],23,fit['certificate']);lower=C.verify_price_dual(fit['program'],23,fit['dual'])
        assert upper['status']=='VERIFIED_FINITE_COUPLED_UPPER_BOUND',upper
        assert lower['status']=='VERIFIED_FINITE_COUPLED_PRICE_LOWER_BOUND',lower
        assert Q(fit['exact_gap'])==Q(fit['certificate']['price'])-Q(fit['dual']['lower_bound'])>=0
        fits.append(dict(unit_balance=balance,price=fit['certificate']['price'],lower_bound=fit['dual']['lower_bound'],gap=fit['exact_gap'],solver_status=fit['solver_status']))
    return dict(status='PASS',tiny_full_coordinate_upper_dual_cases=cases,synthetic_lp_proposals=fits,resource_issues_reported=['Cumulative resident model/input/native scratch reserve','Dense dual matrix versus edge-only reservation','Public coupled_basis should prospectively gate its own allocation'],scientific_source_queries=False,old_tests_run=False,hashes_used=False,uniform_growth_proved=False,uniform_original_source_bound_proved=False,RH_proved=False,scope='Math/integration PASS; reported generic resource issues require separate root fixes and targeted audit.')
if __name__=='__main__':
    start=time.monotonic()
    try:r=audit()
    except Exception:r=dict(status='FAIL',traceback=traceback.format_exc())
    r['elapsed_seconds']=time.monotonic()-start
    p=Path('mobius_coupled_completion_independent_review_083.json')
    if p.exists():p=Path('mobius_coupled_completion_independent_review_083_attempt_'+str(time.time_ns())+'.json')
    with p.open('x')as f:json.dump(r,f,indent=2,sort_keys=True);f.write('\n')
    print(p,r['status']);print(r.get('traceback',''))
