"""External independent producer audit084; generic tiny geometry, no old science."""
import json,time,traceback
from pathlib import Path
from fractions import Fraction as Q
from unittest.mock import patch
import numpy as np
import mobius_coupled_square_084 as P
import mobius_rh_target_084 as H
import check_mobius_coupled_square_084 as C

def fixture(anchor=True):
    weight=dict(kind='product',arithmetic='all',i=0,j=0)
    def term(comp):return dict(cut=dict(scale='1',n_exponent='1',u_exponent='0',complement=comp,unit_balance=True),weight=dict(weight),theta='5/2')
    return dict(schema='coupled-divisor-completion-v1',kernel=[dict(divisor=4,weight='-1'),dict(divisor=5,weight='1'),dict(divisor=8,weight='1'),dict(divisor=10,weight='-1')],memory=1,rays=[],drift_multiplier='3/2',coupled_terms=[term(False),term(True)],gram_weights=['1/4','1/3'],prime_anchor=anchor)

def audit():
    cases=[]
    for anchor in (False,True):
        for u in (1,24,53):
            p=fixture(anchor);model=P.B.build_model(p,u);outer=P.O.synthesize(p)['certificate'];n=model['price_dimension'];rows=[[(-1)**i]for i in range(n)]
            cert,diag=P.certificate(model,8,rows);v=C.verify_certificate(p,u,outer,cert);assert v['status']=='VERIFIED_FINITE_COUPLED_SQUARE_BOUND',v
            lam=[Q(1,7),Q(-2,5),Q(3,11)];dual=P.dual_certificate(model,2,rows,lam);v=C.verify_dual(p,u,outer,dual);assert v['status']=='VERIFIED_FINITE_COUPLED_SQUARE_GRAMMAR_LOWER_BOUND',v
            raw=P.B.project_native(model,P.R.raw_remainder(model));base=P.native_base(model)
            for k,t in enumerate(model['program']['coupled_terms']):base+=P.native_template(model,k)*P.fmpq(t['theta'].numerator,t['theta'].denominator)
            assert base==raw
            cases.append(dict(anchor=anchor,u=u,price=cert['price'],lower=dual['lower_bound'],native_affine_identity=True))
    solve=P.solve(fixture(),53,optimize_operator=True,time_limit=10);assert solve['status']=='EXACT_SQUARE_PROPOSAL',solve
    assert C.verify_certificate(solve['program'],53,solve['outer_certificate'],solve['certificate'])['status']=='VERIFIED_FINITE_COUPLED_SQUARE_BOUND'
    assert C.verify_dual(solve['program'],53,solve['outer_certificate'],solve['dual'])['status']=='VERIFIED_FINITE_COUPLED_SQUARE_GRAMMAR_LOWER_BOUND'
    inverse=dict(schema='two-dilation-source-inverse-v1',base_divisor=4,ratios=['1/2','4/5'],extra=None)
    target=H.compile_target(fixture(),inverse);assert target['RH_proved']is False and target['arithmetic_leaf_status']=='UNPAID'
    model=P.B.build_model(fixture(),53);model['extra_resident_bytes']=4*1024**3
    try:P.certificate(model,1,[[]for _ in range(model['price_dimension'])])
    except ValueError:pass
    else:raise AssertionError('cumulative exactfactor gate absent')
    oversized=np.zeros((513,513))
    with patch.object(P.np.linalg,'eigh',side_effect=AssertionError('oversized helper reached native eigen allocation')):
        try:P.factor_from_psd(oversized)
        except ValueError:pass
        else:raise AssertionError('oversized helper accepted')
    return dict(status='PASS',tiny_primal_dual_cases=cases,exact_scs_proposal_independently_admitted=True,exact_native_affine_identity=True,resource_cumulative_and_public_factor_gate=True,rh_target_conditional_only=True,scientific_source_queries=False,old_tests_run=False,hashes_used=False,uniform_source_bound_proved=False,RH_proved=False)
def audit_resources_only():
    """Affected public-helper regression only; no prior math/SCS replay."""
    with patch.object(P.np.linalg,'eigh',side_effect=AssertionError('must reject before eigen')):
        for matrix,bits in [(np.zeros((513,513)),24),(np.zeros((1,1)),True)]:
            try:P.factor_from_psd(matrix,bits)
            except ValueError:pass
            else:raise AssertionError('public factor gate absent')
        m=P.B.OLD.Meter();m.limit=1
        try:P.factor_from_psd(np.zeros((2,2)),meter=m)
        except ValueError:pass
        else:raise AssertionError('public work gate absent')
    return dict(status='PASS',scope='Affected public factor/resource regression only',scientific_source_queries=False,old_tests_run=False,hashes_used=False)

if __name__=='__main__':
    started=time.monotonic()
    import sys
    try:r=audit_resources_only()if "--resources-only"in sys.argv else audit()
    except Exception:r=dict(status='FAIL',traceback=traceback.format_exc(),scientific_source_queries=False,old_tests_run=False,hashes_used=False)
    r['elapsed_seconds']=time.monotonic()-started
    p=Path('mobius_coupled_square_independent_review_084.json')
    if p.exists():p=Path('mobius_coupled_square_independent_review_084_attempt_'+str(time.time_ns())+'.json')
    p.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n');print(p,r['status']);print(r.get('traceback',''))
