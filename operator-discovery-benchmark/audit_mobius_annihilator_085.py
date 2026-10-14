"""Independent external085 preflight; synthetic tiny integration only."""
from fractions import Fraction as Q
from pathlib import Path
from unittest.mock import patch
import json,time,traceback,sys
import mobius_annihilator_085 as P
import mobius_annihilator_bank_085 as B
import check_mobius_annihilator_085 as C
import run_mobius_annihilator_085 as RUN

def fixture():
    w=dict(kind='product',arithmetic='all',i=0,j=0)
    def term(comp):return dict(cut=dict(scale='1',n_exponent='1',u_exponent='0',complement=comp,unit_balance=True),weight=dict(w),theta='5/2')
    return dict(schema='coupled-divisor-completion-v1',kernel=[dict(divisor=4,weight='-1'),dict(divisor=5,weight='1'),dict(divisor=8,weight='1'),dict(divisor=10,weight='-1')],memory=1,rays=[],drift_multiplier='3/2',coupled_terms=[term(False),term(True)],gram_weights=['1/4','1/3'],prime_anchor=True)

def bank():return [dict(scale='1',u_exponent='1',complement=False,unit_balance=False),dict(scale='1/2',u_exponent='1',complement=True,unit_balance=True),dict(scale='3/2',u_exponent='-17/31',complement=False,unit_balance=True)]

def integration():
    p=fixture();o=P.SQUARE.O.synthesize(p)['certificate'];cases=[]
    for u in (1,4,24,53):
        model=P.B.build_model(p,u);data=C.R.build_remainder(p,u,o);ids=C.build_identities(data['model'],bank());V,cuts=P.identity_vectors(model,bank());E=model['price_dimension'];assert cuts==ids['cuts']
        assert [[Q(str(V[i,j]))for j in range(3)]for i in range(E)]==ids['vectors']
        S=[[Q(-1)if i==j else Q(2,3)for j in range(3)]for i in range(3)];rows=[[(-1)**i]for i in range(E)];cert,diag=P.certificate(model,bank(),S,4,rows)
        v=C.verify_certificate(p,u,o,bank(),cert);assert v['status']=='VERIFIED_FINITE_ANNIHILATOR_SQUARE_BOUND',v
        cases.append(dict(u=u,price=cert['price'],cuts=cuts,identity_trace=diag['identity_trace']))
    solve=P.solve(p,bank(),53,time_limit=10);assert solve['status']=='EXACT_ANNIHILATOR_SQUARE_PROPOSAL',solve
    assert C.verify_certificate(p,53,o,bank(),solve['certificate'])['status']=='VERIFIED_FINITE_ANNIHILATOR_SQUARE_BOUND'
    cat=B.catalog(p,[24,53],scale_height=4,exponent_height=3);witness={u:[1]+[-1]*(cat['models'][u]['price_dimension']-1)for u in cat['parents']};selected=B.select(cat,witness,bank_size=3)
    # Reconstruct exact score and greedy tie order independently from complete integer columns.
    values={}
    for item in cat['representatives']:
        values[item['id']]=[Q(sum(a*b for a,b in zip(cat['cache'][key]['column'],witness[u]))**2,cat['cache'][key]['norm'])if cat['cache'][key]['norm']else Q(0)for u,key in zip(cat['parents'],item['column_keys'])]
    remaining=[x for x in cat['representatives']if any(cat['cache'][k]['norm']for k in x['column_keys'])];coverage=[Q(0)]*2;chosen=[]
    while remaining and len(chosen)<3:
        gain=lambda x:sum(v/(1+c)for v,c in zip(values[x['id']],coverage))
        best=max(remaining,key=gain)
        if not gain(best):break
        chosen.append(best['id']);coverage=[a+b for a,b in zip(coverage,values[best['id']])];remaining.remove(best)
    assert chosen==selected['selected_ids']
    return dict(tiny_exact_cases=cases,tiny_SCS_exact_admission=True,independent_exact_score_and_tie_reconstruction=True,synthetic_catalog_representatives=len(cat['representatives']))

def guards():
    p=fixture();model=P.B.build_model(p,53);model['extra_resident_bytes']=4*1024**3
    try:P.identity_integer_column(model,bank()[0])
    except ValueError:pass
    else:raise AssertionError('standalone identity column cumulative gate absent')
    source=Path('run_mobius_annihilator_085.py').read_text()
    assert "row['admission']['status']!='VERIFIED_FINITE_FIXED_OPERATOR_SQUARE_LOWER_BOUND'"in source,'saved witness status mismatch'
    model=P.B.build_model(p,53);cat=B.catalog(p,[24,53],scale_height=4,exponent_height=3);w={u:[1]*m['price_dimension']for u,m in cat['models'].items()};w[24][0]=-1
    try:B.select(cat,w,bank_size=3)
    except ValueError:pass
    else:raise AssertionError('standalone witness anchor sign not enforced')
    return dict(standalone_identity_column_cumulative_gate=True,witness_frozen_status_binding=True,standalone_witness_anchor_one=True)

def runner_metadata():
    import random
    counts=RUN.validate_parent();candidates=RUN.read(RUN.PRIOR.OUT/'frozen_candidates.json')['candidates'];assert len(candidates)==8;rows=[]
    for c in candidates:
        for u in RUN.SPEC['training_parents']:
            name='witness_'+c['id']+'_'+str(u)+'.json';row=RUN.read(RUN.PRIOR.OUT/name);a=row['admission'];cert=row['certificate']
            assert row['candidate_id']==c['id']and row['u']==u
            assert a['status']=='VERIFIED_FINITE_FIXED_OPERATOR_SQUARE_LOWER_BOUND'
            assert a['fixed_operator_only']is True and a['whole_theta_grammar_bound']is False
            assert cert['signs'][0]==1 and len(cert['signs'])==a['effective_dimension']
            assert cert['squarefree_count']==a['squarefree_count']
            rows.append(dict(candidate_id=c['id'],u=u,file=name,status=a['status']))
    assert RUN.SPEC['training_parents']==RUN.read(RUN.PRIOR.OUT/'validation_draw.json')['parents']
    excluded=set(RUN.inventory()['parents']);rng=random.Random(RUN.SPEC['seed']);draw=[]
    for lo,hi in RUN.SPEC['validation_bands']:
        while True:
            u=rng.randint(lo,hi)
            if u not in excluded:draw.append(u);excluded.add(u);break
    return dict(status='PASS',direct_byte_preserved_counts=counts,total_direct_byte_preserved=sum(counts),saved_artificial_witness_metadata_bindings=rows,prospective_fresh_parent_draw=sorted(draw),scope='Read-only metadata and byte-preservation audit; no scientific values or rerun')

if __name__=='__main__':
    started=time.monotonic();r={}
    try:
        if '--metadata-only'in sys.argv:r.update(runner_metadata())
        else:
            if '--guards-only'not in sys.argv:r.update(integration())
            r.update(guards());r.update(status='PASS')
    except Exception:r.update(status='FAIL',traceback=traceback.format_exc())
    r.update(elapsed_seconds=time.monotonic()-started,scientific_source_queries=False,old_tests_run=False,hashes_used=False,uniform_remaining_bound_proved=False,uniform_source_bound_proved=False,RH_proved=False)
    path=Path('mobius_annihilator_independent_audit_085.json')
    if path.exists():path=Path('mobius_annihilator_independent_audit_085_attempt_'+str(time.time_ns())+'.json')
    path.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n');print(path,r['status']);print(r.get('traceback',''))
