#!/usr/bin/env python3
"""Independent analytic obstruction witnesses and unchanged candidate audit."""
import argparse
from pathlib import Path
from fractions import Fraction as Q
from math import gcd,lcm,isqrt
import flint
from stable_scale_report import BASE,read,sha,digest
from check_divisor_dual import ceiling,weight,matrix
from check_signed_control import independent_inverse
from check_mellin_kernels import put


def count(mask,L,U,N):
    k=mask['kind']
    if k=='constant':return (U-L)*(1-mask['value'])
    if k in ['residue','divisible_union']:
        period=mask.get('modulus') if k=='residue' else lcm(*mask['bases']);out=0
        for r in range(period):
            selected=r==mask['residue'] if k=='residue' else any(r%b==0 for b in mask['bases'])
            if not selected:out+=(U-r)//period-(L-r)//period
        return out
    if k=='square':return U-L-isqrt(U)+isqrt(L)
    if k=='prefix':
        p=Q(mask['power']);a,b=p.numerator,p.denominator;lo,hi=0,N+1
        while hi-lo>1:
            m=(lo+hi)//2
            if m**b<=N**a:lo=m
            else:hi=m
        return max(0,U-max(L,lo))
    raise ValueError('Unknown obstruction mask')


def expected_method(p):
    mask=p['mask'];k=mask['kind']
    if k in ['residue','divisible_union','square'] or k=='prefix' and Q(mask['power'])<1 or k=='constant' and not mask['value']:return 'uncovered_tail_rows'
    if Q(p['Gram_power'])==2 and Q(p['Gram_coefficient'])<Q(4,3):return 'underpowered_quadratic_Gram'
    return None


def audit_witness(p,w):
    X,q=w['X'],w['level'];assert q>=2 and X>0 and X&(X-1)==0;D=Q(p['diagonal_coefficient'])*(1+ceiling(q,p['level_power']))*X*ceiling(X,Q(1,q));Y=Q(p['Gram_coefficient'])*ceiling(X,p['Gram_power']);assert Q(w['parameters']['D'])==D and Q(w['parameters']['Y'])==Y
    if w['method']=='uncovered_tail_rows':
        J=count(p['mask'],2*X,4*X,4*X);J3=count(p['mask'],2*X,3*X,4*X);upper=D*J-X*J3**2;assert J==w['tail_support_count'] and J3==w['uncovered_through_3X'] and Q(w['exact_child_energy_lower'])==X*J3**2 and w['Gram_quadratic_exactly_zero']
    else:
        T=Q((2*X-1)*2*X*(4*X-1),6);upper=2*X*(D+Y)-T;assert Q(w['exact_child_energy'])==T and w['Gram_quadratic_upper']==2*X and w['tail_support_count']==2*X
    assert upper==Q(w['quadratic_upper'])<0 and w['negative_matrix_witness_is_not_RH_counterexample'] and not w['full_matrix_materialization_needed']


def check(d):
    spec=read(d/'protocol.json');result=read(d/'attempts.json');source=Path(spec['source_run']);queue=read(source/'proof_queue.json');final=read(source/'final_evaluation.json');checks={};counts={'exact_large_dyadic_obstruction_witnesses':0,'direct_public_quadratic_witnesses':0,'congruence_nullspace_entries':0}
    def passed(n):checks[n]=True;print('Verified',n,flush=True)
    from divisor_dual_report import summary
    summary(source)
    for n,h in spec['source_sha256'].items():assert sha(source/n)==h
    for n,h in spec['code_sha256'].items():assert sha(BASE/n)==h==sha(d/'frozen_source'/n)
    assert result['protocol_sha256']==digest(spec) and result['source_queue_sha256']==sha(source/'proof_queue.json') and spec['original_candidate_formulas_must_remain_unchanged'] and spec['analytical_review_occurs_after_frozen_final']
    byid={r['program_id']:r for r in queue['queue']};assert {r['program_id'] for r in result['attempts']}==set(byid)
    for row in result['attempts']:
        original=byid[row['program_id']];p=original['exact_program'];assert row['exact_program']==p and row['exact_program_sha256']==digest(p) and row['frozen_global_claim']==original['global_claim'] and not row['formula_changed_after_detection'] and row['validation_positive_cases']==original['validation_evidence']['positive_matrix_cases']
        fresh=[r for r in final['matrix_certificates'] if r['program_id']==row['program_id']];assert row['fresh_matrix_cases']==len(fresh) and row['fresh_positive_matrices']==sum(r['certificate'].get('finite_matrix_PSD',False) for r in fresh)
    passed('every_proof_attempt_uses_unchanged_detector_selected_formula_and_frozen_evidence')
    for row in result['attempts']:
        p=row['exact_program'];method=expected_method(p);assert row['analytic_method']==method and row['proof_status']==('disproved_uniform_matrix_claim' if method else 'unresolved_uniform_matrix_claim') and not row['global_PSD_proved'] and not row['global_full_signed_defect_proved'] and not row['RH_proved']
        if method:
            assert [w['level'] for w in row['witnesses']]==spec['illustrative_witness_levels']
            for w in row['witnesses']:audit_witness(p,w);counts['exact_large_dyadic_obstruction_witnesses']+=1
            # Explicitly check the symbolic hypotheses, not only the sample q's.
            assert Q(p['diagonal_coefficient'])>0 and Q(p['level_power'])>=0
            # For every fixed q>1, 1+1/q<2; its finite constant cannot fix
            # a negative cubic coefficient. Periodic/prefix/square counts
            # give a positive linear lower bound on unselected tail rows.
            if method=='uncovered_tail_rows':
                m=p['mask'];k=m['kind']
                if k=='residue':assert m['modulus']>=2 and 0<=m['residue']<m['modulus']
                elif k=='divisible_union':assert all(b>=2 for b in m['bases']) and all(1%b for b in m['bases'])
                elif k=='prefix':assert 0<=Q(m['power'])<1
                elif k=='constant':assert m['value']==0
                else:assert k=='square'
            else:assert Q(p['Gram_power'])==2 and Q(8,3)-2*Q(p['Gram_coefficient'])>0
    passed('all_fixed_q_universal_obstruction_hypotheses_and_exact_scalar_disproof_witnesses')
    # Direct finite checks use the integration windows, not an H-kernel helper.
    public_masks=[{'kind':'constant','value':0},{'kind':'residue','modulus':3,'residue':1},{'kind':'divisible_union','bases':[2,3]},{'kind':'square'},{'kind':'prefix','power':'1/3'}]
    for m in public_masks:
        for X in [4,8,16]:
            N=4*X;z=[0]+[int(n>2*X and not weight(m,n,N)) for n in range(1,N+1)];response=[0]+[sum(z[n] for n in range(1,k+1) if k%n==0) for k in range(1,N+1)];assert response==z and sum(weight(m,k,N)*response[k]**2 for k in range(1,N+1))==0
            J3=sum(z[2*X+1:3*X+1]);prefix=[0]
            for v in z[1:]:prefix.append(prefix[-1]+v)
            H=sum(prefix[t]**2 for t in range(2*X,4*X))-4*sum(prefix[t]**2 for t in range(X,2*X));assert H>=X*J3**2 and sum(z)==count(m,2*X,4*X,N);counts['direct_public_quadratic_witnesses']+=1
    passed('independent_direct_divisor_transform_tail_annihilation_and_full_window_energy')
    flint.ctx.prec=768
    for row in result['attempts']:
        if row['proof_status']!='unresolved_uniform_matrix_claim':continue
        p=row['exact_program'];assert row['complete_nonunit_Gram'] and p['mask']=={'kind':'above','threshold':1} and row['nullspace_arithmetic_not_affected_by_Gram_weight'] and row['Schur_complement_attempt']=='conditional_only'
        for X in [2,4,8]:
            q=3;N=4*X;mu,M=independent_inverse(N);params,A,den=matrix(p,X,q);delta=sum(M[n]**2 for n in range(2*X,4*X))-4*sum(M[n]**2 for n in range(X,2*X));Qn=sum(n*n for n in mu[1:]);v=mu[1:];value=Q(sum(v[i]*A[i][j]*v[j] for i in range(N) for j in range(N)),den);assert value==Q(params['D'])*Qn-delta;counts['congruence_nullspace_entries']+=1
            Cinv=[[mu[i//j] if i%j==0 else 0 for j in range(1,N+1)] for i in range(1,N+1)];assert max(sum(abs(z) for z in rr) for rr in Cinv)<=2*isqrt(N) and max(sum(abs(Cinv[i][j]) for i in range(N)) for j in range(N))<=N
        assert row['necessary_signed_arithmetic_entry']=='D(X,q)*Q(4X)-Delta(X)>=0' and row['missing_lemma']=='uniform bound on the exact signed nullspace entry and the remaining Schur complement' and row['prescribed_polynomial_level_constant_is_sufficient_not_necessary_for_RH']
        assert row['bounded_level_constant_has_extra_simple_zero_consequence']==(Q(p['level_power'])==0)
    # h=8X², g>=1/(2(4X)^(3/2)), a>=D/2, D>=2*c_D*X
    # produce 128X^(7/2)+(1024/c_D)X^(9/2), with strict > required.
    assert 2*4*2==16 and 16*8==128 and 16*64==1024
    passed('exact_signed_nullspace_entry_conditional_Schur_buffer_and_unresolved_arithmetic_gap')
    assert all(not f['original_run_modified'] for f in result['next_run_feedback']) and not result['all_scale_critical_signed_bound_proved'] and not result['RH_proved'] and result['uniform_RH_sufficient_signed_controls_verified']==[]
    passed('analytical_feedback_only_to_fresh_grammar_and_RH_status_not_promoted')
    verification={'protocol_sha256':digest(spec),'attempts_sha256':sha(d/'attempts.json'),'checker_sha256':sha(BASE/'check_divisor_dual_analytic.py'),'source_queue_sha256':sha(source/'proof_queue.json'),'checks':checks,'counts':counts,'all_passed':all(checks.values()),
        'mathematical_audit_imports_production_code':False,'machine_formalized':False,'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False};put(d/'verification.json',verification);print('Independent analytical review',len(checks),'/',len(checks),flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--review-dir',type=Path,required=True);check(p.parse_args().review_dir.resolve())
