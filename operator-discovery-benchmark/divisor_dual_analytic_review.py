#!/usr/bin/env python3
"""Separate analytic dispositions for exact detector-selected matrix formulas."""
from fractions import Fraction as Q
from pathlib import Path
from math import lcm,isqrt
import argparse,subprocess,sys,json
from stable_scale_report import BASE,read,sha,digest
from divisor_dual_report import summary
import divisor_dual_grammar as g

CODE=['divisor_dual_analytic_review.py','check_divisor_dual_analytic.py','divisor_dual_analytic_report.py','divisor_dual_analytic_proof.txt','test_divisor_dual_analytic_contracts.py']
def write(path,data):Path(path).write_text(json.dumps(data,indent=2)+'\n')


def obstruction(p):
    m=p['mask'];kind=m['kind']
    if kind=='constant' and m['value']==0:return 'uncovered_tail_rows'
    if kind in ['residue','divisible_union','square']:return 'uncovered_tail_rows'
    if kind=='prefix' and Q(m['power'])<1:return 'uncovered_tail_rows'
    if Q(p['Gram_power'])==2 and Q(p['Gram_coefficient'])<Q(4,3):return 'underpowered_quadratic_Gram'
    return None


def count_unselected(mask,L,U,N):
    def residue(r,m):return (U-r)//m-(L-r)//m
    k=mask['kind']
    if k=='constant':return (U-L)*(1-mask['value'])
    if k=='residue':return U-L-residue(mask['residue'],mask['modulus'])
    if k=='divisible_union':
        period=lcm(*mask['bases']);return sum(residue(r,period) for r in range(period) if all(r%b for b in mask['bases']))
    if k=='square':return U-L-(isqrt(U)-isqrt(L))
    if k=='prefix':return max(0,U-max(L,g.floor_power(N,Q(mask['power']))))
    raise ValueError('No declared uncovered-row theorem')


def witness(p,q,method):
    # X=2^(q*k) keeps every test dyadic and the critical root exact.
    for k in range(1,257):
        X=2**(q*k);params=g.parameters(p,X,q);D,Y=Q(params['D']),Q(params['Y'])
        if method=='uncovered_tail_rows':
            J=count_unselected(p['mask'],2*X,4*X,4*X);J3=count_unselected(p['mask'],2*X,3*X,4*X);upper=D*J-X*J3*J3
            data={'tail_support_count':J,'uncovered_through_3X':J3,'exact_child_energy_lower':str(X*J3*J3),'Gram_quadratic_exactly_zero':True}
        else:
            T=Q((2*X-1)*2*X*(4*X-1),6);upper=2*X*(D+Y)-T;data={'tail_support_count':2*X,'exact_child_energy':str(T),'Gram_quadratic_upper':2*X}
        if upper<0:return dict(data,X=X,level=q,parameters=params,quadratic_upper=str(upper),method=method,tail_vector_definition='one on the indicated unselected tail rows' if method=='uncovered_tail_rows' else 'one on every row in (2X,4X]',
            negative_matrix_witness_is_not_RH_counterexample=True,full_matrix_materialization_needed=False)
    raise ArithmeticError('Analytic witness resource limit reached; not a disproof')


def review(source,destination):
    source=Path(source).resolve();summary(source);queue=read(source/'proof_queue.json');final=read(source/'final_evaluation.json');destination=Path(destination).resolve();destination.mkdir(exist_ok=False)
    spec={'schema':1,'source_run':str(source),'source_sha256':{n:sha(source/n) for n in ['protocol.json','seal.json','proof_queue.json','final_evaluation.json','verification.json']},'code_sha256':{n:sha(BASE/n) for n in CODE},
        'original_candidate_formulas_must_remain_unchanged':True,'analytical_review_occurs_after_frozen_final':True,'illustrative_witness_levels':[2,7,17],
        'disproof_quantifiers':'for every fixed integer q>=2 there are arbitrarily large dyadic scales with a negative quadratic form',
        'proof_method_scope':'ordinary analytical arguments and independent exact certificate checks; not machine-formalized','RH_proved':False};write(destination/'protocol.json',spec);(destination/'frozen_source').mkdir()
    for n in CODE:(destination/'frozen_source'/n).write_bytes((BASE/n).read_bytes())
    attempts=[]
    for row in queue['queue']:
        p=row['exact_program'];method=obstruction(p);fresh=[r for r in final['matrix_certificates'] if r['program_id']==row['program_id']]
        attempt={'program_id':row['program_id'],'exact_program':p,'exact_program_sha256':digest(p),'frozen_global_claim':row['global_claim'],'formula_changed_after_detection':False,'detector_origins':row['detector_origins'],
            'validation_positive_cases':row['validation_evidence']['positive_matrix_cases'],'fresh_matrix_cases':len(fresh),'fresh_positive_matrices':sum(r['certificate'].get('finite_matrix_PSD',False) for r in fresh),
            'proof_status':'disproved_uniform_matrix_claim' if method else 'unresolved_uniform_matrix_claim','analytic_method':method,'witnesses':[witness(p,q,method) for q in spec['illustrative_witness_levels']] if method else [],
            'global_PSD_proved':False,'global_full_signed_defect_proved':False,'RH_proved':False}
        if not method:
            full=p['mask']=={'kind':'above','threshold':1};attempt.update({'complete_nonunit_Gram':full,'necessary_signed_arithmetic_entry':'D(X,q)*Q(4X)-Delta(X)>=0',
                'nullspace_arithmetic_not_affected_by_Gram_weight':full,'Schur_complement_attempt':'conditional_only' if full else 'unavailable_for_this_mask',
                'sufficient_arithmetic_gap_if_proved':'Delta(X)<=D(X,q)*Q(4X)/2' if full else None,
                'conditional_orthogonal_buffer':'Y>128*X^(7/2)+(1024/c_D)*X^(9/2)' if full else None,
                'missing_lemma':'uniform bound on the exact signed nullspace entry and the remaining Schur complement',
                'prescribed_polynomial_level_constant_is_sufficient_not_necessary_for_RH':True,'bounded_level_constant_has_extra_simple_zero_consequence':Q(p['level_power'])==0})
        attempts.append(attempt)
    result={'protocol_sha256':digest(spec),'source_queue_sha256':sha(source/'proof_queue.json'),'attempts':attempts,
        'proved_subclaims':['complete actual inverse forces C_N*mu=e_1 for every N','nonunit divisor Gram annihilates mu at every N','ordinary q=1 row-norm energy power three'],
        'next_run_feedback':[{'change':'test or prune positive-density uncovered tail rows for this particular universal PSD certificate','kind':'proved_structural_obstruction','original_run_modified':False},
            {'change':'expand Gram coefficient profiles beyond the proved tail-vector obstruction','kind':'candidate_language_feedback','larger_coefficients_prove_PSD':False,'original_run_modified':False},
            {'change':'separate cofinal exponent decay from the permitted finite constant growth law','kind':'coverage_limitation','RH_implies_current_polynomial_constant_family':False,'original_run_modified':False}],
        'all_scale_critical_signed_bound_proved':False,'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False};write(destination/'attempts.json',result)
    subprocess.run([sys.executable,str(BASE/'check_divisor_dual_analytic.py'),'--review-dir',str(destination)],cwd=BASE,check=True)
    from divisor_dual_analytic_report import summary as report,text_report
    s=report(destination);write(destination/'summary.json',s);(destination/'report.txt').write_text(text_report(s));write(BASE/'divisor-dual-results/latest-analytical-review.json',{'review_directory':str(destination)})


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--source',type=Path,required=True);parser.add_argument('--review-dir',type=Path,required=True);args=parser.parse_args();review(args.source,args.review_dir)
