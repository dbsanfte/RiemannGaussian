#!/usr/bin/env python3
"""Frozen large-scale signed-gap profiles and an anonymous estimate proof queue."""
from fractions import Fraction as Q
from pathlib import Path
import argparse,random,os,sys,subprocess
from stable_scale_search import BASE,read,write,sha,digest,verify_code
from divisor_dual_search import restrict
import signed_gap_profile_grammar as g

CODE=['signed_gap_profile_grammar.py','signed_gap_profile_search.py','check_signed_gap_profiles.py','signed_gap_profile_report.py','signed_gap_profile_proof.txt',
      'signed_gap_profile_analytic.py','check_signed_gap_profile_analytic.py','test_signed_gap_profile_contracts.py','plot_signed_gap_profiles.py']
SEALED=['protocol.json','candidate_batch.json','validation.json','archive.json','proof_queue.json']


def protocol(source):
    from divisor_dual_analytic_report import load_latest
    a=load_latest();assert a['source_run']==str(Path(source).resolve());old=read(Path(source)/'protocol.json');fail=[]
    for f in sorted((BASE/'signed-gap-profile-results').glob('*/failure.json')):
        d=f.parent;fail.append({'run_directory':str(d),'failure_sha256':sha(f),'files_sha256':{p.name:sha(p) for p in d.glob('*.json') if p.name!='failure.json'},'excluded_final_scales':read(d/'final_cases.json')['scales'] if (d/'final_cases.json').exists() else []})
    return {'schema':1,'grammar_version':g.VERSION,'source_run':str(Path(source).resolve()),'source_sha256':{n:sha(Path(source)/n) for n in ['protocol.json','verification.json','proof_queue.json','summary.json']},
        'source_analytical_review':a['review_directory'],'source_analytical_sha256':{n:sha(Path(a['review_directory'])/n) for n in ['protocol.json','attempts.json','verification.json']},
        'code_sha256':dict(old['code_sha256'],**{n:sha(BASE/n) for n in CODE}),'this_stage_source_files':CODE,'named_calibration_dependencies':old['named_calibration_dependencies'],'seed':2026100828,
        'training_scales':[1024,2048,4096,8192],'training_levels':[2,3,6,12],'validation_scales':[12288,16384,24576,32768],'validation_levels':[2,3,6,12],
        'earlier_exposed_scales_are_development':[4096,8192,30,32,64],'target':'full actual signed half-gap Delta(X)<=D(X,q)*Q(4X)/2, every dyadic X and cofinal q',
        'exponent_schedules':[{'kind':'power','power':r} for r in ['1/6','1/3','1/2','1','2']]+[{'kind':'exponential','power':r} for r in ['1/2','1']]+[{'kind':'factorial'}],
        'constant_laws':[{'kind':'constant'}]+[{'kind':'power','power':r} for r in ['1/6','1/3','1/2','1','2','3']]+[{'kind':'exponential','power':r} for r in ['1/2','1','2']]+[{'kind':'factorial'}]+[{'kind':'denominator_power','power':r} for r in ['1/6','1/2','1','2']]+[{'kind':'free_per_level'}],
        'log_powers':['0','1/6','1'],'constant_fit':'5/4 times largest exact positive half-gap requirement on training, plus 2^-64; per-level family has no unseen-level prediction',
        'ranking':'validation half-gap pass count, then maximum fully charged cost/generic upper bound, then description length and stable id',
        'archive_rule':'best per exponent schedule and constant production family; all failed and missing cases retained',
        'anonymous_minimum_response_dimensions':[4,5,6,7,8],'minimum_feature_dictionary':[list(t) for t in g.MONOMIALS],'minimum_sparse_support_budget':4,
        'minimum_inference_expected_polynomial_or_coefficients_supplied':False,'analytical_admission_backend':'generic finite difference plus boundary check, and binary-prefix exchange argument',
        'final_cases':{'dyadic_exponent_range':[16,19],'dyadic_count':2,'irregular_scale_range':[45000,90000],'irregular_count':2,'new_level_range':[4,17],'new_level_count':2,'excluded_earlier_final_levels':[9,10],
            'minimum_dimension_range':[11,16],'minimum_dimension_count':2},
        'integer_program_bit_budget':65536,'semantic_denominator_cap':False,'global_calibration':{'epsilon':'1','D_coefficient':'16','ordinary_energy_power':'3','method':'H row-norm <=8X^2'},
        'guided_arithmetic_target_and_grammar_supplied':True,'proof_attempts_after_sealed_candidates_and_final':True,'finite_success_is_not_all_scale_control':True,'historical_priority_is_acceptance_gate':False,
        'retained_failed_runs_are_development':fail,'global_actual_critical_signed_gap_proved':False,'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False}


def score(rows):
    valid=[r for r in rows if not r['parameters']['missing']];passed=[r for r in valid if r['finite_half_gap_pass']]
    return {'finite_passes':len(passed),'finite_cases':len(valid),'missing_cases':len(rows)-len(valid),'max_charged_bound_over_generic':str(max((Q(r['charged_bound_over_generic']) for r in valid),default=Q(10**100))),'global_signed_bound_proved':False}


def key(row):return (-row['score']['finite_passes'],Q(row['score']['max_charged_bound_over_generic']),len(str(row['program'])),row['id'])


def worker(d):
    spec=read(d/'protocol.json');verify_code(spec);denied=restrict(d,spec);train=g.arithmetic(spec['training_scales']);programs=[]
    for schedule in spec['exponent_schedules']:
        for law in spec['constant_laws']:
            for L in spec['log_powers']:
                p=g.fit({'exponent_schedule':schedule,'constant_law':law,'log_power':L,'arithmetic_model':'inverse_one'},train,spec['training_levels']);programs.append({'id':digest(p),'program':p,'training_observations':g.observations(p,train,spec['training_levels'])})
    responses=g.min_response(spec['anonymous_minimum_response_dimensions']);inference=g.infer_polynomial(responses,spec['minimum_sparse_support_budget'])
    write(d/'candidate_batch.json',{'protocol_sha256':digest(spec),'programs':programs,'training_arithmetic':train,'anonymous_minimum_responses':responses,'minimum_inference':inference,
        'access_denials':denied,'candidate_batch_frozen_before_validation':True,'expected_winning_formula_supplied':False})
    validation=g.arithmetic(spec['validation_scales']);vr=[]
    for row in programs:
        obs=g.observations(row['program'],validation,spec['validation_levels']);vr.append({'program_id':row['id'],'observations':obs,'score':score(obs)})
    write(d/'validation.json',{'arithmetic':validation,'program_results':vr,'all_candidates_retained':True,'final_data_used':False});byid={r['program_id']:r for r in vr};archive=[]
    for schedule in spec['exponent_schedules']:
        for kind in sorted({p['kind'] for p in spec['constant_laws']}):
            choices=[dict(row,score=byid[row['id']]['score']) for row in programs if row['program']['exponent_schedule']==schedule and row['program']['constant_law']['kind']==kind];best=min(choices,key=key);archive.append({'program_id':best['id'],'exponent_schedule':schedule,'constant_family':kind,'score':best['score']})
    write(d/'archive.json',{'leads':archive,'selection_closed':True,'final_data_used':False,'minimum_lead':inference['selected'],'global_actual_critical_signed_gap_proved':False,'uniform_RH_sufficient_signed_controls_verified':[]})
    ids={r['id']:r for r in programs};queue=[]
    for row in archive:
        p=ids[row['program_id']]['program'];free=p['constant_law']['kind']=='free_per_level';queue.append({'program_id':row['program_id'],'exact_program':p,'validation_evidence':row['score'],
            'global_claim':'exists q0, every integer q>=q0, exists finite C_q, every dyadic X: Delta<=D*Q/2' if free else 'exists q0, every integer q>=q0, every dyadic X: Delta<=D*Q/2 for the exact fitted C(q)',
            'missing_lemma':'all-scale actual signed half-gap','new_level_constants_are_unknown':free,'global_bound_proved':False,'formula_changed_after_detection':False,'proof_status':'pending_separate_analytical_attempt'})
    write(d/'proof_queue.json',{'protocol_sha256':digest(spec),'queue':queue,'minimum_lead':inference['selected'],'minimum_claim':'for every dimension m and mass 0<=J<=m, the exact detected polynomial is the minimum binary-prefix square energy',
        'candidate_ids_frozen_before_final':True,'final_data_used_for_selection':False})
    write(d/'seal.json',{'protocol_sha256':digest(spec),'files':{n:sha(d/n) for n in SEALED},'selection_closed':True,'final_cases_exist':False});print('Sealed',len(programs),'signed-gap profiles and anonymous minimum-bound lead',flush=True)


def fake_arithmetic(scales,head):
    N=4*max(scales);mu=g.inverse_one_prefix(head);fake=mu+[1]*(N-head);needed={v for X in scales for v in [X,2*X,4*X]};snap={};M=E=Qn=0
    for n in range(1,N+1):
        E+=M*M;M+=fake[n];Qn+=fake[n]*fake[n]
        if n in needed:snap[n]=(E,Qn,M)
    rows=[]
    for X in scales:
        A=snap[2*X][0]-snap[X][0];child=snap[4*X][0]-snap[2*X][0];rows.append({'X':X,'energy':A,'child_energy':child,'signed_defect':child-4*A,'squarefree_count_through_4X':snap[4*X][1]})
    c=sum(mu)-head
    return {'cutoff':N,'complete_inverse_sha256':digest(fake),'rows':rows,'shared_actual_prefix_through':head,'shared_actual_prefix_sha256':digest(mu),'eventual_affine_offset':c,
        'coefficient_origin':'counterfeit actual head and positive future tail','producer_prime_or_factor_oracle_used':False,'whole_signed_defect_retained':True,'actual_complete_inverse':False,'analytic_eventual_defect_formula':'(28X^3-X)/3-2(c^2-c)X'}


def final(d):
    spec=read(d/'protocol.json');verify_code(spec);batch=read(d/'candidate_batch.json');arc=read(d/'archive.json');rule=spec['final_cases'];rng=random.Random(int.from_bytes(os.urandom(32),'big'));excluded={X for f in spec['retained_failed_runs_are_development'] for X in f['excluded_final_scales']}
    dyadic=sorted(rng.sample([2**n for n in range(rule['dyadic_exponent_range'][0],rule['dyadic_exponent_range'][1]+1) if 2**n not in excluded],rule['dyadic_count']));irregular=sorted(rng.sample([n for n in range(rule['irregular_scale_range'][0],rule['irregular_scale_range'][1]+1) if n not in excluded and n&(n-1)],rule['irregular_count']));newq=sorted(rng.sample([q for q in range(rule['new_level_range'][0],rule['new_level_range'][1]+1) if q not in spec['training_levels']+rule['excluded_earlier_final_levels']],rule['new_level_count']));dims=sorted(rng.sample(range(rule['minimum_dimension_range'][0],rule['minimum_dimension_range'][1]+1),rule['minimum_dimension_count']))
    cases={'scales':sorted(dyadic+irregular),'dyadic_scales':dyadic,'irregular_scales':irregular,'new_levels':newq,'seen_levels':[3,12],'minimum_dimensions':dims,'generated_after_seal':True,'seal_sha256':sha(d/'seal.json')};write(d/'final_cases.json',cases);data=g.arithmetic(cases['scales']);ids={r['id']:r for r in batch['programs']};levels=cases['seen_levels']+newq;fake=fake_arithmetic(cases['scales'],4*max(spec['validation_scales']));rows=[]
    for r in arc['leads']:
        p=ids[r['program_id']]['program'];obs=g.observations(p,data,levels);controls=g.observations(p,fake,levels);rows.append({'program_id':r['program_id'],'observations':obs,'score':score(obs),'counterfeit_observations':controls})
    fresh_min=g.min_response(dims);lead=arc['minimum_lead'];minobs=[]
    for row in fresh_min:
        prediction=sum(Q(c)*row['mass']**i*row['dimension']**j for i,j,c in lead['terms']) if lead else None;minobs.append(dict(row,predicted=None if prediction is None else str(prediction),finite_pass=prediction==row['anonymous_response']))
    write(d/'final_evaluation.json',{'protocol_sha256':digest(spec),'cases_sha256':digest(cases),'arithmetic':data,'program_results':rows,'counterfeit_arithmetic':fake,'fresh_minimum_observations':minobs,
        'global_actual_critical_signed_gap_proved':False,'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False});print('Fresh actual signed gaps through coefficient cutoff',data['cutoff'],flush=True)


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('mode',nargs='?',default='run',choices=['run','worker']);parser.add_argument('--run-dir',type=Path,required=True);parser.add_argument('--source',type=Path);args=parser.parse_args();d=args.run_dir.resolve()
    if args.mode=='worker':worker(d);return
    if args.source is None:raise ValueError('Verified detector-to-proof source required')
    d.mkdir(exist_ok=False,parents=True);spec=protocol(args.source);write(d/'protocol.json',spec);(d/'frozen_source').mkdir()
    for n in CODE:(d/'frozen_source'/n).write_bytes((BASE/n).read_bytes())
    try:
        subprocess.run([sys.executable,str(BASE/'signed_gap_profile_search.py'),'worker','--run-dir',str(d)],cwd=BASE,check=True);final(d)
        subprocess.run([sys.executable,str(BASE/'check_signed_gap_profiles.py'),'--run-dir',str(d)],cwd=BASE,check=True)
        subprocess.run([sys.executable,str(BASE/'signed_gap_profile_analytic.py'),'--run-dir',str(d)],cwd=BASE,check=True)
        from signed_gap_profile_report import summary,text_report
        s=summary(d);write(d/'summary.json',s);(d/'report.txt').write_text(text_report(s));write(BASE/'signed-gap-profile-results/latest.json',{'run_directory':str(d)})
    except Exception as e:write(d/'failure.json',{'error_type':type(e).__name__,'error':str(e),'original_data_and_sources_retained':True});raise


if __name__=='__main__':main()
