#!/usr/bin/env python3
"""Frozen targeted audit of the actual RH energy-defect proof obligation."""
from fractions import Fraction as Q
from pathlib import Path
import argparse,os,random,socket,subprocess,sys
import flint
from stable_scale_search import BASE,read,write,sha,digest,verify_code
import critical_defect_grammar as g

CODE=['critical_defect_grammar.py','critical_defect_search.py','check_critical_defects.py','critical_defect_report.py',
      'critical_defect_proof.txt','test_critical_defect_contracts.py','plot_critical_defects.py']
EXTRA=['rational_fractional_evaluator.py','check_rational_fractional_contracts.py','rational_fractional_contract_report.py']
SEALED=['protocol.json','candidate_batch.json','validation.json','archive.json']


def protocol(source):
    from branch_center_report import summary
    from rational_fractional_contract_report import load_latest
    source=Path(source).resolve();summary(source);assert Path(load_latest()['run_directory'])==source;old=read(source/'protocol.json');failed=[]
    for p in sorted((BASE/'critical-defect-results').glob('*/failure.json')):
        d=p.parent;failed.append({'run_directory':str(d),'failure_sha256':sha(p),'files_sha256':{f.name:sha(f) for f in d.glob('*.json') if f.name!='failure.json'},
            'excluded_final_scales':read(d/'final_cases.json')['scales'] if (d/'final_cases.json').exists() else []})
    return {'schema':1,'grammar_version':g.VERSION,'source_run':str(source),'source_sha256':{n:sha(source/n) for n in ['protocol.json','verification.json','summary.json','rational_fractional_contract_verification.json']},
        'code_sha256':dict(old['code_sha256'],**{n:sha(BASE/n) for n in CODE+EXTRA}),'this_stage_source_files':CODE,'named_calibration_dependencies':old['named_calibration_dependencies'],
        'target':'every cofinal epsilon>0: exists finite B_epsilon, every dyadic X>=1, A_2(2X)-4*A_2(X)<=B_epsilon*X^(2+epsilon)',
        'one_sided_upper_bound':True,'unfiltered_actual_mertens_is_recovering_calibration':True,'cofinal_epsilons_needed':True,'critical_zero_simplicity_assumed':False,
        'training_scales':[8,16,32,64,128],'validation_scales':[256,512,1024],'cutoff_grammar_denominators':list(range(1,13)),
        'arbitrary_rational_exponents_have_semantics':True,'semantic_denominator_cap':False,'maximum_native_primitive_cutoff':64,'epsilon_fit_values':['1/2','1/3','1/6','1/12'],
        'selection_rule':'largest coverage cutoff power with proved component power <=2; no full-defect proof inferred; finite residual leads retained',
        'component_method':'gcd primitive pairs; elementary coprime squarefree density; shared-cutoff leading cancellation',
        'component_proof_method_supplied':True,'guided_mathematical_audit_not_anonymous_operator_invention':True,'adaptive_promotion_claimed':False,
        'final_case_generation':{'dyadic_exponent_range':[11,15],'scale_count':2,'density_geometries':12},'retained_failed_runs_are_development':failed,
        'generation_literature_network_model_or_prime_oracle_access':False,'actual_prime_or_factor_oracle_used_by_producer':False,'new_prime_distribution_estimate_imported':False,
        'global_full_signed_defect_proved':False,'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False}


def restrict(d,spec):
    allowed={str((BASE/n).resolve()) for n in spec['code_sha256']}|{str((d/n).resolve()) for n in SEALED+['seal.json']}
    def audit(event,args):
        if event=='open' and not isinstance(args[0],int) and str(Path(args[0]).resolve()) not in allowed:raise PermissionError('Audit worker access denied')
        if event.startswith('socket.') or event in ['subprocess.Popen','os.system','os.posix_spawn','os.posix_spawnp']:raise PermissionError('External access denied')
    sys.addaudithook(audit);denied={}
    for label,fn in [('fresh_final',lambda:open(d/'final_cases.json')),('parent_outcomes',lambda:open(Path(spec['source_run'])/'final_evaluation.json')),
        ('root_registry',lambda:open(BASE/'root-results/candidate_registry.json')),('literature',lambda:open(spec['named_calibration_dependencies'][0]['path'])),
        ('network',lambda:socket.socket()),('subprocess',lambda:subprocess.run([sys.executable,'-c','pass']))]:
        try:fn()
        except PermissionError:denied[label]=True
        else:raise AssertionError('Isolation failed')
    return denied


def data(spec,scales,candidates):
    N=max(4*max(scales),spec['maximum_native_primitive_cutoff']**2);values=g.inverse_one_prefix(N);rows=[]
    for X in scales:
        whole=g.whole(values,X);Bmap={p['id']:g.floor_power(X,p['beta']) for p in candidates};cutoffs=sorted({B for B in Bmap.values() if B is not None and B<=spec['maximum_native_primitive_cutoff']});grid=g.projection_grid(values,X,cutoffs);byB={r['shared_cutoff']:r for r in grid['cutoff_rows']};records=[]
        for p in candidates:
            B=Bmap[p['id']]
            if B is None or B>spec['maximum_native_primitive_cutoff']:records.append({'candidate_id':p['id'],'missing':True,'reason':'native_cutoff_resources_exhausted','missing_not_counterexample':True,'semantic_cutoff':B});continue
            c=byB[B];records.append({'candidate_id':p['id'],'missing':False,'shared_cutoff':B,'signed_projection_defect':c['signed_projection_defect'],'signed_dense_residual_defect':whole['off_diagonal_defect']-c['signed_projection_defect'],
                'whole_defect_reconstructed':whole['diagonal_defect']+c['signed_projection_defect']+(whole['off_diagonal_defect']-c['signed_projection_defect'])})
        rows.append({'whole':whole,'projection_grid':grid,'candidate_observations':records});print('Complete signed defect and primitive pairs at X',X,flush=True)
    return {'cutoff':N,'divisor_inverse_sha256':digest(values),'complete_coefficient_prefix':values,'scales':scales,'rows':rows,'producer_prime_or_factor_oracle_used':False}


def growth(X,epsilon):return g.rational_power(g.real(X),2+Q(epsilon))


def fit_constants(training,candidates,spec):
    estimates=[];flint.ctx.prec=512
    for p in candidates:
        if not p['certificate']['component_admits_every_positive_epsilon_critical_bound']:continue
        for epsilon in spec['epsilon_fit_values']:
            observations=[]
            for row in training['rows']:
                o=next(o for o in row['candidate_observations'] if o['candidate_id']==p['id'])
                if not o['missing']:observations.append(max(o['signed_dense_residual_defect'],0)/growth(row['whole']['X'],epsilon))
            C=max(observations,key=lambda v:float(v.upper()))*g.real(Q(5,4));C=max(1,g.integer_guard(C*2**64));constant=str(Q(C,2**64))
            estimates.append({'id':digest({'candidate_id':p['id'],'epsilon':epsilon}),'candidate_id':p['id'],'epsilon':epsilon,'constant':constant,
                'uniform_residual_premise_proved':False,'finite_fit_is_not_full_defect_certificate':True})
    return estimates


def evaluate(data,estimates):
    results=[]
    for e in estimates:
        observations=[]
        for row in data['rows']:
            o=next(o for o in row['candidate_observations'] if o['candidate_id']==e['candidate_id'])
            if not o['missing']:observations.append(float((g.real(max(o['signed_dense_residual_defect'],0))/(g.real(Q(e['constant']))*growth(row['whole']['X'],e['epsilon']))).upper()))
        results.append(dict(e,maximum_finite_ratio=max(observations,default=None),finite_pass=bool(observations) and max(observations)<=1))
    return results


def worker(d):
    spec=read(d/'protocol.json');verify_code(spec);denied=restrict(d,spec);powers=sorted({Q(n,k) for k in spec['cutoff_grammar_denominators'] for n in range(k+1)});candidates=[{'id':digest({'beta':str(b)}),'beta':str(b),'certificate':g.component_certificate(b)} for b in powers]
    training=data(spec,spec['training_scales'],candidates);estimates=fit_constants(training,candidates,spec)
    batch={'protocol_sha256':digest(spec),'candidates':candidates,'training':training,'residual_estimates':estimates,'access_denials':denied,
        'candidate_batch_frozen_before_validation':True,'guided_targeted_bound_audit':True,'expected_winning_cutoff_supplied':False};write(d/'candidate_batch.json',batch)
    validation=data(spec,spec['validation_scales'],candidates);results=evaluate(validation,estimates);write(d/'validation.json',{'data':validation,'estimates':results,'all_candidates_retained':True,'final_data_used':False})
    admitted=[p for p in candidates if p['certificate']['component_admits_every_positive_epsilon_critical_bound']];selected=max(admitted,key=lambda p:(Q(p['beta']),p['id']));arc={'selected_component_candidate_id':selected['id'],'selected_cutoff_power':selected['beta'],
        'residual_estimates':[r for r in results if r['candidate_id']==selected['id']],'all_residual_leads_retained_in_validation':True,'selection_closed':True,'final_data_used':False,
        'full_defect_proof_status':'missing_uniform_dense_signed_residual_bound','cofinal_recovery_certificate':g.cofinal_recovery(),'uniform_RH_sufficient_signed_controls_verified':[]};write(d/'archive.json',arc)
    write(d/'seal.json',{'protocol_sha256':digest(spec),'files':{n:sha(d/n) for n in SEALED},'selection_closed':True,'final_cases_exist':False});print('Sealed critical signed-defect decomposition and exact unresolved residual',flush=True)


def final(d):
    spec=read(d/'protocol.json');verify_code(spec);batch=read(d/'candidate_batch.json');arc=read(d/'archive.json');rule=spec['final_case_generation'];rng=random.Random(int.from_bytes(os.urandom(32),'big'));excluded={n for f in spec['retained_failed_runs_are_development'] for n in f['excluded_final_scales']};available=[2**j for j in range(rule['dyadic_exponent_range'][0],rule['dyadic_exponent_range'][1]+1) if 2**j not in excluded];scales=sorted(rng.sample(available,rule['scale_count']));geometries=[{'modulus':rng.randint(1,96),'y':str(Q(rng.randint(0,8000),rng.choice([1,2,3,6])))} for _ in range(rule['density_geometries'])]
    cases={'scales':scales,'density_geometries':geometries,'generated_after_seal':True,'seal_sha256':sha(d/'seal.json')};write(d/'final_cases.json',cases);actual=data(spec,scales,batch['candidates']);density=[]
    for row in geometries:
        k=row['modulus'];y=Q(row['y']);n=y.numerator//y.denominator;c,tau=g.divisor_density(actual['complete_coefficient_prefix'],k);count=sum(actual['complete_coefficient_prefix'][h]**2 for h in range(1,n+1) if __import__('math').gcd(h,k)==1);density.append(dict(row,count=count,density_ball=g.ball(c),tau_radical=tau,bound_ball=g.ball((tau+2)*g.real(y).sqrt())))
    positive=[];delayed=[];tail=4*max(spec['validation_scales']);mu=actual['complete_coefficient_prefix'];values=[0]+[1]*(len(mu)-1);fake=mu[:tail+1]+[1]*(len(mu)-tail-1)
    for X in scales:
        B=g.floor_power(X,arc['selected_cutoff_power']);whole=g.whole(values,X);positive.append({'whole':whole,'projection':g.positive_projection(X,B),'shared_cutoff':B,'analytic_full_defect_formula':str(Q(28*X**3-X,3))});delayed.append(g.whole(fake,X))
    controls={'positive_projection_does_not_control_full_defect':all(r['whole']['signed_defect']==Q(r['analytic_full_defect_formula']) for r in positive),
        'generic_sequence_not_actual_prime_density':True,'delayed_positive_tail_is_counterfeit_arithmetic':True,'delayed_tail_matches_all_development_coefficients':fake[:tail+1]==mu[:tail+1],
        'separate_cutoffs_not_same_proved_defect':not g.component_certificate(arc['selected_cutoff_power'],False)['admitted'],
        'finite_epsilon_list_not_cofinal_proof':not g.cofinal_recovery(epsilon_tends_to_zero=False)['admitted'],
        'finite_scales_not_uniform_proof':not g.cofinal_recovery(all_dyadic_scales=False)['admitted'],
        'generic_model_not_ordinary_zeta':not g.cofinal_recovery(arithmetic_model='generic_sequence')['admitted']}
    write(d/'final_evaluation.json',{'protocol_sha256':digest(spec),'cases_sha256':digest(cases),'data':actual,'density_observations':density,
        'residual_estimate_evaluations':evaluate(actual,arc['residual_estimates']),'positive_coefficient_controls':positive,'delayed_tail_controls':delayed,
        'delayed_tail_starts_after':tail,'negative_controls':controls,'global_full_signed_defect_proved':False,'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False})


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('mode',nargs='?',default='run',choices=['run','worker']);p.add_argument('--run-dir',type=Path,required=True);p.add_argument('--source',type=Path);args=p.parse_args();d=args.run_dir.resolve()
    if args.mode=='worker':worker(d);return
    if args.source is None:raise ValueError('Verified preceding source required')
    d.mkdir(parents=True,exist_ok=False);spec=protocol(args.source);write(d/'protocol.json',spec);(d/'frozen_source').mkdir()
    for n in CODE:(d/'frozen_source'/n).write_bytes((BASE/n).read_bytes())
    try:
        subprocess.run([sys.executable,str(BASE/'critical_defect_search.py'),'worker','--run-dir',str(d)],cwd=BASE,check=True);final(d)
        subprocess.run([sys.executable,str(BASE/'check_critical_defects.py'),'--run-dir',str(d)],cwd=BASE,check=True)
        from critical_defect_report import summary,text_report
        s=summary(d);write(d/'summary.json',s);(d/'report.txt').write_text(text_report(s));write(BASE/'critical-defect-results/latest.json',{'run_directory':str(d)})
    except Exception as e:write(d/'failure.json',{'error_type':type(e).__name__,'error':str(e),'original_data_and_sources_retained':True});raise


if __name__=='__main__':main()
