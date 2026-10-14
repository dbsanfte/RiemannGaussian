#!/usr/bin/env python3
"""Frozen divisor-response inference and proof-oriented full-defect matrices."""
from fractions import Fraction as Q
from pathlib import Path
from math import gcd,lcm
import argparse,os,random,socket,subprocess,sys
import flint
from stable_scale_search import BASE,read,write,sha,digest,verify_code
import divisor_dual_grammar as g

CODE=['divisor_dual_grammar.py','divisor_dual_search.py','check_divisor_dual.py','divisor_dual_report.py',
      'divisor_dual_proof.txt','test_divisor_dual_contracts.py','plot_divisor_dual.py']
SEALED=['protocol.json','candidate_batch.json','validation.json','archive.json','proof_queue.json']


def protocol(source):
    from critical_defect_report import summary
    source=Path(source).resolve();summary(source);old=read(source/'protocol.json');failed=[]
    for p in sorted((BASE/'divisor-dual-results').glob('*/failure.json')):
        d=p.parent;failed.append({'run_directory':str(d),'failure_sha256':sha(p),'files_sha256':{f.name:sha(f) for f in d.glob('*.json') if f.name!='failure.json'},
            'excluded_final_scales':read(d/'final_cases.json')['scales'] if (d/'final_cases.json').exists() else []})
    return {'schema':1,'grammar_version':g.VERSION,'seed':2026100827,'source_run':str(source),'source_sha256':{n:sha(source/n) for n in ['protocol.json','verification.json','summary.json']},
        'code_sha256':dict(old['code_sha256'],**{n:sha(BASE/n) for n in CODE}),'this_stage_source_files':CODE,'named_calibration_dependencies':old['named_calibration_dependencies'],
        'training_scales':[2,4,8,16],'training_levels':[2,3,6],'validation_scales':[20,24],'validation_levels':[2,3,6],
        'development_matrix_probes':[4,8,16],'precision':512,'mask_response_cutoff':48,'kernel_response_dimensions':[6,10,14],
        'baseline_masks':[{'kind':'constant','value':1},{'kind':'residue','modulus':2,'residue':0},{'kind':'divisible_union','bases':[2,3]},{'kind':'prefix','power':'1/3'}],
        'diagonal_coefficients':['1/4','1','4'],'level_powers':['0','1/6','1/3','1/2','1','2'],'Gram_powers':['2','9/2','5','6'],'Gram_coefficients':['1/4','1','4'],
        'profiles_per_mask':12,'profile_sampling':'balanced cyclic coverage of level powers, three seeded profiles per Gram-power family',
        'mask_feature_dictionary':'constant; above thresholds 1,2,3,4; residues mod 2,3,4; unions of divisibility by 2,3; prefixes with powers 0,1/6,1/3,1/2,1; squares',
        'kernel_feature_dictionary':['floor(N/lcm(i,j))','N/lcm(i,j)','floor(N/gcd(i,j))','floor(N/max(i,j))','floor(N/min(i,j))','delta(i,j)','delta(i,1)*delta(j,1)','1'],
        'kernel_fit_rule':'single feature exact rational least squares plus integer rounding; all alternatives retained',
        'mask_promotion_rule':'minimum exact squared zero-forcing residual, then description length and stable id; only zero-residual masks promoted',
        'mask_promotion_slots':1,'ablation_rule':'one equal-slot random dictionary mask; identical scalar profiles and response data',
        'ranking':'finite proof coverage, then maximum fully charged bound/generic whole-defect bound, then description length and stable id',
        'archive_rule':'best finite native certificate per level-constant-power and mode; analytic dispositions never change that frozen selection',
        'workflow':'detector responses, sealed candidate selection and proof queue, protected final evaluation, separate analytical proof attempts, independently checked dispositions, feedback only to a fresh next run',
        'proof_queue_rule':'exact selected templates, quantified global PSD claim, complete charged cost, validation evidence, missing lemma; no outcome-driven formula edits',
        'named_global_calibration':{'level':1,'diagonal_coefficient':'4','ordinary_energy_power':'3','method':'H row-norm <=8X^2'},
        'final_cases':{'scale_range':[25,32],'count':2,'level_range':[4,12],'level_count':2,'large_scale_range':[48,64],'large_count':1},
        'retained_failed_runs_are_development':failed,'matrix_generator_uses_inverse_or_prime_or_factor_oracle':False,
        'response_calibration_uses_full_divisor_inverse_without_factor_oracle':True,'historical_priority_is_acceptance_gate':False,'semantic_denominator_cap':False,
        'feature_and_certificate_methods_supplied':True,'not_autonomous_proof_invention':True,'new_prime_distribution_estimate_imported':False,
        'global_critical_matrix_PSD_proved':False,'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False}


def restrict(d,spec):
    allowed={str((BASE/n).resolve()) for n in spec['code_sha256']}|{str((d/n).resolve()) for n in SEALED+['seal.json']}
    def audit(event,args):
        if event=='open' and not isinstance(args[0],int) and str(Path(args[0]).resolve()) not in allowed:raise PermissionError('Learning worker access denied')
        if event.startswith('socket.') or event in ['subprocess.Popen','os.system','os.posix_spawn','os.posix_spawnp']:raise PermissionError('External access denied')
    sys.addaudithook(audit);denied={}
    for label,fn in [('final_cases',lambda:open(d/'final_cases.json')),('parent_outcomes',lambda:open(Path(spec['source_run'])/'final_evaluation.json')),
        ('root_registry',lambda:open(BASE/'root-results/candidate_registry.json')),('literature',lambda:open(spec['named_calibration_dependencies'][0]['path'])),
        ('network',lambda:socket.socket()),('subprocess',lambda:subprocess.run([sys.executable,'-c','pass']))]:
        try:fn()
        except PermissionError:denied[label]=True
        else:raise AssertionError('Isolation failed')
    return denied


def masks():
    out=[{'kind':'constant','value':1}]+[{'kind':'above','threshold':k} for k in [1,2,3,4]]
    out +=[{'kind':'residue','modulus':m,'residue':r} for m in [2,3,4] for r in range(m)]+[{'kind':'divisible_union','bases':[2,3]}]
    out +=[{'kind':'prefix','power':b} for b in ['0','1/6','1/3','1/2','1']]+[{'kind':'square'}]
    return out


def mask_inference(responses,features):
    """Anonymous rows and feature columns; no expected mask is provided."""
    target=[int(all(v==0 for v in row)) for row in responses];fits=[]
    for description,values in features:
        residual=sum((y-v)**2 for y,v in zip(target,values));fits.append({'mask':description,'exact_squared_residual':residual,'description_length':len(str(description)),
            'operator_names_or_expected_mask_supplied':False,'universal_response_pattern_claimed':False})
    return sorted(fits,key=lambda row:(row['exact_squared_residual'],row['description_length'],digest(row['mask'])))


def kernel_features(N,i,j):
    return {'floor(N/lcm(i,j))':Q(N//lcm(i,j)),'N/lcm(i,j)':Q(N,lcm(i,j)),'floor(N/gcd(i,j))':Q(N//gcd(i,j)),
        'floor(N/max(i,j))':Q(N//max(i,j)),'floor(N/min(i,j))':Q(N//min(i,j)),'delta(i,j)':Q(i==j),'delta(i,1)*delta(j,1)':Q(i==j==1),'1':Q(1)}


def kernel_inference(response,features):
    norm=sum(y*y for y in response) or 1;out=[]
    for name,values in features.items():
        xx=sum(x*x for x in values)
        if not xx:continue
        coefficient=(sum(x*y for x,y in zip(values,response))/xx).limit_denominator(64);error=sum((y-coefficient*x)**2 for x,y in zip(values,response))/norm
        out.append({'feature':name,'coefficient':str(coefficient),'relative_squared_residual':str(error),'expected_kernel_or_coefficient_supplied':False})
    return sorted(out,key=lambda r:(Q(r['relative_squared_residual']),len(r['feature']),r['feature']))


def generic_upper(X):return Q(56*X**3,3)-6*X**2+Q(X,3)


def evaluate(programs,scales,levels,spec):
    rows=[]
    for X in scales:
        for q in levels:
            for row in programs:
                cert=g.certify(row['program'],X,q,spec['precision']);cost=None if cert.get('missing') else Q(cert['parameters']['charged_defect_bound']);rows.append({'program_id':row['id'],'X':X,'level':q,'certificate':cert,
                    'fully_charged_bound_over_generic':None if cost is None else str(cost/generic_upper(X))})
        print('Proof-oriented full-defect matrices through X',X,flush=True)
    return rows


def scores(programs,results):
    out=[]
    for p in programs:
        rows=[r for r in results if r['program_id']==p['id']];valid=[r for r in rows if r['certificate'].get('finite_matrix_PSD')];out.append({'program_id':p['id'],'positive_matrix_cases':len(valid),'total_cases':len(rows),
            'maximum_charged_bound_over_generic':str(max((Q(r['fully_charged_bound_over_generic']) for r in valid),default=Q(10**100))),
            'cofinal_matrix_family_ruled_out':p['family_certificate'].get('cofinal_critical_matrix_family_analytically_ruled_out',False),'global_critical_PSD_proved':False})
    return out


def key(score,program):return (-score['positive_matrix_cases'],Q(score['maximum_charged_bound_over_generic']),len(str(program['program'])),score['program_id'])


def worker(d):
    spec=read(d/'protocol.json');verify_code(spec);g.np.linalg.eigh(g.np.eye(2));denied=restrict(d,spec);rng=random.Random(spec['seed']);dictionary=masks();N=spec['mask_response_cutoff'];inputs=[['0']+['1']*N]
    for seed in [13,31]:
        r=random.Random(seed);inputs.append(['0','1']+[str(Q(r.randint(-7,7),r.randint(1,5))) for _ in range(N-1)])
    forcing=[g.forcing(f) for f in inputs];response=[[Q(t['anonymous_response'][i]) for t in forcing] for i in range(N)];features=[(m,[g.mask_value(m,n,N) for n in range(1,N+1)]) for m in dictionary];fits=mask_inference(response,features)
    kr=[];kf={name:[] for name in spec['kernel_feature_dictionary']};observations=[]
    for size in spec['kernel_response_dimensions']:
        table=g.gram({'kind':'constant','value':1},size)
        for i in range(1,size+1):
            for j in range(1,size+1):
                kr.append(Q(table[i-1][j-1]));f=kernel_features(size,i,j);observations.append({'dimension':size,'i':i,'j':j,'value':table[i-1][j-1]})
                for name in kf:kf[name].append(f[name])
    kernel_fits=kernel_inference(kr,kf);best=kernel_fits[0];kernel_admission=best['feature']=='floor(N/lcm(i,j))' and Q(best['coefficient'])==1 and not Q(best['relative_squared_residual'])
    profiles=[];rp=spec['level_powers'][:];rng.shuffle(rp)
    for index,gamma in enumerate(spec['Gram_powers']):
        for j in range(3):profiles.append({'arithmetic_model':'inverse_one','diagonal_coefficient':rng.choice(spec['diagonal_coefficients']),'level_power':rp[(3*index+j)%len(rp)],
            'Gram_power':gamma,'Gram_coefficient':rng.choice(spec['Gram_coefficients'])})
    programs=[];ids={}
    def add(mask,origin):
        for profile in profiles:
            p=dict(profile,mask=mask);pid=digest(p)
            if pid not in ids:row={'id':pid,'program':p,'origin':origin,'family_certificate':g.family_certificate(p)};programs.append(row);ids[pid]=row
    for mask in spec['baseline_masks']:add(mask,'baseline')
    promotions=[];abla=[]
    for fit in fits:
        if fit['exact_squared_residual'] or len(promotions)>=spec['mask_promotion_slots']:break
        if fit['mask']in spec['baseline_masks']:continue
        add(fit['mask'],'learned_zero_forcing_mask');promotions.append({'mask':fit['mask'],'evidence':fit,'same_operator_as_baseline':False,'all_index_mask_semantics_preserved':True,'unit_forcing_charge':g.mask_value(fit['mask'],1,4),
            'dependency':'complete unit-normalized inverse response, finite single-feature fit, exact inverse identity'});pool=[m for m in dictionary if m not in spec['baseline_masks'] and m!=fit['mask']];am=rng.choice(pool);add(am,'equal_slot_random_mask');abla.append(am)
    training=evaluate(programs,spec['training_scales'],spec['training_levels'],spec);batch={'protocol_sha256':digest(spec),'programs':programs,'profiles':profiles,'forcing_calibrations':forcing,
        'mask_inferences':fits,'kernel_response_observations':observations,'kernel_inferences':kernel_fits,'kernel_exact_admission':kernel_admission,'promotions':promotions,'ablation_masks':abla,
        'training_matrix_certificates':training,'access_denials':denied,'candidate_batch_frozen_before_validation':True,'expected_winning_formula_supplied':False};write(d/'candidate_batch.json',batch)
    validation=evaluate(programs,spec['validation_scales'],spec['validation_levels'],spec);vs=scores(programs,validation);write(d/'validation.json',{'matrix_certificates':validation,'scores':vs,'all_candidates_retained':True,'final_data_used':False});byid={r['program_id']:r for r in vs};base={p['id'] for p in programs if p['origin']=='baseline'};archive=[];comparison=[]
    for mode,origin in [('primary','learned_zero_forcing_mask'),('promotion_disabled','equal_slot_random_mask')]:
        pids=base|{p['id'] for p in programs if p['origin']==origin};eligible=[p for p in programs if p['id']in pids and p['family_certificate']['admitted']]
        for power in spec['level_powers']:
            rows=[p for p in eligible if p['program']['level_power']==power]
            if rows:chosen=min(rows,key=lambda p:key(byid[p['id']],p));archive.append({'mode':mode,'program_id':chosen['id'],'level_power':power,'validation_score':byid[chosen['id']]})
        best=min(eligible,key=lambda p:key(byid[p['id']],p)) if eligible else None;comparison.append({'mode':mode,'best_program_id':None if best is None else best['id'],'best_validation_score':None if best is None else byid[best['id']],
            'extra_profiles_per_mask':len(profiles),'extra_mask_slots':len(promotions),'same_response_and_scalar_profile_budget':True,'global_critical_PSD_proved':False})
    calibration=dict(profiles[0],mask={'kind':'above','threshold':1},diagonal_coefficient='4');cal=g.certify(calibration,4,1,spec['precision']);write(d/'archive.json',{'selection_closed':True,'final_data_used':False,'matrix_leads':archive,
        'ablation_comparison':comparison,'global_generic_calibration':{'program':calibration,'certificate':cal},'all_height_RH_premise':'cofinal sufficiently large q, every dyadic X, matrix PSD and fully charged cost',
        'uniform_RH_sufficient_signed_controls_verified':[]})
    queue=[]
    for pid in sorted({r['program_id'] for r in archive}):
        row=ids[pid];queue.append({'program_id':pid,'exact_program':row['program'],'detector_origins':[r['mode'] for r in archive if r['program_id']==pid],
            'validation_evidence':byid[pid],'global_claim':'exists finite q0, every integer q>=q0, every dyadic X>=1: the exact S_(X,q) is PSD',
            'cost_formula':'4*X*D(X,q)+Y(X)*mask(1,4X), with the original exact ceilings and coefficients',
            'RH_recovery_certificate':row['family_certificate'],'missing_lemma':'uniform PSD comparison for this exact template',
            'proof_status':'pending_separate_analytic_attempt','formula_changed_after_detection':False})
    write(d/'proof_queue.json',{'protocol_sha256':digest(spec),'candidate_ids_frozen_before_final':True,'queue':queue,'final_data_used_for_selection':False,'analytic_results_must_not_edit_frozen_candidates':True})
    write(d/'seal.json',{'protocol_sha256':digest(spec),'files':{n:sha(d/n) for n in SEALED},'selection_closed':True,'final_cases_exist':False});print('Sealed divisor-Gram inference, mask promotion and full-defect proof queue',flush=True)


def local_inverse_vector(N,bases):
    out=[0]
    for n in range(1,N+1):
        value=1
        for p in bases:
            if n%(p*p)==0:value=0;break
            if n%p==0:value=-value
        out.append(value)
    return out


def controls(d,spec,scales,level):
    entries=[]
    for bases in [[2],[2,3]]:
        for X in scales:
            N=4*X;v=local_inverse_vector(N,bases);M=[0]
            for z in v[1:]:M.append(M[-1]+z)
            row_zeros=[sum(v[t] for t in range(1,n+1) if n%t==0)==0 for n in range(1,N+1) if any(n%p==0 for p in bases)];Delta=sum(M[n]**2 for n in range(2*X,4*X))-4*sum(M[n]**2 for n in range(X,2*X));c=Q(1)
            for p in bases:c*=Q(p-1,p)**2
            R=4**len(bases);entries.append({'bases':bases,'X':X,'values':v,'all_selected_divisor_rows_zero':all(row_zeros),'full_signed_defect':Delta,'linear_mean':str(c),
                'positive_cubic_leading_coefficient':str(Q(28,3)*c*c),'all_scale_cubic_error_upper':str(24*c*R*X**2+6*R**2*X),
                'counterfeit_arithmetic_not_actual_mobius':True,'rejects_global_pruned_matrix_certificate_not_RH':True})
    f=['0','1','-1000']+['1']*14;forcing=g.forcing(f);bad_norm=max(abs(Q(v)) for v in forcing['inverse'][1:])>1
    return {'finite_prime_row_controls':entries,'generic_large_inverse_control':forcing,'negative_controls':{'generic_inverse_norm_does_not_transfer':bad_norm,
        'generic_model_not_actual_zeta':not g.family_certificate(dict(spec['control_reference_program'],arithmetic_model='generic_sequence'))['admitted'],
        'selected_prime_row_constraints_are_not_complete_inverse':all(e['all_selected_divisor_rows_zero'] for e in entries),
        'finite_PSD_is_not_global_PSD':True,'negative_matrix_direction_is_not_actual_RH_counterexample':True}}


def final(d):
    spec=read(d/'protocol.json');verify_code(spec);batch=read(d/'candidate_batch.json');arc=read(d/'archive.json');rng=random.Random(int.from_bytes(os.urandom(32),'big'));rule=spec['final_cases'];excluded={n for f in spec['retained_failed_runs_are_development'] for n in f['excluded_final_scales']};scales=sorted(rng.sample([n for n in range(rule['scale_range'][0],rule['scale_range'][1]+1) if n not in excluded],rule['count']));levels=sorted(rng.sample([n for n in range(rule['level_range'][0],rule['level_range'][1]+1) if n not in spec['training_levels']],rule['level_count']));large=rng.choice([n for n in range(rule['large_scale_range'][0],rule['large_scale_range'][1]+1) if n not in excluded]);cases={'scales':scales+[large],'ordinary_scales':scales,'large_probe_scale':large,'levels':levels,'generated_after_seal':True,'seal_sha256':sha(d/'seal.json')};write(d/'final_cases.json',cases)
    pids={r['program_id'] for r in arc['matrix_leads']};programs=[p for p in batch['programs'] if p['id']in pids];evaluations=evaluate(programs,scales,levels,spec);positive=[r for r in arc['matrix_leads'] if r['mode']=='primary' and Q(r['level_power'])>0];large_id=min(positive,key=lambda r:(-r['validation_score']['positive_matrix_cases'],Q(r['validation_score']['maximum_charged_bound_over_generic']),r['program_id']))['program_id'] if positive else programs[0]['id'];large_program=next(p for p in programs if p['id']==large_id);evaluations+=evaluate([large_program],[large],[levels[0]],spec)
    spec_control=dict(spec,control_reference_program=programs[0]['program']);negative=controls(d,spec_control,scales,levels[0]);mu=g.inverse_one_prefix(4*max(cases['scales']));M=[0]
    for v in mu[1:]:M.append(M[-1]+v)
    actual=[]
    for X in cases['scales']:actual.append({'X':X,'exact_actual_signed_defect':sum(M[n]**2 for n in range(2*X,4*X))-4*sum(M[n]**2 for n in range(X,2*X))})
    write(d/'final_evaluation.json',{'protocol_sha256':digest(spec),'cases_sha256':digest(cases),'matrix_certificates':evaluations,'actual_mobius_prefix':mu,'actual_signed_defects':actual,'controls':negative,
        'large_probe_program_id':large_id,'global_critical_matrix_PSD_proved':False,'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False})


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('mode',nargs='?',default='run',choices=['run','worker']);p.add_argument('--run-dir',type=Path,required=True);p.add_argument('--source',type=Path);args=p.parse_args();d=args.run_dir.resolve()
    if args.mode=='worker':worker(d);return
    if args.source is None:raise ValueError('Verified full signed-defect source required')
    d.mkdir(parents=True,exist_ok=False);spec=protocol(args.source);write(d/'protocol.json',spec);(d/'frozen_source').mkdir()
    for n in CODE:(d/'frozen_source'/n).write_bytes((BASE/n).read_bytes())
    try:
        subprocess.run([sys.executable,str(BASE/'divisor_dual_search.py'),'worker','--run-dir',str(d)],cwd=BASE,check=True);final(d)
        subprocess.run([sys.executable,str(BASE/'check_divisor_dual.py'),'--run-dir',str(d)],cwd=BASE,check=True)
        from divisor_dual_report import summary,text_report
        s=summary(d);write(d/'summary.json',s);(d/'report.txt').write_text(text_report(s));write(BASE/'divisor-dual-results/latest.json',{'run_directory':str(d)})
    except Exception as e:write(d/'failure.json',{'error_type':type(e).__name__,'error':str(e),'original_data_and_sources_retained':True});raise


if __name__=='__main__':main()
