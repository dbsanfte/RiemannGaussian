#!/usr/bin/env python3
"""Frozen anonymous centered arithmetic, parameter promotion and fresh tests."""
from fractions import Fraction as Q
from itertools import combinations,product
from math import ceil,factorial
from pathlib import Path
import argparse,os,random,socket,subprocess,sys
import flint
from stable_scale_search import BASE,read,write,sha,digest,verify_code
from mellin_kernel_grammar import real,power
from root_lattice_search import solve
import branch_center_grammar as g

CODE=['branch_center_grammar.py','branch_center_search.py','check_branch_centers.py','branch_center_report.py',
      'branch_center_proof.txt','test_branch_center_contracts.py','plot_branch_centers.py']
SEALED=['protocol.json','candidate_batch.json','validation.json','archive.json']


def protocol(source):
    from divisor_preconditioner_report import summary
    source=Path(source).resolve();summary(source);old=read(source/'protocol.json');failed=[]
    for p in sorted((BASE/'branch-center-results').glob('*/failure.json')):
        d=p.parent;failed.append({'run_directory':str(d),'failure_sha256':sha(p),'files_sha256':{f.name:sha(f) for f in d.glob('*.json') if f.name!='failure.json'},
            'excluded_final_scales':read(d/'final_cases.json')['integers'] if (d/'final_cases.json').exists() else []})
    return {'schema':1,'grammar_version':g.VERSION,'seed':2026100825,'source_run':str(source),'source_sha256':{n:sha(source/n) for n in ['protocol.json','verification.json','summary.json']},
        'code_sha256':dict(old['code_sha256'],**{n:sha(BASE/n) for n in CODE}),'this_stage_source_files':CODE,'named_calibration_dependencies':old['named_calibration_dependencies'],
        'precision':384,'center_quadrature_bits':96,'center_native_method':'analytic Taylor, Rouche disk radius 5/4, 448..1024 terms, weighted Cauchy remainder','base_roots':['1/2','1/3','1/6','1/4'],
        'evaluation_root_pool':['1/2','1/3','1/6','1/4','1/12','1/8'],'all_rational_roots_in_open_unit_interval_supported':True,'semantic_denominator_cap':False,
        'training_levels':[2,6,12],'validation_levels':[5,17],'training_points':[4,8,16,32,64,128],'validation_points':[192,257,384],
        'baseline_rule':'four single atoms, both signs for every two-atom pair, four seeded signed rational programs',
        'random_slots':4,'maximum_atoms':6,'anonymous_features':'actual centered response columns, all training levels/scales; no prime labels or analytic constants',
        'learning_quantization_bits':60,'learning_rounding_denominator':256,'learner_expected_weights_or_formula_supplied':False,
        'promotion_rule':'rank primary by fully charged critical observer cost; scan ranked parents, skip already present child semantics, fill four new-family slots by P(t)-2^m P(t/2); recheck nonzero recovery',
        'promotion_slots':4,'promotion_depth':1,'ablation':'same baseline and learned programs; four independent seeded random rational slots on the same predeclared root pool and data budget',
        'growth_grammar':{'eta':['1/2','3/4','1'],'epsilon':['1/16','1/4'],'nu':['1/6','1','2'],'log_degree':['0','1/6','1']},
        'fit_rule':'one free constant per sampled q, 5/4 times maximum training ratio plus 1e-28; never a uniform certificate',
        'archive_rule':'each program retains its best critical target and best predictive target; numerical failures and missing certificates retained',
        'observer_query':{'s_real':'5/8','s_imag':'16'},'promotion_score_target':{'eta':'1/2','epsilon':'1/16','nu':'1','log_degree':'0'},
        'final_cases':{'level_range':[19,41],'level_count':2,'range':[1025,2048],'count':2,'offset':'1/3','boundary':[1,2]},
        'final_constant_order':'new q after seal, fixed training scales for C_q, freeze constants, then generate fresh x',
        'parent_final_scales_excluded':read(source/'final_cases.json')['integers'],'retained_failed_runs_are_development':failed,
        'proof_backends':['Bernstein prime differences','full branch Cauchy center','Euler continuation entire in exponent','Vandermonde and eventual parameter moment dominance',
            'ordinary zero cofinal parameter identity theorem and zeta pole obstruction','all-real-scale weak envelope','incomplete leading-center branch obstruction'],
        'supplied_assumptions':['fractional log weighting and divisor inversion','a full real-cut center','finite positive rational parameter bases and signed rational weights',
            'bounded anonymous linear fitting','critical-growth hypothesis families','first-moment annihilator promotion','classical complex analysis and functional equation'],
        'generator_model_literature_network_or_prime_oracle_access':False,'new_prime_distribution_estimate_imported':False,'not_autonomous_proof_invention':True,
        'historical_priority_is_acceptance_gate':False,'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False}


def restrict(d,spec):
    allowed={str((BASE/n).resolve()) for n in spec['code_sha256']};allowed|={str((d/n).resolve()) for n in SEALED+['seal.json']}
    def audit(event,args):
        if event=='open' and not isinstance(args[0],int) and str(Path(args[0]).resolve()) not in allowed:raise PermissionError('Discovery access denied')
        if event.startswith('socket.') or event in ['subprocess.Popen','os.system','os.posix_spawn','os.posix_spawnp']:raise PermissionError('External access denied')
    sys.addaudithook(audit);denied={}
    probes=[('private_final',lambda:open(d/'final_cases.json')),('private_constants',lambda:open(d/'final_constants.json')),
        ('parent_outcomes',lambda:open(Path(spec['source_run'])/'final_evaluation.json')),('literature',lambda:open(spec['named_calibration_dependencies'][0]['path'])),
        ('network',lambda:socket.socket()),('subprocess',lambda:subprocess.run([sys.executable,'-c','pass']))]
    for label,fn in probes:
        try:fn()
        except PermissionError:denied[label]=True
        else:raise AssertionError('Isolation failed')
    return denied


def data(spec,levels,points):
    points=list(map(str,points));N=max(Q(x).numerator//Q(x).denominator for x in points);orders=sorted({Q(b)/q for b in spec['evaluation_root_pool'] for q in levels});tables={};obs={}
    for order in orders:
        key=str(order);table=g.coefficients(order,N,spec['precision']);tables[key]=table;obs[key]={}
        for x in points:
            center=g.complete_center(order,x,spec['precision'],spec['center_quadrature_bits']);T=g.sum_at(table,x)
            obs[key][x]={'sum_ball':g.ball(T),'center':center,'error_ball':None if center['missing'] else g.ball(T-flint.arb(center['value_ball']))}
        print('Complete response',key,'through',N,flush=True)
    return {'tables':tables,'observations':obs,'levels':levels,'points':points,'complete_arithmetic':True}


def evaluate(p,q,x,observations):
    values={str(Q(b)/q):observations[str(Q(b)/q)][str(x)]['error_ball'] for b,w in p['atoms']}
    if any(v is None for v in values.values()):return None
    return g.apply(p,q,values)


def anonymous_learn(columns,spec):
    """This function receives only numeric columns and resource choices."""
    quant=lambda x:Q(round(Q(x.mid().str(75,radius=False))*2**spec['learning_quantization_bits']),2**spec['learning_quantization_bits']);rows=[[quant(v) for v in row] for row in columns];K=len(rows[0]);out=[]
    for target in range(K):
        features=[j for j in range(K) if j!=target];A=[[sum((row[i]*row[j] for row in rows),Q(0)) for j in features] for i in features];b=[sum((row[i]*row[target] for row in rows),Q(0)) for i in features];c=solve(A,b)
        if c is None:out.append({'target_channel':target,'weights':None,'status':'rank_deficient'});continue
        weights=[Q(int(j==target)) for j in range(K)]
        for j,v in zip(features,c):weights[j]=-v.limit_denominator(spec['learning_rounding_denominator'])
        residual=max(abs(row[target]-sum((v*row[j] for j,v in zip(features,c)),Q(0))) for row in rows)
        out.append({'target_channel':target,'weights':list(map(str,weights)),'status':'anonymous_response_combination','fit_residual':str(residual),
            'operator_names_prime_labels_or_analytic_constants_supplied':False,'universal_identity_claimed':False})
    return out


def envelope(h,q,x):
    theta=real(Q(h['eta']))+real(Q(h['epsilon']))/power(real(q),Q(h['nu']));return (theta*real(Q(x)).log()).exp()*power((flint.arb.const_e()+real(Q(x))).log(),Q(h['log_degree']))


def fit_constant(p,h,q,observations,spec):
    vals=[evaluate(p,q,x,observations) for x in spec['training_points']]
    if any(v is None for v in vals):return None
    return 1.25*max(float((abs(v)/envelope(h,q,x)).upper()) for x,v in zip(spec['training_points'],vals))+1e-28


def gap_integral(gap,d):
    D=ceil(Q(d));c=(flint.arb.const_e()+1).log()
    return sum((real(factorial(D)//(factorial(j)*factorial(D-j)))*c**(D-j)*factorial(j)/gap**(j+1) for j in range(D+1)),flint.arb(0))


def charged_cost(p,h,q,C,spec):
    sreal=Q(spec['observer_query']['s_real']);theta=real(Q(h['eta']))+real(Q(h['epsilon']))/power(real(q),Q(h['nu']));gap=real(sreal)-theta
    if C is None:return {'missing':True,'reason':'signed_training_observation_missing'}
    if not gap>0:return {'missing':True,'reason':'no_positive_mellin_gap'}
    o=g.observer(p,q,**spec['observer_query']);
    if o['missing']:return {'missing':True,'reason':o['reason']}
    s=flint.acb(real(sreal),real(Q(spec['observer_query']['s_imag'])));I=gap_integral(gap,h['log_degree']);value=abs(s)*(flint.arb(o['full_cut_center_mellin_upper_ball'])+real(Q(str(C)))*I+flint.arb(o['integer_to_real_guard_ball']))/flint.arb(o['profile_modulus_lower_ball'])
    return {'missing':False,'value':float(value.upper()),'value_ball':g.ball(value),'gap_integral_ball':g.ball(I),'gap_ball':g.ball(gap),'conditional_on_unproved_global_estimate':True,'C_q':C}


def hypotheses(spec):return [dict(zip(['eta','epsilon','nu','log_degree'],v)) for v in product(*(spec['growth_grammar'][k] for k in ['eta','epsilon','nu','log_degree']))]


def worker(d):
    spec=read(d/'protocol.json');verify_code(spec);denied=restrict(d,spec);training=data(spec,spec['training_levels'],spec['training_points']);rng=random.Random(spec['seed']);programs=[];ids={}
    def add(atoms,origin):
        p=g.canonical(atoms);pid=digest(p)
        if pid not in ids:
            row={'id':pid,'program':p,'origin':origin,'recovery_certificate':g.recovery(p)};programs.append(row);ids[pid]=row
        return pid
    bases=spec['base_roots']
    for b in bases:add([(b,1)],'baseline_single')
    for b,c in combinations(bases,2):
        for sign in [-1,1]:add([(b,1),(c,sign)],'baseline_signed_pair')
    def random_atoms(pool):
        while True:
            atoms=[(b,Q(rng.randint(-3,3),rng.choice([1,2,3]))) for b in rng.sample(pool,rng.randint(1,len(pool)))]
            if any(w for b,w in atoms):return atoms
    for slot in range(spec['random_slots']):add(random_atoms(bases),'baseline_random')
    def learning_value(b,q,x):
        v=evaluate(g.canonical([(b,1)]),q,x,training['observations']);return None if v is None else v/(1+real(x))
    columns=[[learning_value(b,q,x) for b in bases] for q in spec['training_levels'] for x in spec['training_points']]
    inferred=anonymous_learn(columns,spec) if not any(v is None for row in columns for v in row) else []
    for row in inferred:
        if row['weights'] is not None:row['decoded_program_id']=add(zip(bases,row['weights']),'anonymous_learned')
    score_h=spec['promotion_score_target'];q=max(spec['training_levels']);scores=[]
    for p in programs:
        C=fit_constant(p['program'],score_h,q,training['observations'],spec);cost=charged_cost(p['program'],score_h,q,C,spec);scores.append({'program_id':p['id'],'cost':cost})
    ranked=sorted(scores,key=lambda row:(row['cost']['missing'],row['cost'].get('value',float('inf')),row['program_id']));prom=[];abl=[]
    for row in ranked:
        if len(prom)>=spec['promotion_slots']:break
        parent=ids[row['program_id']];m=g.moments(parent['program'])[0];atoms=[]
        for b,w in parent['program']['atoms']:atoms.extend([(Q(b),Q(w)),(Q(b)/2,-2**m*Q(w))])
        if digest(g.canonical(atoms)) in ids:continue
        child=add(atoms,'parameter_moment_promotion');prom.append({'parent_id':parent['id'],'child_id':child,'annihilated_moment':m,'same_operator_as_parent':False,'new_family_before_validation':True})
        aid=add(random_atoms(spec['evaluation_root_pool']),'ablation_random_slot');abl.append({'program_id':aid})
    batch={'protocol_sha256':digest(spec),'programs':programs,'training':training,'anonymous_inferences':inferred,'access_denials':denied,'pre_promotion_scores':scores,
        'promotions':prom,'ablation_slots':abl,'candidate_batch_frozen_before_validation':True};write(d/'candidate_batch.json',batch)
    validation=data(spec,spec['validation_levels'],spec['training_points']+spec['validation_points']);results=[]
    for p in programs:
        for hyp in hypotheses(spec):
            records=[]
            for q in spec['validation_levels']:
                C=fit_constant(p['program'],hyp,q,validation['observations'],spec);vals=[evaluate(p['program'],q,x,validation['observations']) for x in spec['validation_points']]
                missing=C is None or any(v is None for v in vals);ratio=None if missing else max(float((abs(v)/(real(Q(str(C)))*envelope(hyp,q,x))).upper()) for x,v in zip(spec['validation_points'],vals));records.append({'level':q,'constant':C,'maximum_validation_ratio':ratio,'missing':missing})
            finite=not any(r['missing'] for r in records) and all(r['maximum_validation_ratio']<=1 for r in records);worst=max((r['maximum_validation_ratio'] for r in records if not r['missing']),default=None)
            C=fit_constant(p['program'],hyp,max(spec['training_levels']),training['observations'],spec);results.append({'estimate_id':digest({'program_id':p['id'],'hypothesis':hyp}),'program_id':p['id'],'hypothesis':hyp,'records':records,
                'finite_pass':finite,'maximum_validation_ratio':worst,'global_signed_premise_proved':False,'RH_if_uniform':Q(hyp['eta'])==Q(1,2) and p['recovery_certificate']['admitted'],
                'charged_observer_cost':charged_cost(p['program'],hyp,max(spec['training_levels']),C,spec)})
    write(d/'validation.json',{'data':validation,'estimates':results,'all_candidates_retained':True,'final_cases_used':False})
    archive=[]
    for p in programs:
        rs=[r for r in results if r['program_id']==p['id']]
        key=lambda r:(not r['finite_pass'],r['maximum_validation_ratio'] if r['maximum_validation_ratio'] is not None else float('inf'),r['charged_observer_cost'].get('value',float('inf')),r['estimate_id'])
        selected=[min(rs,key=key),min([r for r in rs if Q(r['hypothesis']['eta'])==Q(1,2)],key=key)]
        for row in selected:
            if row['estimate_id'] not in {r['estimate_id'] for r in archive}:archive.append(row)
    primary_ids={p['id'] for p in programs if p['origin']!='ablation_random_slot'};baseline_ids=primary_ids-{r['child_id'] for r in prom};ablation_ids=baseline_ids|{r['program_id'] for r in abl}
    comparison=[]
    for mode,pids in [('primary',primary_ids),('promotion_disabled',ablation_ids)]:
        rr=[r for r in results if r['program_id'] in pids and r['hypothesis']==score_h and r['finite_pass'] and not r['charged_observer_cost']['missing']]
        comparison.append({'mode':mode,'best_finite_validated_charged_cost':min((r['charged_observer_cost']['value'] for r in rr),default=None),'finite_validated_programs':len(rr),
            'same_root_response_data_budget':True,'extra_program_slots':spec['promotion_slots'],'uniform_signed_premise_proved':False})
    write(d/'archive.json',{'selection_closed':True,'final_data_used':False,'estimates':archive,'ablation_comparison':comparison,'negative_control_program_ids':[p['id'] for p in sorted(programs,key=lambda p:p['id'])[:3]],
        'numerical_leads_retained_without_certificates':True,'uniform_RH_sufficient_signed_controls_verified':[]})
    write(d/'seal.json',{'protocol_sha256':digest(spec),'files':{n:sha(d/n) for n in SEALED},'selection_closed':True,'final_cases_exist':False});print('Sealed complete centers and signed parameter-family archive',flush=True)


def final(d):
    spec=read(d/'protocol.json');verify_code(spec);batch=read(d/'candidate_batch.json');arc=read(d/'archive.json');rule=spec['final_cases'];rng=random.Random(int.from_bytes(os.urandom(32),'big'))
    levels=sorted(rng.sample(range(rule['level_range'][0],rule['level_range'][1]+1),rule['level_count']));cal=data(spec,levels,spec['training_points']);constants={}
    for row in arc['estimates']:
        p=next(p for p in batch['programs'] if p['id']==row['program_id'])
        for q in levels:
            eid=digest({'archived_estimate_id':row['estimate_id'],'level':q});constants[eid]={'constant':fit_constant(p['program'],row['hypothesis'],q,cal['observations'],spec),'program_id':p['id'],'hypothesis':row['hypothesis'],'level':q}
    write(d/'final_constants.json',{'data':cal,'estimates':constants,'seal_sha256':sha(d/'seal.json'),'new_levels_generated_after_seal':True,'fresh_x_exists':False})
    excluded=set(spec['parent_final_scales_excluded'])|{n for f in spec['retained_failed_runs_are_development'] for n in f['excluded_final_scales']};integers=sorted(rng.sample([n for n in range(rule['range'][0],rule['range'][1]+1) if n not in excluded],rule['count']));points=list(map(str,rule['boundary']+integers))+[str(Q(n)+Q(rule['offset'])) for n in integers]
    cases={'levels':levels,'integers':integers,'points':points,'seal_sha256':sha(d/'seal.json'),'generated_after_seal':True,'calibration_sha256':sha(d/'final_constants.json'),'x_generated_after_constants':True};write(d/'final_cases.json',cases);actual=data(spec,levels,points);responses={};weak={};observers={};profiles={};evaluations=[]
    for p in batch['programs']:
        pid=p['id'];responses[pid]={};weak[pid]={};observers[pid]={}
        for q in levels:
            responses[pid][str(q)]={x:(g.ball(v) if (v:=evaluate(p['program'],q,x,actual['observations'])) is not None else None) for x in points};weak[pid][str(q)]=g.weak_certificate(p['program'],q);o=g.observer(p['program'],q,**spec['observer_query']);observers[pid][str(q)]=o
            for order,row in o['profiles'].items():profiles[order]=row
    for eid,row in constants.items():
        C=row['constant'];values=responses[row['program_id']][str(row['level'])];ratios=[float((abs(flint.arb(values[x]))/(real(Q(str(C)))*envelope(row['hypothesis'],row['level'],x))).upper()) for x in points] if C is not None and all(v is not None for v in values.values()) else []
        p=next(p for p in batch['programs'] if p['id']==row['program_id']);evaluations.append(dict(row,estimate_id=eid,maximum_fresh_ratio=max(ratios,default=None),finite_pass=bool(ratios) and max(ratios)<=1,
            global_signed_premise_proved=False,RH_if_uniform=Q(row['hypothesis']['eta'])==Q(1,2) and p['recovery_certificate']['admitted'],charged_observer_cost=charged_cost(p['program'],row['hypothesis'],row['level'],C,spec)))
    controls=[]
    for pid in arc['negative_control_program_ids']:
        p=next(p for p in batch['programs'] if p['id']==pid)
        for q in levels:
            lead={};m,pm=g.moments(p['program']);h=pm/Q(q)**m
            for x in points:
                E=sum((real(Q(w))*(flint.arb(actual['observations'][str(Q(b)/q)][x]['sum_ball'])-g.leading_center(Q(b)/q,x)) for b,w in p['program']['atoms']),flint.arb(0))/real(h);lead[x]=g.ball(E)
            controls.append({'program_id':pid,'level':q,'responses':lead,'analytic_obstruction':g.leading_only_obstruction(p['program'],q)})
    zero=False
    try:g.canonical([('1/2',1),('1/2',-1)])
    except ValueError:zero=True
    reference=batch['programs'][0]['program'];generic=dict(reference,arithmetic_model='generic_sequence');incomplete=dict(reference,center='leading_only');type_controls={'zero_family_not_recovering':zero,
        'generic_sequence_not_actual_zeta':not g.recovery(generic)['admitted'],'leading_only_not_complete_center':not g.recovery(incomplete)['admitted'],
        'finite_levels_not_cofinal_proof':all(not r['global_signed_premise_proved'] for r in evaluations),'finite_success_not_global_RH':True}
    write(d/'final_evaluation.json',{'protocol_sha256':digest(spec),'cases_sha256':digest(cases),'data':actual,'responses':responses,'weak_certificates':weak,'observers':observers,'profile_observations':profiles,
        'estimate_evaluations':evaluations,'leading_only_controls':controls,'type_controls':type_controls,'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False})


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('mode',nargs='?',default='run',choices=['run','worker']);p.add_argument('--run-dir',type=Path,required=True);p.add_argument('--source',type=Path);args=p.parse_args();d=args.run_dir.resolve()
    if args.mode=='worker':worker(d);return
    if args.source is None:raise ValueError('Verified retained-arithmetic source required')
    d.mkdir(parents=True,exist_ok=False);spec=protocol(args.source);write(d/'protocol.json',spec);(d/'frozen_source').mkdir()
    for n in CODE:(d/'frozen_source'/n).write_bytes((BASE/n).read_bytes())
    try:
        subprocess.run([sys.executable,str(BASE/'branch_center_search.py'),'worker','--run-dir',str(d)],cwd=BASE,check=True);final(d)
        subprocess.run([sys.executable,str(BASE/'check_branch_centers.py'),'--run-dir',str(d)],cwd=BASE,check=True)
        from branch_center_report import summary,text_report
        s=summary(d);write(d/'summary.json',s);(d/'report.txt').write_text(text_report(s));write(BASE/'branch-center-results/latest.json',{'run_directory':str(d)})
    except Exception as e:write(d/'failure.json',{'error_type':type(e).__name__,'error':str(e),'original_data_and_sources_retained':True});raise


if __name__=='__main__':main()
