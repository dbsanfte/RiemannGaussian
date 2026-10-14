#!/usr/bin/env python3
"""Frozen behavioral limit inference and certified arithmetic-envelope search."""
from fractions import Fraction as Q
from itertools import product
from math import factorial,floor,comb
from pathlib import Path
import argparse,os,random,socket,subprocess,sys
import flint
from stable_scale_search import BASE,read,write,sha,digest,verify_code
from mellin_kernel_grammar import real
import branch_center_grammar as bc
import parameter_cancellation_grammar as g

CODE=['parameter_cancellation_grammar.py','parameter_cancellation_search.py','check_parameter_cancellation.py',
      'parameter_cancellation_report.py','parameter_cancellation_proof.txt','test_parameter_cancellation_contracts.py','plot_parameter_cancellation.py']
EXTRA=['rational_fractional_evaluator.py','check_rational_fractional_contracts.py','rational_fractional_contract_report.py','branch_center_positive_gap_audit.py']
SEALED=['protocol.json','candidate_batch.json','validation.json','archive.json']


def protocol(source):
    from branch_center_report import summary
    from rational_fractional_contract_report import load_latest as contracts
    source=Path(source).resolve();summary(source);contract=contracts();assert Path(contract['run_directory'])==source;old=read(source/'protocol.json');parents=read(source/'candidate_batch.json')['programs'];failed=[]
    for p in sorted((BASE/'parameter-cancellation-results').glob('*/failure.json')):
        d=p.parent;failed.append({'run_directory':str(d),'failure_sha256':sha(p),
            'files_sha256':{f.name:sha(f) for f in d.glob('*.json') if f.name!='failure.json'},
            'excluded_final_scales':read(d/'final_cases.json')['integers'] if (d/'final_cases.json').exists() else []})
    bases=sorted({Q(b) for p in parents for b,w in p['program']['atoms']});pool=sorted({b/2**j for b in bases for j in range(3)})
    return {'schema':1,'grammar_version':g.VERSION,'seed':2026100826,'precision':640,'source_run':str(source),
        'source_sha256':{n:sha(source/n) for n in ['protocol.json','candidate_batch.json','verification.json','summary.json','positive_gap_observer_audit.json','rational_fractional_contract_data.json','rational_fractional_contract_verification.json']},
        'code_sha256':dict(old['code_sha256'],**{n:sha(BASE/n) for n in CODE+EXTRA}),'this_stage_source_files':CODE,
        'named_calibration_dependencies':old['named_calibration_dependencies'],
        'starting_programs':[p['program'] for p in parents],'parent_names_and_scores_passed_to_learners':False,
        'evaluation_root_pool':list(map(str,pool)),'parameter_moment_mutation_slots':4,'parameter_moment_mutation_depth':2,'random_family_slots':4,
        'training_levels':[8,16,32,64],'training_cutoff':128,'training_points':[4,8,16,32,64,128],
        'validation_points':[256,384,640,1024],'moment_response_indices':[2,3,6,12,30,60],
        'moment_feature_exponents':['0','1/6','1/3','1/2','1','3/2','2','5/2','3','4','5'],
        'moment_fit_tolerance':'1/10','learning_quantization_bits':80,'coefficient_rounding_denominator':64,'limit_fit_tolerance':'1/100000',
        'limit_feature_dictionary':'constant; nested log integer powers 1..4; log and shifted nested log powers 1/6,1/3,1/2,1,2,3,4; third shifted log; sine/cosine; Gaussian nested; mixed log',
        'limit_promotion_slots':4,'limit_promotion_rule':'admitted distinct formulas by reuse, aggregate residual, stable id; no nominated jet order',
        'limit_ablation_rule':'equal slots random feature and rational coefficient, without inferred fit; same admission backend and data',
        'radius_training_indices':[1,2,3],'radius_training_coordinates':[4,8,16,32,64],
        'radius_validation_coordinates':[3,6,12,24,48,96],'radius_grid_denominator':64,'radius_grid_indices':list(range(1,17)),'radius_cap':'1/4',
        'radius_baseline_coefficients':['1/4','1'],'radius_baseline_shifts':['1','4','16'],
        'radius_coordinate_powers':['1/6','1/3','1/2','1','2'],'radius_baseline_index_powers':['0','1'],
        'radius_inference_index_powers':['-2','-1','-1/2','0','1/2','1','2'],
        'radius_promotion_slots':4,'radius_coefficient_rounding_denominator':4096,
        'radius_ablation_coefficients':['1/4','1/2','1','2','4'],'radius_selection':'mean log certified envelope, then description length and stable id',
        'critical_growth_grammar':{'epsilon':'1/16','nu':['1/6','1','2'],'log_degree':['0','1/6','1']},
        'critical_archive_selection':'all finite leads retained; minimum finite validation ratio per index, charged whole observer cost tie-break',
        'final_cases':{'level_range':[65,96],'level_count':2,'range':[4097,8192],'count':2,'offset':'2/5','boundary':[1,2,3],
            'envelope_coordinate_range':[97,256],'envelope_coordinate_count':5,'envelope_coordinate_denominator':7},
        'parent_final_scales_excluded':read(source/'final_cases.json')['integers'],
        'retained_failed_runs_are_development':failed,'all_rational_exponents_supported':True,'semantic_denominator_cap':False,
        'ordinary_zeta_retained':True,'new_prime_distribution_estimate_imported':False,'generator_model_literature_network_or_prime_oracle_access':False,
        'envelope_coordinates_are_proved_bound_optimization_not_huge_prime_samples':True,
        'supplied_analytic_methods':['exponential maximum','Gamma product','parameter Cauchy bounds','Taylor moment remainder','full positive-real cut center','whole integer parameter-tail pole contradiction'],
        'RH_bound_strategy':{'proved_envelope_power':'1','this_stage_claims_square_root_cancellation':False,
            'missing_mechanism':'signed off-diagonal arithmetic cancellation or a uniformly closed scale inequality',
            'existing_recovering_energy_target':'A_2(2X)-4*A_2(X)<=B*X^2 for every dyadic X, with finite B',
            'existing_diagonal_bound_proved':True,'signed_off_diagonal_defect_bound_proved':False,
            'priority_metric':'saved ordinary power after normalization, interpolation and all-height recovery costs; log savings recorded separately'},
        'not_autonomous_proof_invention':True,'historical_priority_is_acceptance_gate':False,'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False}


def restrict(d,spec):
    allowed={str((BASE/n).resolve()) for n in spec['code_sha256']}|{str((d/n).resolve()) for n in SEALED+['seal.json']}
    def audit(event,args):
        if event=='open' and not isinstance(args[0],int) and str(Path(args[0]).resolve()) not in allowed:raise PermissionError('Discovery access denied')
        if event.startswith('socket.') or event in ['subprocess.Popen','os.system','os.posix_spawn','os.posix_spawnp']:raise PermissionError('External access denied')
    sys.addaudithook(audit);denied={}
    probes=[('private_final',lambda:open(d/'final_cases.json')),('parent_outcomes',lambda:open(Path(spec['source_run'])/'final_evaluation.json')),
        ('literature',lambda:open(spec['named_calibration_dependencies'][0]['path'])),('root_registry',lambda:open(BASE/'root-results/candidate_registry.json')),
        ('network',lambda:socket.socket()),('subprocess',lambda:subprocess.run([sys.executable,'-c','pass']))]
    for label,fn in probes:
        try:fn()
        except PermissionError:denied[label]=True
        else:raise AssertionError('Isolation failed')
    return denied


def quant(x,bits):return Q(round(Q(x.mid().str(85,radius=False))*2**bits),2**bits)


def family_raw(p,q,tables,n):
    return sum((real(Q(w))*flint.arb(tables[str(Q(b)/q)]['values'][n]) for b,w in p['atoms']),flint.arb(0))


def infer_moment(response,levels,spec):
    """Only anonymous numeric responses, parameter coordinates and a dictionary."""
    flint.ctx.prec=spec['precision'];Y=[[quant(v,spec['learning_quantization_bits']) for v in row] for row in response];fits=[]
    norm=sum((v*v for row in Y for v in row),Q(0))
    for exponent in spec['moment_feature_exponents']:
        X=[quant(g.rational_power(real(q),-Q(exponent)),spec['learning_quantization_bits']) for q in levels];xx=sum((v*v for v in X),Q(0));coeff=[sum((X[i]*Y[i][j] for i in range(len(X))),Q(0))/xx for j in range(len(Y[0]))]
        residual=sum(((Y[i][j]-X[i]*coeff[j])**2 for i in range(len(X)) for j in range(len(coeff))),Q(0))/norm if norm else Q(0)
        fits.append({'exponent':exponent,'relative_squared_residual':str(residual)})
    best=min(fits,key=lambda r:(Q(r['relative_squared_residual']),Q(r['exponent'])))
    return {'exponent':best['exponent'],'relative_squared_residual':best['relative_squared_residual'],'fits':fits,
        'operator_names_exact_moments_and_expected_exponents_supplied':False,'universal_identity_claimed':False}


def infer_feature(response,features,spec):
    """Single-feature least squares; no expected feature or coefficient argument."""
    Y=[quant(v,spec['learning_quantization_bits']) for v in response];norm=sum((v*v for v in Y),Q(0));fits=[]
    for name,values in features.items():
        X=[quant(v,spec['learning_quantization_bits']) for v in values];xx=sum((v*v for v in X),Q(0))
        if not xx:continue
        c=sum((x*y for x,y in zip(X,Y)),Q(0))/xx;rounded=c.limit_denominator(spec['coefficient_rounding_denominator']);res=sum(((y-rounded*x)**2 for x,y in zip(X,Y)),Q(0))/(norm or 1)
        fits.append({'feature':name,'coefficient':str(rounded),'relative_squared_residual':str(res),'description_length':len(name)+len(str(rounded))})
    best=min(fits,key=lambda r:(Q(r['relative_squared_residual']),r['description_length'],r['feature']))
    return dict(best,all_fits=fits,expected_feature_or_factorial_supplied=False,universal_identity_claimed=False)


def limit_inference(p,tables,features,spec):
    flint.ctx.prec=spec['precision'];levels=spec['training_levels'];N=spec['training_cutoff'];response=[[family_raw(p,q,tables,n) for n in spec['moment_response_indices']] for q in levels];mf=infer_moment(response,levels,spec);m,pm=g.moments(p)
    moment_admitted=Q(mf['exponent'])==m and Q(mf['relative_squared_residual'])<=Q(spec['moment_fit_tolerance'])
    if not moment_admitted:return {'program':p,'moment_inference':mf,'moment_admitted':False,'limit_certificate':{'admitted':False},'status':'unsupported_parameter_scaling_lead'}
    nodes=[Q(1,q) for q in levels];weights=[Q(1) for _ in nodes]
    for i,t in enumerate(nodes):
        for j,u in enumerate(nodes):
            if i!=j:weights[i]*=-u/(t-u)
    limit=[flint.arb(0)]
    for n in range(1,N+1):limit.append(sum((real(w)*family_raw(p,q,tables,n)/real(pm/Q(q)**m) for w,q in zip(weights,levels)),flint.arb(0)))
    raw=[sum((limit[j] for j in range(1,n+1) if n%j==0),flint.arb(0)) for n in range(2,N+1)];fit=infer_feature(raw,features,spec);certificate=g.feature_limit_admission(fit['feature'],fit['coefficient'],m)
    certificate['admitted']=certificate['admitted'] and Q(fit['relative_squared_residual'])<=Q(spec['limit_fit_tolerance'])
    return dict(fit,program=p,moment_inference=mf,moment_admitted=True,limit_certificate=certificate,
        extrapolation={'levels':levels,'weights':list(map(str,weights)),'degree':len(levels)-1,'finite_extrapolation_is_not_proof':True},
        anonymous_inferred_raw_response=list(map(g.ball,raw)),status='exact_compact_limit_admitted' if certificate['admitted'] else 'unsupported_limit_feature_lead')


def radius_envelope(r,V,m,cap):
    d=g.radius_value(r,real(Q(V)),m,Q(cap));return 9*d**(-m)*(d*real(Q(V))).exp()


def radius_fit(grid,spec):
    bits=spec['learning_quantization_bits'];Y=[Q(1)/Q(row['radius']) for row in grid if not row['boundary_censored']];rows=[row for row in grid if not row['boundary_censored']];norm=sum((y*y for y in Y),Q(0));out=[]
    for t,r in product(spec['radius_inference_index_powers'],spec['radius_coordinate_powers']):
        X=[quant(g.rational_power(real(max(1,row['index'])),Q(t))*g.rational_power(real(Q(row['coordinate'])),Q(r)),bits) for row in rows];xx=sum((x*x for x in X),Q(0))
        if not xx:continue
        c=(sum((x*y for x,y in zip(X,Y)),Q(0))/xx).limit_denominator(spec['radius_coefficient_rounding_denominator']);res=sum(((y-c*x)**2 for x,y in zip(X,Y)),Q(0))/(norm or 1);p={'kind':'inverse_monomial','coefficient':str(c),'index_power':t,'coordinate_power':r}
        out.append({'radius':p,'relative_squared_residual':str(res),'certificate':g.radius_certificate(p),'target_formula_or_coefficient_supplied':False})
    return sorted(out,key=lambda row:(not row['certificate']['admitted'],Q(row['relative_squared_residual']),len(str(row['radius'])),digest(row['radius'])))


def jet_data(indices,points,spec):
    N=max(Q(x).numerator//Q(x).denominator for x in points);tables={str(m):g.jets(m,N,spec['precision']) for m in indices};observations=[]
    for m in indices:
        prefix=[flint.arb(0)]
        for v in tables[str(m)]['values'][1:]:prefix.append(prefix[-1]+flint.arb(v))
        for x in points:
            center=g.jet_center(m,x,spec['precision']);n=Q(x).numerator//Q(x).denominator;observations.append({'index':m,'x':str(x),'center':center,'sum_ball':g.ball(prefix[n]),'signed_error_ball':g.ball(prefix[n]-flint.arb(center['value_ball']))})
    return {'tables':tables,'observations':observations,'complete_arithmetic':True}


def critical_envelope(h,m,x):
    theta=real(Q(1,2))+real(Q(h['epsilon']))/g.rational_power(real(m+1),Q(h['nu']));return (theta*real(Q(x)).log()).exp()*g.rational_power((flint.arb.const_e()+real(Q(x))).log(),Q(h['log_degree']))


def fit_constant(rows,h,m):
    flint.ctx.prec=640;value=max((abs(flint.arb(row['signed_error_ball']))/critical_envelope(h,m,row['x']) for row in rows if row['index']==m),key=lambda v:float(v.upper()))*Q(5,4)
    return str(Q(g.integer_guard(value*2**64),2**64))


def jet_cost(m,h,C,profile):
    if profile.get('missing'):return {'missing':True,'reason':profile['reason']}
    flint.ctx.prec=640;F=g.decode(profile['value_ball']);lower=Q(max(0,floor(Q(abs(F).lower().str(150,radius=False))*2**160)-1),2**160)
    theta=real(Q(1,2))+real(Q(h['epsilon']))/g.rational_power(real(m+1),Q(h['nu']));gap=real(Q(5,8))-theta
    if not gap>0 or not lower:return {'missing':True,'reason':'nonpositive_Mellin_gap_or_uncertain_whole_numerator'}
    degree=Q(h['log_degree']);D=-(-degree.numerator//degree.denominator);c=(flint.arb.const_e()+1).log();I=sum((real(comb(D,j)*factorial(j))*c**(D-j)/gap**(j+1) for j in range(D+1)),flint.arb(0));s=flint.acb(real(Q(5,8)),16);K=12*2**m
    cost=abs(s)*(real(K)/(abs(s)*16)+real(Q(C))*I+real(K)/s.real)/real(lower)
    return {'missing':False,'value':float(cost.upper()),'value_ball':g.ball(cost),'profile_modulus_lower_ball':str(lower),'gap_ball':g.ball(gap),'gap_integral_ball':g.ball(I),
        'full_center_mellin_upper_ball':g.ball(real(K)/(abs(s)*16)),'integer_to_real_guard':str(K),'conditional_on_unproved_global_estimate':True,
        'all_parameter_factorials_charged':True,'standalone_jet_RH_recovery_proved':m==0,'finite_cost_not_RH_proof':True}


def worker(d):
    spec=read(d/'protocol.json');verify_code(spec);denied=restrict(d,spec);rng=random.Random(spec['seed']);programs=[];ids={}
    def add(p,origin,parent=None):
        pid=digest(p)
        if pid not in ids:row={'id':pid,'program':p,'origin':origin,'parent_id':parent,'family_certificate':g.family_parameters(p),'cofinal_recovery_certificate':g.recovery(p)};programs.append(row);ids[pid]=row
        return pid
    for p in spec['starting_programs']:add(p,'verified_optional_starting_module')
    mutation_attempts=[]
    for parent in rng.sample(list(programs),min(spec['parameter_moment_mutation_slots'],len(programs))):
        p=parent['program']
        for depth in range(spec['parameter_moment_mutation_depth']):
            m,pm=g.moments(p);atoms=[]
            for b,w in p['atoms']:atoms.extend([(Q(b),Q(w)),(Q(b)/2,-2**m*Q(w))])
            p=g.canonical(atoms);pid=add(p,'generic_parameter_moment_mutation',parent['id']);mutation_attempts.append({'parent_id':parent['id'],'child_id':pid,'depth':depth+1,'annihilated_moment':m})
    for slot in range(spec['random_family_slots']):
        while True:
            atoms=[(b,Q(rng.randint(-3,3),rng.choice([1,2,3]))) for b in rng.sample(spec['evaluation_root_pool'],rng.randint(1,5))]
            if any(w for b,w in atoms):break
        add(g.canonical(atoms),'random_family')
    orders=sorted({Q(b)/q for p in programs for b,w in p['program']['atoms'] for q in spec['training_levels']});tables={str(a):g.coefficients(a,spec['training_cutoff'],spec['precision']) for a in orders}
    features={};flint.ctx.prec=spec['precision']
    for n in range(2,spec['training_cutoff']+1):
        for name,value in g.coefficient_features(n).items():features.setdefault(name,[]).append(value)
    inferences=[]
    for row in programs:
        inference=limit_inference(row['program'],tables,features,spec);inference['program_id']=row['id'];inferences.append(inference)
    groups={}
    for row in inferences:
        if row['limit_certificate']['admitted']:groups.setdefault((row['feature'],row['coefficient']),[]).append(row)
    ranked=sorted(groups.items(),key=lambda item:(-len(item[1]),sum(Q(r['relative_squared_residual']) for r in item[1]),digest(list(item[0]))));promotions=[];ablations=[]
    for (feature,coefficient),rows in ranked[:spec['limit_promotion_slots']]:
        m=rows[0]['limit_certificate']['pointwise_limit_jet_index'];promotions.append({'id':digest({'feature':feature,'coefficient':coefficient}),'feature':feature,'coefficient':coefficient,'index':m,
            'reuse':len(rows),'parent_program_ids':[r['program_id'] for r in rows],'universal_exact_compact_limit':True,'same_as_fixed_q_parent':False,'critical_global_bound_transferred':False})
        f=rng.choice(sorted(features));c=Q(rng.randint(1,12),rng.randint(1,12));cert=g.feature_limit_admission(f,c,m);ablations.append({'feature':f,'coefficient':str(c),'attempted_index':m,'limit_certificate':cert})
    radii=[];rids={}
    def add_radius(p,origin,fit=None):
        rid=digest(p)
        if rid not in rids:row={'id':rid,'radius':p,'origin':origin,'certificate':g.radius_certificate(p),'inference':fit};radii.append(row);rids[rid]=row
        return rid
    for c in ['1/16','1/8','1/4']:add_radius({'kind':'constant','value':c},'baseline')
    for c,shift,r,t in product(spec['radius_baseline_coefficients'],spec['radius_baseline_shifts'],spec['radius_coordinate_powers'],spec['radius_baseline_index_powers']):add_radius({'kind':'shifted_power','coefficient':c,'shift':shift,'coordinate_power':r,'index_power':t},'baseline')
    grid=[];flint.ctx.prec=spec['precision']
    for m,V in product(spec['radius_training_indices'],spec['radius_training_coordinates']):
        values=[(j,radius_envelope({'kind':'constant','value':str(Q(j,spec['radius_grid_denominator']))},V,m,spec['radius_cap'])) for j in spec['radius_grid_indices']];j,val=min(values,key=lambda t:float(t[1].upper()));grid.append({'index':m,'coordinate':str(V),'radius':str(Q(j,spec['radius_grid_denominator'])),
            'bound_ball':g.ball(val),'boundary_censored':j in [min(spec['radius_grid_indices']),max(spec['radius_grid_indices'])]})
    fits=radius_fit(grid,spec);rprom=[];rabl=[]
    for fit in [r for r in fits if r['certificate']['admitted']][:spec['radius_promotion_slots']]:rprom.append(add_radius(fit['radius'],'learned_radius',fit))
    while len(rabl)<len(rprom):
        p={'kind':'inverse_monomial','coefficient':rng.choice(spec['radius_ablation_coefficients']),'index_power':rng.choice(spec['radius_inference_index_powers']),'coordinate_power':rng.choice(spec['radius_coordinate_powers'])}
        if digest(p) not in rids:rabl.append(add_radius(p,'random_radius_slot'))
    indices=sorted({0}|{r['index'] for r in promotions});training=jet_data(indices,spec['training_points'],spec);profiles={str(m):g.jet_observer(m) for m in indices}
    batch={'protocol_sha256':digest(spec),'programs':programs,'parameter_mutation_attempts':mutation_attempts,'root_training_tables':tables,'limit_inferences':inferences,'limit_promotions':promotions,'limit_ablation_slots':ablations,
        'radius_programs':radii,'radius_grid_observations':grid,'radius_fits':fits,'radius_promotions':rprom,'radius_ablation_slots':rabl,'jet_training':training,'jet_profiles':profiles,
        'access_denials':denied,'candidate_batch_frozen_before_validation':True,'final_cases_used':False};write(d/'candidate_batch.json',batch)
    validation=jet_data(indices,spec['validation_points'],spec);radius_rows=[]
    for row in radii:
        observations=[{'index':m,'coordinate':str(V),'bound_ball':g.ball(radius_envelope(row['radius'],V,m,spec['radius_cap']))} for m,V in product(spec['radius_training_indices'],spec['radius_validation_coordinates'])];score=sum(float(flint.arb(o['bound_ball']).log().mid()) for o in observations)/len(observations);radius_rows.append({'radius_id':row['id'],'mean_log_bound':score,'observations':observations,'global_power_one_certificate':True})
    hgrammar=spec['critical_growth_grammar'];estimates=[]
    for m,nu,dlog in product(indices,hgrammar['nu'],hgrammar['log_degree']):
        h={'epsilon':hgrammar['epsilon'],'nu':nu,'log_degree':dlog};C=fit_constant(training['observations'],h,m);ratios=[float((abs(flint.arb(o['signed_error_ball']))/(real(Q(C))*critical_envelope(h,m,o['x']))).upper()) for o in validation['observations'] if o['index']==m];cost=jet_cost(m,h,C,profiles[str(m)])
        estimates.append({'estimate_id':digest({'index':m,'hypothesis':h}),'index':m,'hypothesis':h,'constant':C,'maximum_validation_ratio':max(ratios),'finite_pass':max(ratios)<=1,'charged_whole_observer_cost':cost,
            'global_critical_signed_premise_proved':False,'individual_jet_RH_recovery_proved':m==0,'all_integer_tail_RH_if_uniform':True})
    write(d/'validation.json',{'jet_data':validation,'radius_results':radius_rows,'critical_estimates':estimates,'all_candidates_retained':True,'final_cases_used':False})
    baseline={r['id'] for r in radii if r['origin']=='baseline'};comparison=[];best={}
    for mode,extra in [('primary',rprom),('promotion_disabled',rabl)]:
        rows=[r for r in radius_rows if r['radius_id'] in baseline|set(extra)];winner=min(rows,key=lambda r:(r['mean_log_bound'],len(str(rids[r['radius_id']]['radius'])),r['radius_id']));best[mode]=winner['radius_id'];comparison.append({'mode':mode,'best_radius_id':winner['radius_id'],'mean_log_certified_bound':winner['mean_log_bound'],'extra_radius_slots':len(extra),'same_data_budget':True,'global_ordinary_power':'1','RH_strength':False})
    archived=[min([r for r in estimates if r['index']==m],key=lambda r:(not r['finite_pass'],r['maximum_validation_ratio'],r['charged_whole_observer_cost'].get('value',float('inf')),r['estimate_id'])) for m in indices]
    arc={'selection_closed':True,'final_data_used':False,'best_radius_by_mode':best,'radius_ablation_comparison':comparison,
        'limit_ablation_comparison':{'primary_admitted_formula_count':len(promotions),'promotion_disabled_admitted_formula_count':sum(r['limit_certificate']['admitted'] for r in ablations),'extra_slots_each':len(promotions),'same_data_budget':True},
        'compiled_jet_indices':indices,'critical_estimates':archived,'all_numerical_leads_retained_in_validation':True,'uniform_RH_sufficient_signed_controls_verified':[]};write(d/'archive.json',arc)
    write(d/'seal.json',{'protocol_sha256':digest(spec),'files':{n:sha(d/n) for n in SEALED},'selection_closed':True,'final_cases_exist':False});print('Sealed limit inference, radius promotions, equal-slot ablations and critical leads',flush=True)


def complex_geometry(base,rates,re,im):
    alpha=flint.acb(real(Q(re)),real(Q(im)));value=flint.acb(0);r=len(rates)
    for mask in range(1<<r):
        x=Q(base)+sum((Q(h) for j,h in enumerate(rates) if mask>>j&1),Q(0))
        if x:value+=(-1)**(r-mask.bit_count())*(alpha*real(x).log()).exp()
    return {'base':str(Q(base)),'rates':list(map(str,rates)),'parameter_real':str(Q(re)),'parameter_imag':str(Q(im)),'difference_ball':g.cball(value),'empty_zero_weight_masked':True}


def final(d):
    spec=read(d/'protocol.json');verify_code(spec);batch=read(d/'candidate_batch.json');arc=read(d/'archive.json');rule=spec['final_cases'];rng=random.Random(int.from_bytes(os.urandom(32),'big'));excluded=set(spec['parent_final_scales_excluded'])|{n for f in spec['retained_failed_runs_are_development'] for n in f['excluded_final_scales']}
    levels=sorted(rng.sample(range(rule['level_range'][0],rule['level_range'][1]+1),rule['level_count']));integers=sorted(rng.sample([n for n in range(rule['range'][0],rule['range'][1]+1) if n not in excluded],rule['count']));points=list(map(str,rule['boundary']+integers))+[str(Q(n)+Q(rule['offset'])) for n in integers]
    coordinates=[str(Q(n,rule['envelope_coordinate_denominator'])) for n in rng.sample(range(rule['envelope_coordinate_range'][0]*rule['envelope_coordinate_denominator'],rule['envelope_coordinate_range'][1]*rule['envelope_coordinate_denominator']+1),rule['envelope_coordinate_count'])];seed=rng.getrandbits(128)
    cases={'levels':levels,'integers':integers,'points':points,'envelope_coordinates':coordinates,'generic_seed':seed,'generated_after_seal':True,'seal_sha256':sha(d/'seal.json')};write(d/'final_cases.json',cases);N=max(integers);orders=sorted({Q(b)/q for p in batch['programs'] for b,w in p['program']['atoms'] for q in levels});tables={};prefix={};centers={}
    for order in orders:
        table=g.coefficients(order,N,spec['precision']);key=str(order);tables[key]=table;v=[flint.arb(0)]
        for z in table['values'][1:]:v.append(v[-1]+flint.arb(z))
        prefix[key]=v
        for x in points:centers[(key,x)]=g.complete_center(order,x,spec['precision'])
        print('Fresh complete arithmetic',key,'through',N,flush=True)
    radii={r['id']:r['radius'] for r in batch['radius_programs']};best=radii[arc['best_radius_by_mode']['primary']];family_rows=[]
    for row in batch['programs']:
        p=row['program']
        for q,x in product(levels,points):
            h=g.normalization(p,q);n=Q(x).numerator//Q(x).denominator;T=sum((real(Q(w))*prefix[str(Q(b)/q)][n] for b,w in p['atoms']),flint.arb(0))/real(h);A=sum((real(Q(w))*flint.arb(centers[(str(Q(b)/q),x)]['value_ball']) for b,w in p['atoms']),flint.arb(0))/real(h)
            family_rows.append({'program_id':row['id'],'program':p,'level':q,'x':x,'radius':best,'sum_ball':g.ball(T),'center_ball':g.ball(A),'signed_error_ball':g.ball(T-A),'certificate':g.certified_family_bound(p,best,q,x),
                'old_triangle_certificate':bc.weak_certificate(p,q)})
    jets=jet_data(arc['compiled_jet_indices'],points,spec)
    for row in jets['observations']:row['certificate']=g.certified_jet_bound(row['index'],best,row['x']);row['radius']=best
    radius_rows=[]
    for row in batch['radius_programs']:
        for m,V in product(spec['radius_training_indices'],coordinates):radius_rows.append({'radius_id':row['id'],'radius':row['radius'],'index':m,'coordinate':V,'bound_ball':g.ball(radius_envelope(row['radius'],V,m,spec['radius_cap'])),'certificate':row['certificate']})
    evaluations=[]
    for row in arc['critical_estimates']:
        ratios=[float((abs(flint.arb(o['signed_error_ball']))/(real(Q(row['constant']))*critical_envelope(row['hypothesis'],row['index'],o['x']))).upper()) for o in jets['observations'] if o['index']==row['index']];evaluations.append(dict(row,maximum_fresh_ratio=max(ratios),fresh_finite_pass=max(ratios)<=1,global_critical_signed_premise_proved=False))
    grng=random.Random(seed);generic=[]
    for trial in range(2):
        f=['0','1']+[str(Q(grng.randint(-7,7),grng.randint(1,5))) for _ in range(47)]
        if trial==0:f[2]='1000'
        for m in arc['compiled_jet_indices']:generic.append({'input':f,'table':g.jets(m,len(f)-1,spec['precision'],f),'actual_prime_bound_transfer_admitted':False})
    geometries=[complex_geometry(0,['2','3'],'-1/8','1/8'),complex_geometry(4,['2','3'],'1/4',0),complex_geometry(0,['1','3','7'],'1/3','-1/8'),
        complex_geometry(2,['1','2','5'],'-1/4',0),complex_geometry(0,['2','4'],'0','1/4'),complex_geometry(5,['1','3'],'0',0)]
    malformed=False
    try:g.certified_jet_bound(1,best,2,'generic_sequence')
    except ValueError:malformed=True
    zero=False
    try:g.canonical([('1/2',1),('1/2',-1)])
    except ValueError:zero=True
    controls={'generic_actual_prime_certificate_transfer_rejected':malformed,'zero_erasing_family_rejected':zero,
        'cofinal_subset_not_integer_tail':not g.jet_bank_recovery(1,False)['admitted'],'generic_bank_not_ordinary_zeta':not g.jet_bank_recovery(1,True,'generic_sequence')['admitted'],
        'finite_bank_not_global_critical_premise':not g.jet_bank_recovery(1)['global_critical_signed_premise_proved'],
        'individual_positive_jet_does_not_inherit_parent_RH_gate':all(not r['critical_global_bound_transferred'] for r in batch['limit_promotions']),
        'finite_critical_fit_not_RH_proof':all(not r['global_critical_signed_premise_proved'] for r in evaluations)}
    write(d/'final_evaluation.json',{'protocol_sha256':digest(spec),'cases_sha256':digest(cases),'root_tables':tables,'family_observations':family_rows,'jet_tables':jets['tables'],'jet_observations':jets['observations'],
        'jet_profiles':batch['jet_profiles'],'probability_geometries':geometries,'radius_evaluations':radius_rows,'critical_estimate_evaluations':evaluations,'generic_input_audit':generic,'negative_controls':controls,
        'all_integer_tail_recovery_certificate':g.jet_bank_recovery(1),'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False})


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('mode',nargs='?',default='run',choices=['run','worker']);p.add_argument('--run-dir',type=Path,required=True);p.add_argument('--source',type=Path);args=p.parse_args();d=args.run_dir.resolve()
    if args.mode=='worker':worker(d);return
    if args.source is None:raise ValueError('Verified complete fractional-center source required')
    d.mkdir(parents=True,exist_ok=False);spec=protocol(args.source);write(d/'protocol.json',spec);(d/'frozen_source').mkdir()
    for n in CODE:(d/'frozen_source'/n).write_bytes((BASE/n).read_bytes())
    try:
        subprocess.run([sys.executable,str(BASE/'parameter_cancellation_search.py'),'worker','--run-dir',str(d)],cwd=BASE,check=True);final(d)
        subprocess.run([sys.executable,str(BASE/'check_parameter_cancellation.py'),'--run-dir',str(d)],cwd=BASE,check=True)
        from parameter_cancellation_report import summary,text_report
        s=summary(d);write(d/'summary.json',s);(d/'report.txt').write_text(text_report(s));write(BASE/'parameter-cancellation-results/latest.json',{'run_directory':str(d)})
    except Exception as e:write(d/'failure.json',{'error_type':type(e).__name__,'error':str(e),'original_data_and_sources_retained':True});raise


if __name__=='__main__':main()
