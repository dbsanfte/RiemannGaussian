#!/usr/bin/env python3
"""Frozen actual-root search with anonymous moment and response learning."""
import argparse
from collections import defaultdict
from fractions import Fraction as Q
from itertools import product,combinations
from math import ceil
from pathlib import Path
import os,random,socket,subprocess,sys
import flint
from stable_scale_search import BASE,read,write,sha,digest,verify_code
from mellin_kernel_grammar import real,power,serialize
import root_lattice_grammar as g

CODE=['root_lattice_grammar.py','root_lattice_search.py','check_root_lattices.py','root_lattice_report.py',
      'root_lattice_proof.txt','test_root_lattice_contracts.py','plot_root_lattices.py']
SEALED=['protocol.json','source_forms.json','discovery_data.json','candidate_batch.json','validation_data.json','archive.json']
def pid(row):return digest({'parameters':row,'semantics':g.VERSION})


def source_forms(source):
    b=read(Path(source)/'candidate_batch.json')
    return {'forms':[{'parent_id':p['id'],'terms':p['shape']['terms']} for p in b['programs']],
        'prior_outcomes_supplied':False,'production':'reuse signed moment coefficient patterns in the new pure-power normalized basis'}


def protocol(source):
    from lattice_synthesis_report import summary
    source=Path(source).resolve();summary(source);old=read(source/'protocol.json');rng=random.Random(2026100823)
    pool=sorted({Q(p,q) for p in range(1,7) for q in range(2,7) if Q(1,6)<=Q(p,q)<1 and Q(p,q).numerator!=1})
    rs=sorted([Q(1,6),Q(1,3),Q(1,2),rng.choice(pool),Q(1)]);rows=[list(map(str,(1+1/r,ell,r))) for ell in [Q(1,6),Q(1,3),Q(1,2)] for r in rs];failed=[]
    for f in sorted((BASE/'root-lattice-results').glob('*/failure.json')):
        d=f.parent;failed.append({'run_directory':str(d),'failure_sha256':sha(f),'original_code_sha256':read(d/'protocol.json')['code_sha256'],
            'retained_files_sha256':{p.name:sha(p) for p in d.glob('*.json') if p.name!='failure.json'},
            'excluded_final_scales':read(d/'final_cases.json')['integers'] if (d/'final_cases.json').exists() else [],
            'excluded_final_q':read(d/'parameter_cases.json')['fresh_q'] if (d/'parameter_cases.json').exists() else []})
    return {'schema':1,'grammar_version':g.VERSION,'seed':2026100823,'precision':384,'source_run':str(source),
        'source_sha256':{n:sha(source/n) for n in ['protocol.json','verification.json','summary.json','candidate_batch.json']},
        'code_sha256':dict(old['code_sha256'],**{n:sha(BASE/n) for n in CODE}),'this_stage_source_files':CODE,
        'named_calibration_dependencies':old['named_calibration_dependencies'],'parameters':rows,'maximum_moment':4,
        'required_arithmetic_root_dilations':['1/2','1/3','1/6'],'random_fraction_pool':list(map(str,pool)),
        'unit_dilation_is_separate_known_signed_cancellation_calibration':True,'all_positive_rational_r_semantics':True,'semantic_denominator_cap':False,
        'scale_policy':'compare ordinary arithmetic-index M; X=M^r; K=1+1/r, R=K/ell; peak of moment zero at u=1',
        'initial_atoms':[0,1,2],'two_atom_coefficients':[-1,1],'source_patterns':2,'random_initial_per_context':3,
        'random_numerators':[-3,3],'random_denominators':[1,2,3,4],
        'moment_relation':{'training_count':8,'total_count':14,'maximum_order':3,'quantization_bits':80,'coefficient_denominator':4096,'tolerance':'1/100000000'},
        'moment_learning_inputs':'anonymous moment vector only; no r, arithmetic names, factor ledger or named identity',
        'response_learning_inputs':'anonymous centered actual primitive response columns and index scales only; no pole locations',
        'response_rounding_denominator':4096,'promotion_slots':4,'promotion_pool':4,
        'promotion_lambdas':['-2','-1','-1/2','-1/6','0','1/6','1/2','1','2'],
        'promotion_rule':'training-ranked actual inverse kernels; Euler derivative y*d/dy-lambda; exact semantics',
        'arithmetic_promotion_rule':'admit inferred moment recurrence only with exact empty factor ledger; compile finite support; otherwise preserve numerical relation',
        'ablation':'same initial and learned shapes, full moment evaluator retained; replace four derivative slots by random shapes',
        'training_points':[1,2,3,8,16,32,64,128,256],'validation_points':[384,512,768],
        'training_q':[2,3,6,12],'validation_new_q':[5,10,17],'limits':['1/2','3/4','1'],'margins':['1/16','1/4'],
        'approach_powers':['1/6','1','2'],'log_powers':['0','1/2'],'rapid_orders':['1/6','1/3','1'],
        'constant_rule':{'training_margin':'3/2','upward_denominator':str(2**128),'minimum':str(Q(1,2**128))},
        'cost_query':['5/8','16'],'archive_size':24,
        'selection':'validation and charged recovery, preserve actual root regimes, proved signed collapse, learned kernels and weak/missing regimes',
        'final_cases':{'count':3,'range':[1025,2048],'offset':'1/3','boundary':[1,2],'q_count':3,'q_range':[19,223]},
        'parent_final_scales_excluded':read(source/'final_cases.json')['integers'],'parent_final_q_excluded':read(source/'parameter_cases.json')['fresh_q'],
        'retained_failed_runs_are_development':failed,'counterfeit_cutoff_binary_power':8192,
        'supplied_proof_backends':['complete absolute-convergence moment identities','exact integer factor-ledger cancellation',
            'peak bound after retaining signed arithmetic cancellation','root unsigned-count weak envelope','finite division zero escape',
            'frozen independent finite-polynomial zero-preservation certificates','uncancelled late-tail pole'],
        'design_assumptions':['positive arithmetic dilation','linear pure-power exponential kernels','normalization by declared peak geometry',
            'Prony recurrences of bounded order','supplied identities and proof methods','bounded enumeration and cost ranking'],
        'developer_preflight':'generic whole-series versus rectangle arithmetic, contracts and proof-scope tests only; no expected discovery winner',
        'generator_model_literature_network_access':False,'not_autonomous_proof_invention':True,'historical_priority_is_acceptance_gate':False,
        'new_prime_distribution_bound_imported':False,'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False}


def restrict(d):
    spec=read(d/'protocol.json');allowed={str((BASE/n).resolve()) for n in spec['code_sha256']}
    allowed|={str((d/n).resolve()) for n in SEALED+['seal.json','parameter_cases.json','parameter_calibration.json','calibration_seal.json']}
    def audit(event,args):
        if event=='open' and not isinstance(args[0],int) and str(Path(args[0]).resolve()) not in allowed:raise PermissionError('Discovery access denied')
        if event.startswith('socket.') or event in ('subprocess.Popen','os.system','os.posix_spawn','os.posix_spawnp'):raise PermissionError('External access denied')
    sys.addaudithook(audit);denied={}
    for name,fn in [('private_final',lambda:open(d/'final_cases.json')),('parent_outcomes',lambda:open(Path(spec['source_run'])/'final_evaluation.json')),
        ('parent_full_batch',lambda:open(Path(spec['source_run'])/'candidate_batch.json')),('literature',lambda:open(spec['named_calibration_dependencies'][0]['path'])),
        ('network',lambda:socket.socket()),('subprocess',lambda:subprocess.run([sys.executable,'-c','pass']))]:
        try:fn()
        except PermissionError:denied[name]=True
        else:raise AssertionError('Isolation failed')
    return denied


def tables(spec,points,rows=None):
    out={}
    for row in spec['parameters'] if rows is None else rows:
        out[pid(row)]=g.complete_table(row,points,spec['maximum_moment'],spec['precision']);print('Complete arithmetic roots',row,'L',out[pid(row)]['Taylor_terms'],flush=True)
    return {'tables':out,'all_infinite_arithmetic_positions_included':True}


def solve(A,b):
    M=[list(row)+[v] for row,v in zip(A,b)];n=len(b)
    for j in range(n):
        k=next((i for i in range(j,n) if M[i][j]),None)
        if k is None:return None
        M[j],M[k]=M[k],M[j];p=M[j][j];M[j]=[v/p for v in M[j]]
        for i in range(n):
            if i!=j:
                p=M[i][j];M[i]=[x-p*y for x,y in zip(M[i],M[j])]
    return [row[-1] for row in M]


def anonymous_prony(values,rule):
    D=2**rule['quantization_bits'];v=[Q(round(Q(flint.arb(x).mid().str(60,radius=False))*D),D) for x in values];out=[]
    for k in range(1,rule['maximum_order']+1):
        rows=[v[h:h+k] for h in range(rule['training_count']-k)];ys=[-v[h+k] for h in range(len(rows))]
        A=[[sum((row[i]*row[j] for row in rows),Q(0)) for j in range(k)] for i in range(k)];b=[sum((row[i]*y for row,y in zip(rows,ys)),Q(0)) for i in range(k)];c=solve(A,b)
        if c is None:out.append({'order':k,'status':'rank_deficient','coefficients':None});continue
        coeff=[x.limit_denominator(rule['coefficient_denominator']) for x in c]+[Q(1)]
        def residual(indices):return max((float(abs(sum((real(a)*flint.arb(values[h+j]) for j,a in enumerate(coeff)),flint.arb(0))).upper()) for h in indices),default=0)
        train=residual(range(rule['training_count']-k));validation=residual(range(rule['training_count'],len(values)-k));tol=float(Q(rule['tolerance']))
        out.append({'order':k,'status':'numerical_recurrence','coefficients':list(map(str,coeff)),'training_residual':train,'validation_residual':validation,
            'training_passed':train<=tol,'validation_passed':validation<=tol,'universal_from_numeric_fit':False})
    return out


def relation_records(spec,data):
    out=[]
    for row in spec['parameters']:
        t=data['tables'][pid(row)]
        for model in ['inverse','unit']:
            values=t['moments'][model][:spec['moment_relation']['total_count']];relations=anonymous_prony(values,spec['moment_relation']);ledger=g.profile(model,row[2])
            for rel in relations:
                admit=rel.get('training_passed',False) and rel.get('validation_passed',False) and not ledger['remaining_factors'] and sum(map(Q,rel['coefficients']))==0
                out.append({'parameter_id':pid(row),'anonymous_channel_id':digest({'parameter_id':pid(row),'model':model}),
                    'decoded_model_after_fit':model,'relation':rel,'universal_certificate_admitted':admit,
                    'proof_certificate':ledger if admit else None,'numeric_only_if_no_certificate':not admit})
    return out


def build(c,row,family,backend='complete_moment_series'):
    semantic=digest({'shape':c,'parameters':row});res=g.residues(c,row);rapid={a:g.rapid_certificate(c,row,a) for a in ['1/6','1/3','1']}
    return {'id':digest({'semantic_operator_id':semantic,'backend':backend}),'semantic_operator_id':semantic,'parameter_id':pid(row),'parameters':row,
        'shape':c,'family':family,'origins':[family],'arithmetic_backend':backend,'residues':res,'zero_bridge':g.zero_bridge(c,row),
        'global_constants':g.global_constants(c,row,res),'rapid_certificates':rapid,'late_tail_pole':g.late_tail_pole(c,row)}


def observations(p,data,points):
    out=g.responses(p['shape'],data['tables'][p['parameter_id']],points,p['residues'])
    if p['arithmetic_backend']=='certified_single_support':
        for M,row in out.items():value=g.finite_response(p['shape'],p['parameters'],M);row['actual_raw_ball']=row['actual_centered_ball']=serialize(value)
    return out


def random_shape(rng,spec):
    ms=sorted(rng.sample(range(spec['maximum_moment']+1),rng.randint(1,4)));terms=[[m,Q(rng.randint(*spec['random_numerators']),rng.choice(spec['random_denominators']))] for m in ms]
    return g.shape(terms if any(c for m,c in terms) else [[ms[0],1]])


def learn_response(columns,points,spec):
    v=[[Q(flint.arb(col[str(M)]['actual_centered_ball']).mid().str(60,radius=False)) for col in columns] for M in points]
    A=[[sum((x[i]*x[j]/Q(M) for M,x in zip(points,v)),Q(0)) for j in range(2)] for i in range(2)];b=[-sum((x[i]*x[2]/Q(M) for M,x in zip(points,v)),Q(0)) for i in range(2)];c=solve(A,b)
    return g.shape([[0,c[0].limit_denominator(spec['response_rounding_denominator'])],[1,c[1].limit_denominator(spec['response_rounding_denominator'])],[2,1]]) if c is not None else None


def generate(spec,forms,data,relations):
    rng=random.Random(spec['seed']);primary={};ablation={};promotions=[];learned=[];arithmetic_promotions=[]
    normalized={digest(g.shape(f['terms'])):g.shape(f['terms']) for f in forms['forms']};patterns=sorted(normalized.values(),key=lambda c:(len(c['terms']),c['maximum_moment'],digest(c)))[:spec['source_patterns']]
    def add(store,c,row,family,backend):
        key=digest({'semantic_operator_id':digest({'shape':c,'parameters':row}),'backend':backend})
        if key not in store:store[key]=build(c,row,family,backend)
        elif family not in store[key]['origins']:store[key]['origins'].append(family)
        return store[key]
    for row in spec['parameters']:
        admitted=[r for r in relations if r['parameter_id']==pid(row) and r['decoded_model_after_fit']=='inverse' and r['universal_certificate_admitted']]
        backend='certified_single_support' if admitted else 'complete_moment_series'
        if admitted:arithmetic_promotions.append({'parameter_id':pid(row),'relation':min(admitted,key=lambda r:r['relation']['order']),
            'compiled_backend':backend,'preserves_all_scale_semantics':True,'RH_information_retained':False})
        local=[]
        def put(c,family):
            p=add(primary,c,row,family,backend);add(ablation,c,row,family,'complete_moment_series')
            if p not in local:local.append(p)
        for m in spec['initial_atoms']:put(g.shape([[m,1]]),'baseline_atom')
        for m,n in combinations(spec['initial_atoms'],2):
            for a in spec['two_atom_coefficients']:put(g.shape([[m,a],[n,1]]),'baseline_two_atoms')
        for c in patterns:put(c,'retuned_source_pattern')
        for _ in range(spec['random_initial_per_context']):put(random_shape(rng,spec),'baseline_random')
        columns=[g.responses(g.shape([[m,1]]),data['tables'][pid(row)],spec['training_points']) for m in range(3)]
        c=learn_response(columns,spec['training_points'],spec)
        if c is not None:put(c,'learned_actual_centered_response')
        learned.append({'parameter_id':pid(row),'shape':c,'analytic_pole_labels_supplied':False})
        def score(p):return max(float((abs(flint.arb(v['actual_centered_ball']))/power(real(M),Q(1,2))).upper()) for M,v in observations(p,data,spec['training_points']).items())
        pool=sorted(local,key=lambda p:(score(p),p['id']))[:spec['promotion_pool']]
        for slot in range(spec['promotion_slots']):
            parent=rng.choice(pool);lam=Q(rng.choice(spec['promotion_lambdas']));R=g.rate(row);terms=defaultdict(Q)
            for m,c in parent['shape']['terms']:terms[m]+=(m-lam)*Q(c);terms[m+1]-=R*Q(c)
            c=g.shape([[m,a] for m,a in terms.items()]);admit=c['maximum_moment']<=spec['maximum_moment']
            promotions.append({'parameter_id':pid(row),'slot':slot,'parent_id':parent['id'],'lambda':str(lam),'shape':c,'admitted':admit})
            if admit:add(primary,c,row,'promoted_actual_Euler_derivative',backend)
            add(ablation,random_shape(rng,spec),row,'ablation_random_slot','complete_moment_series')
    return list(primary.values()),list(ablation.values()),promotions,learned,arithmetic_promotions


def fit(rows,f,qs,spec):
    flint.ctx.prec=640;D=int(spec['constant_rule']['upward_denominator']);out={}
    for q in qs:
        v=max((abs(flint.arb(a['actual_centered_ball']))/g.envelope(f,q,M) for M,a in rows.items()),key=lambda a:float(a.upper()))*real(spec['constant_rule']['training_margin'])
        out[str(q)]=str(max(Q(spec['constant_rule']['minimum']),Q(ceil(Q(v.upper().str(70,radius=False))*D),D)))
    return out


def compare(rows,f,Cs,qs):
    bad=[];unresolved=[];worst=(0,None)
    for q in qs:
        for M,row in rows.items():
            v=abs(flint.arb(row['actual_centered_ball']));B=real(Cs[str(q)])*g.envelope(f,q,M);label=f'{q}:{M}'
            if not v<=B:(bad if v>B else unresolved).append(label)
            ratio=float((v/B).upper())
            if ratio>worst[0]:worst=(ratio,label)
    return {'failures':bad,'unresolved':unresolved,'maximum_ratio':worst[0],'maximum_ratio_case':worst[1],
        'finite_points_passed':not bad and not unresolved,'same_fitted_constants_proved_global':False,'comparisons':len(qs)*len(rows)}


def hypotheses(p,rows,spec):
    out=[];qs=spec['training_q']+spec['validation_new_q']
    for eta,eps,nu,d in product(spec['limits'],spec['margins'],spec['approach_powers'],spec['log_powers']):
        f=g.frontier(eta,eps,nu,d);Cs=fit(rows,f,qs,spec);critical=Q(eta)==Q(1,2);rapid=p['rapid_certificates']['1']['global_premise_proved']
        weak=p['global_constants']['global_ordinary_exponent_one_proved'] and Q(eta)>=1;proved=rapid or weak
        core={'program_id':p['id'],'frontier':f,'constants':Cs}
        cost=g.charge(p,f,Cs,spec['training_q'],spec['cost_query']) if critical else {'best_log_cost':None,'observers':[],'status':'above_critical_limit'}
        out.append(dict(core,id=digest(core),RH_sufficient_if_uniform=critical and p['zero_bridge']['RH_sufficient_if_uniform'],
            uniform_frontier_has_proved_constant_witness=proved,same_fitted_constants_proved=False,
            witness_arithmetic_model='inverse',recovery_cost=cost,
            missing_signed_critical_estimate=critical and not rapid))
    return out


def rank(c):return (not c['validation']['finite_points_passed'],c['recovery_cost']['best_log_cost'] if c['recovery_cost'].get('best_log_cost') is not None else 1e100,c['validation']['maximum_ratio'],c['id'])
def select(candidates,programs,spec):
    ps={p['id']:p for p in programs};out=[]
    def include(pool):
        if pool:
            c=min(pool,key=rank)
            if c not in out and len(out)<spec['archive_size']:out.append(c)
    for row in spec['parameters']:include([c for c in candidates if c['RH_sufficient_if_uniform'] and ps[c['program_id']]['parameters']==row])
    for ell in ['1/6','1/3','1/2']:include([c for c in candidates if ps[c['program_id']]['parameters'][1]==ell and c['uniform_frontier_has_proved_constant_witness'] and not c['RH_sufficient_if_uniform']])
    for label in ['learned_actual_centered_response','promoted_actual_Euler_derivative']:include([c for c in candidates if label in ps[c['program_id']]['origins'] and c['RH_sufficient_if_uniform']])
    include([c for c in candidates if Q(c['frontier']['limit'])==1 and ps[c['program_id']]['global_constants']['global_ordinary_exponent_one_proved']])
    for c in sorted(candidates,key=rank):
        if len(out)>=spec['archive_size']:break
        if c not in out:out.append(c)
    return out


def worker(d):
    spec=read(d/'protocol.json');verify_code(spec);denied=restrict(d);data=tables(spec,spec['training_points']);write(d/'discovery_data.json',dict(data,worker_access_denials=denied))
    relations=relation_records(spec,data);ps,aps,promotions,learned,arithmetic=generate(spec,read(d/'source_forms.json'),data,relations);allps={p['id']:p for p in aps+ps};obs={i:observations(p,data,spec['training_points']) for i,p in allps.items()};cs=[]
    for p in allps.values():cs+=hypotheses(p,obs[p['id']],spec)
    write(d/'candidate_batch.json',{'protocol_sha256':digest(spec),'programs':ps,'ablation_programs':aps,'training_observables':obs,'candidates':cs,
        'moment_relations':relations,'shape_promotions':promotions,'learned_shapes':learned,'arithmetic_promotions':arithmetic,
        'frozen_before_validation':True,'generation_uses_training_only':True});print('Frozen',len(ps),'programs',len(cs),'hypotheses',flush=True)
    vd=tables(spec,spec['validation_points']);vobs={i:observations(p,vd,spec['validation_points']) for i,p in allps.items()};valid=[dict(c,validation=compare(vobs[c['program_id']],c['frontier'],c['constants'],spec['training_q']+spec['validation_new_q'])) for c in cs]
    write(d/'validation_data.json',dict(vd,program_observables=vobs,candidates=valid,candidate_batch_sha256=sha(d/'candidate_batch.json')))
    ids={p['id'] for p in ps};aids={p['id'] for p in aps};arc=select([c for c in valid if c['program_id'] in ids],ps,spec);aarc=select([c for c in valid if c['program_id'] in aids],aps,spec)
    best=lambda rows:min((c['recovery_cost']['best_log_cost'] for c in rows if c['recovery_cost'].get('best_log_cost') is not None),default=None)
    write(d/'archive.json',{'archive':arc,'ablation_archive':aarc,'selection_closed':True,'final_data_used':False,
        'ablation_comparison':{'equal_derivative_proposal_slots':True,'proposal_slots':spec['promotion_slots']*len(spec['parameters']),
            'admitted_shape_promotions':sum(r['admitted'] for r in promotions),'admitted_arithmetic_promotions':len(arithmetic),
            'primary_programs':len(ps),'ablation_programs':len(aps),'best_primary_log_cost':best(arc),'best_ablation_log_cost':best(aarc)}})
    write(d/'seal.json',{'protocol_sha256':digest(spec),'files':{n:sha(d/n) for n in SEALED},'selection_closed':True,'final_cases_exist_at_seal':False,'parameter_cases_exist_at_seal':False});print('Sealed archive',len(arc),flush=True)


def parameter_cases(d):
    spec=read(d/'protocol.json');rule=spec['final_cases'];rng=random.Random(int.from_bytes(os.urandom(32),'big'));excluded=set(spec['training_q']+spec['validation_new_q']+spec['parent_final_q_excluded'])|{q for f in spec['retained_failed_runs_are_development'] for q in f['excluded_final_q']}
    qs=sorted(rng.sample([q for q in range(rule['q_range'][0],rule['q_range'][1]+1) if q not in excluded],rule['q_count']))
    write(d/'parameter_cases.json',{'fresh_q':qs,'seal_sha256':sha(d/'seal.json'),'generated_after_archive_seal':True,'no_final_scale_information_present':True})


def calibrate(d):
    spec=read(d/'protocol.json');verify_code(spec);denied=restrict(d);pc=read(d/'parameter_cases.json');batch=read(d/'candidate_batch.json');out=[]
    for c in read(d/'archive.json')['archive']:out.append({'candidate_id':c['id'],'constants':fit(batch['training_observables'][c['program_id']],c['frontier'],pc['fresh_q'],spec)})
    write(d/'parameter_calibration.json',{'parameters_sha256':digest(pc),'training_only':True,'final_scales_used':False,'worker_access_denials':denied,'illustrative_free_constants':out})
    write(d/'calibration_seal.json',{'archive_seal_sha256':sha(d/'seal.json'),'parameter_cases_sha256':sha(d/'parameter_cases.json'),'parameter_calibration_sha256':sha(d/'parameter_calibration.json'),'final_cases_exist_at_calibration_seal':False})


def final(d):
    spec=read(d/'protocol.json');verify_code(spec);seal=read(d/'seal.json');cal=read(d/'calibration_seal.json')
    for n,h in seal['files'].items():assert sha(d/n)==h
    for key,n in [('archive_seal_sha256','seal.json'),('parameter_cases_sha256','parameter_cases.json'),('parameter_calibration_sha256','parameter_calibration.json')]:assert cal[key]==sha(d/n)
    rule=spec['final_cases'];rng=random.Random(int.from_bytes(os.urandom(32),'big'));excluded=set(spec['parent_final_scales_excluded'])|{x for f in spec['retained_failed_runs_are_development'] for x in f['excluded_final_scales']}
    integers=sorted(rng.sample([M for M in range(rule['range'][0],rule['range'][1]+1) if M not in excluded],rule['count']));points=list(map(str,rule['boundary']+integers))+[str(Q(M)+Q(rule['offset'])) for M in integers];cases={'integers':integers,'index_points':points,'X_semantics':'M^r, exact real roots',
        'calibration_seal_sha256':digest(cal),'generated_after_calibration_seal':True};write(d/'final_cases.json',cases)
    batch=read(d/'candidate_batch.json');arc=read(d/'archive.json');ps={p['id']:p for p in batch['programs']};pids={c['program_id'] for c in arc['archive']};rows=[r for r in spec['parameters'] if any(ps[i]['parameters']==r for i in pids)];data=tables(spec,points,rows);fobs={i:observations(ps[i],data,points) for i in pids};fresh=read(d/'parameter_cases.json')['fresh_q'];calibrated={c['candidate_id']:c['constants'] for c in read(d/'parameter_calibration.json')['illustrative_free_constants']};out=[];controls=[];erasure=[];rapid=[]
    for c in arc['archive']:
        p=ps[c['program_id']];Cs={**c['constants'],**calibrated[c['id']]};qs=spec['training_q']+spec['validation_new_q']+fresh
        out.append(dict(compare(fobs[p['id']],c['frontier'],Cs,qs),candidate_id=c['id'],constants=Cs,
            recovery_cost=g.charge(p,c['frontier'],Cs,qs,spec['cost_query']) if Q(c['frontier']['limit'])==Q(1,2) else {'best_log_cost':None,'observers':[],'status':'above_critical_limit'}))
        if Q(c['frontier']['limit'])==Q(1,2) and p['late_tail_pole']['applies']:
            fake={}
            for M,row in fobs[p['id']].items():
                B=g.late_tail_bound(p['shape'],p['parameters'],M,spec['counterfeit_cutoff_binary_power']);fake[M]=dict(row,actual_centered_ball=serialize(flint.arb(row['actual_centered_ball'])+flint.arb(0,B)))
            controls.append(dict(compare(fake,c['frontier'],Cs,qs),candidate_id=c['id'],fake_observables=fake,
                known_pole_certificate=p['late_tail_pole'],globally_false_uniform_target=True,actual_arithmetic_counterexample=False))
        if c['uniform_frontier_has_proved_constant_witness'] and not p['zero_bridge']['arithmetic_profile']['remaining_factors']:
            erasure.append({'candidate_id':c['id'],'actual_uniform_frontier_proved':True,'kernel_preserves_right_zeros':p['zero_bridge']['kernel_certificate']['all_right_half_ordinary_zeros_preserved'],
                'false_RH_inference_rejected':True,'arithmetic_erases_ordinary_zeros':True})
    for i in pids:
        p=ps[i]
        for a,cert in p['rapid_certificates'].items():
            if not cert['global_premise_proved']:continue
            for M,row in fobs[i].items():assert abs(flint.arb(row['actual_centered_ball']))<=flint.arb(cert['constant_ball'])*power(real(M),-Q(a))
            rapid.append({'program_id':i,'order':a,'fresh_witnesses_passed':True,'actual_inverse_arithmetic':True,'RH_consequence':False})
    write(d/'final_evaluation.json',{'protocol_sha256':digest(spec),'seal_sha256':digest(seal),'calibration_seal_sha256':digest(cal),'cases_sha256':digest(cases),
        'data':data,'program_observables':fobs,'outcomes':out,'late_tail_controls':controls,'zero_erasure_controls':erasure,'signed_rapid_witnesses':rapid,
        'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False})


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('mode',choices=['run','worker','calibrate','final'],nargs='?',default='run');parser.add_argument('--run-dir',type=Path,required=True);parser.add_argument('--source',type=Path);args=parser.parse_args();d=args.run_dir.resolve()
    if args.mode=='worker':worker(d);return
    if args.mode=='calibrate':calibrate(d);return
    if args.mode=='final':final(d);return
    if args.source is None:raise ValueError('Verified typed-lattice source required')
    d.mkdir(parents=True,exist_ok=False);spec=protocol(args.source);write(d/'protocol.json',spec);write(d/'source_forms.json',source_forms(args.source));(d/'frozen_source').mkdir()
    for n in CODE:(d/'frozen_source'/n).write_bytes((BASE/n).read_bytes())
    try:
        subprocess.run([sys.executable,str(BASE/'root_lattice_search.py'),'worker','--run-dir',str(d)],check=True,cwd=BASE);parameter_cases(d)
        subprocess.run([sys.executable,str(BASE/'root_lattice_search.py'),'calibrate','--run-dir',str(d)],check=True,cwd=BASE);final(d)
        subprocess.run([sys.executable,str(BASE/'check_root_lattices.py'),'--run-dir',str(d)],check=True,cwd=BASE)
        from root_lattice_report import summary,text_report
        s=summary(d);write(d/'summary.json',s);(d/'report.txt').write_text(text_report(s));write(BASE/'root-lattice-results/latest.json',{'run_directory':str(d)})
    except Exception as e:write(d/'failure.json',{'error_type':type(e).__name__,'error':str(e),'original_data_and_sources_retained':True});raise


if __name__=='__main__':main()
