#!/usr/bin/env python3
"""Sealed search for signed Gram control and squarefree density corrections."""
import argparse
from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
from math import ceil
from pathlib import Path
import os,random,socket,subprocess,sys
import flint
from estimate_grammar import inverse_one_prefix
from stable_scale_search import BASE,read,write,sha,digest,verify_code
from mellin_kernel_grammar import real,power,serialize,primitive_table,response,global_certificate,envelope
import kernel_correlation_grammar as gram
import kernel_density_bridge as density

CODE=['kernel_correlation_grammar.py','kernel_density_bridge.py','kernel_correlation_search.py',
      'check_kernel_correlations.py','kernel_correlation_report.py','kernel_correlation_proof.txt']
SEALED=['protocol.json','source_forms.json','discovery_data.json','candidate_batch.json','validation_data.json','archive.json']


def pid(row):return digest({'k':row[0],'ell':row[1],'base':row[2]})


def protocol(source):
    from mellin_kernel_report import summary
    source=Path(source).resolve();summary(source);old=read(source/'protocol.json')
    failed=[]
    for f in sorted((BASE/'kernel-correlation-results').glob('*/failure.json')):
        d=f.parent
        failed.append({'run_directory':str(d),'failure_sha256':sha(f),
            'excluded_final_scales':read(d/'final_cases.json').get('integers',[]) if (d/'final_cases.json').exists() else [],
            'excluded_final_q':read(d/'parameter_cases.json').get('fresh_q',[]) if (d/'parameter_cases.json').exists() else [],
            'original_code_sha256':read(d/'protocol.json')['code_sha256'],
            'retained_files_sha256':{p.name:sha(p) for p in d.glob('*.json') if p.name!='failure.json'}})
    return {'schema':1,'grammar_version':gram.VERSION,'seed':2026100871,'precision':384,
        'source_run':str(source),'source_sha256':{n:sha(source/n) for n in ['protocol.json','verification.json','summary.json','candidate_batch.json']},
        'code_sha256':dict(old['code_sha256'],**{n:sha(BASE/n) for n in CODE}),
        'this_stage_source_files':CODE,'named_calibration_dependencies':old['named_calibration_dependencies'],
        'parameters':old['parameters'],'maximum_moment':2,'maximum_dilation':2,
        'pair_groups_per_parameter':4,'single_density_extra_low_energy':2,'single_density_extra_random':1,
        'source_selection':'only kernel forms and pair membership; recalculate certificates; reserve one recovering pair when available, then seeded sampling; every one-atom form plus training-energy and random single forms',
        'fixed_metric_entries':[['1','0','1'],['1','-1','1'],['1','0','0'],['1','1','1']],
        'random_signed_metrics_per_pair':2,'random_positive_metrics_per_pair':2,
        'metric_integer_range':[-3,3],'metric_rounding_denominator':64,'metric_denominator_bits_cap':160,
        'learning':'rank-one least squares and positive inverse training covariance with an exact positive rational ridge',
        'promotion_slots_per_parameter':4,'promotion_pool':6,
        'promotion_rule':'training-energy pool; exact rational congruence S^T H S using seeded unit triangular S; no claim that compression proves an estimate',
        'ablation':'identical initial and learned metrics; replace four promotion proposal slots by seeded random symmetric matrices',
        'matrix_density_leads_per_parameter':2,'rho_grid':['-1','0'],'rho_fit_denominator':64,'rho_resource_cap':16,
        'training_points':[1,2,3,8,16,32,64,128,256],'validation_points':[385,512,768],
        'training_q':[2,3,6,12],'validation_new_q':[5,10,17],
        'energy_limits':['1/2','3/4','1'],'energy_margins':['1/4'],
        'density_limits':['1/4','3/8','1/2'],'density_margins':['1/16','1/4'],
        'approach_powers':['1/6','1','2'],'energy_log_powers':['0','1'],'density_log_powers':['0','1/2','1'],
        'constant_rule':{'training_margin':'3/2','upward_denominator':str(2**128),'minimum':str(Q(1,2**128))},
        'constants_scope':'independent free B_q or C_q; no law for their growth in q; fit only frozen training scales',
        'prefix_rule':'N=max(256,2*ceil(max(points))); complete arithmetic prefix and rigorously enclosed entire infinite tail',
        'energy_cost_query':['5/8','16'],'density_cost_query':['5/16','8'],
        'archive_size':24,'selection':'validation then fully charged conditional cost; preserve roots, singular, learned, promoted, indefinite, density, missing-certificate and weak regimes',
        'final_cases':{'count':3,'range':[1537,3072],'real_offset':'1/3','boundary':[1,2],
            'fresh_q_count':3,'fresh_q_range':[19,223],'generic_count':4,'generic_cutoff':24},
        'parent_final_scales_excluded':read(source/'final_cases.json')['integers'],
        'parent_final_q_excluded':read(source/'parameter_cases.json')['fresh_q'],
        'retained_failed_runs_are_development':failed,'counterfeit_tail_cutoff':str(2**200),
        'wrong_density_center_factor':str(1+Q(1,2**100)),
        'supplied_backends':['complete arithmetic Gram identity','square-divisor inversion and all-real-scale density remainder',
            'exact rational positive and singular metric factorization','all-height parent bank certificate',
            'common-rate polynomial strip certificate','ordinary-zero multiplicity, reflection and height halving',
            'free cofinal growth targets and fully charged finite observers'],
        'developer_preflight':'training-sized complete diagonal atoms and products; generic source-form counts; no new candidate scoring, validation, archive or final cases',
        'generator_model_literature_network_access':False,'not_autonomous_proof_invention':True,
        'historical_priority_is_acceptance_gate':False,'new_prime_distribution_estimate_imported':False,
        'machine_formalized':False,'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False}


def source_forms(source):
    b=read(Path(source)/'candidate_batch.json')
    return {'programs':[{k:p[k] for k in ['id','parameter_id','parameters','kernel']} for p in b['programs']],
        'pairs':[{k:g[k] for k in ['id','parameter_id','parameters','member_ids']} for g in b['banks'] if len(g['member_ids'])==2],
        'growth_fits_archive_and_final_outcomes_supplied':False}


def restrict(directory):
    spec=read(directory/'protocol.json')
    allowed={str((BASE/n).resolve()) for n in spec['code_sha256']}
    allowed|={str((directory/n).resolve()) for n in SEALED+['seal.json','parameter_cases.json','parameter_calibration.json','calibration_seal.json']}
    def audit(event,args):
        if event=='open' and not isinstance(args[0],int) and str(Path(args[0]).resolve()) not in allowed:
            raise PermissionError('Discovery or calibration file access denied')
        if event.startswith('socket.') or event in ('subprocess.Popen','os.system','os.posix_spawn','os.posix_spawnp'):
            raise PermissionError('External access denied')
    sys.addaudithook(audit);denied={}
    for label,action in [('private_final',lambda:open(directory/'final_cases.json')),
        ('parent_outcomes',lambda:open(Path(spec['source_run'])/'final_evaluation.json')),
        ('parent_full_batch',lambda:open(Path(spec['source_run'])/'candidate_batch.json')),
        ('literature',lambda:open(spec['named_calibration_dependencies'][0]['path'])),
        ('network',lambda:socket.socket()),('subprocess',lambda:subprocess.run([sys.executable,'-c','pass']))]:
        try:action()
        except PermissionError:denied[label]=True
        else:raise AssertionError('Isolation probe failed')
    return denied


def tables(spec,points,parameters=None):
    N=max(256,2*ceil(max(map(Q,points))));mu=inverse_one_prefix(N);out={}
    for row in spec['parameters'] if parameters is None else parameters:
        out[pid(row)]={'inverse':primitive_table(mu,*map(Q,row),points,2,2,spec['precision']),
            'squarefree':gram.squarefree_table(mu,*map(Q,row),points,4,2,spec['precision'])}
        print('Complete inverse and squarefree tails',row,'N',N,flush=True)
    flint.ctx.prec=spec['precision']
    return {'cutoff':N,'inverse_coefficient_sha256':digest(mu),'tables':out,'all_infinite_tails_included':True}


def responses(Ks,table,points):return [response(K,table['inverse'],points) for K in Ks]


def observations(p,data,points):
    table=data['tables'][p['parameter_id']];vs=responses(p['kernels'],table,points)
    out=gram.observable(p['kernels'],p['metric'],vs,table['squarefree'],p['diagonal_terms'],points)
    zs=density.value(out,p['diagonal_certificate'])
    for X in out:out[X]['density_correction_ball']=zs[X]
    return out


def build(kind,Ks,H,row,members,family,method):
    core={'kind':kind,'parameters':row,'kernels':Ks,'metric':H}
    p=dict(core,id=digest(core),parameter_id=pid(row),source_members=members,family=family,method=method)
    p['diagonal_terms']=gram.diagonal_terms(Ks,H,Q(row[2]))
    p['diagonal_certificate']=gram.diagonal_certificate(p['diagonal_terms'],*map(Q,row[:2]))
    if kind=='energy':p['recovery']=gram.recovery(Ks,H)
    else:
        p['density_recovery']=density.recovery_certificate(p['diagonal_terms'],*map(Q,row[:2]))
        p['density_constants']=density.constants(p['diagonal_terms'],*map(Q,row[:2]),p['diagonal_certificate'])
    return p


def energy_score(p,obs):
    return sum(abs(float(flint.arb(v['energy_ball']).mid()))/float(Q(X)) for X,v in obs.items())


def random_entries(rng,spec):
    lo,hi=spec['metric_integer_range']
    return [Q(rng.randint(lo,hi),rng.randint(1,3)) for _ in range(3)]


def congruence(H,S):
    a,b,c=map(Q,H['entries']);u,v,w,z=map(Q,S)
    return gram.metric(a*u*u+2*b*u*w+c*w*w,a*u*v+b*(u*z+v*w)+c*w*z,a*v*v+2*b*v*z+c*z*z)


def generate(spec,forms,data):
    old={p['id']:p for p in forms['programs']};primary=[];ablation=[];rejected=[];promotions=[];selected_pairs=[];seen=set()
    def admit(kind,Ks,H,row,members,family,method,out):
        if max(Q(x).denominator.bit_length() for x in H['entries'])>spec['metric_denominator_bits_cap']:
            rejected.append({'family':family,'reason':'declared denominator bit resource cap','parameters':row,'metric':H});return
        p=build(kind,Ks,H,row,members,family,method)
        if p['id'] in seen:
            rejected.append({'family':family,'reason':'duplicate exact normalized observable','id':p['id']});return
        if not p['diagonal_terms']:
            rejected.append({'family':family,'reason':'identically zero diagonal observable','id':p['id']});return
        seen.add(p['id']);out.append(p)
    for row in spec['parameters']:
        par=pid(row);rng=random.Random(spec['seed']+int(par[:12],16));table=data['tables'][par]
        pairs=[g for g in forms['pairs'] if g['parameter_id']==par];rng.shuffle(pairs)
        good=[g for g in pairs if gram.recovery([old[i]['kernel'] for i in g['member_ids']],gram.metric(1,0,1))['all_height_no_common_zero']]
        chosen=good[:1];chosen += [g for g in pairs if g not in chosen][:spec['pair_groups_per_parameter']-len(chosen)]
        selected_pairs+=chosen
        for g in pairs:
            if g not in chosen:rejected.append({'source_pair':g['id'],'reason':'declared pair group sampling resource limit','parameters':row})
        baseline=[]
        for g in chosen:
            Ks=[old[i]['kernel'] for i in g['member_ids']];vals=responses(Ks,table,spec['training_points'])
            rr=[(Q(round(float(flint.arb(vals[0][str(X)]).mid())*2**60),2**60),
                 Q(round(float(flint.arb(vals[1][str(X)]).mid())*2**60),2**60),Q(X)) for X in spec['training_points']]
            A=sum((f*f/X for f,h,X in rr),Q(0));B=sum((f*h/X for f,h,X in rr),Q(0));C=sum((h*h/X for f,h,X in rr),Q(0))
            ridge=(A+C+1)/spec['metric_rounding_denominator']
            r=Q(round((-B/C if C else Q(0))*spec['metric_rounding_denominator']),spec['metric_rounding_denominator'])
            proposals=[('fixed_metric',gram.metric(*v),'declared matrix enumeration') for v in spec['fixed_metric_entries']]
            proposals += [('random_signed_metric',gram.metric(*v),'seeded signed symmetric matrix') for _ in range(spec['random_signed_metrics_per_pair']) if any(v:=random_entries(rng,spec))]
            for _ in range(spec['random_positive_metrics_per_pair']):
                u,v,w,z=[Q(rng.randint(-3,3),rng.randint(1,3)) for _ in range(4)]
                if u or v or w or z:proposals.append(('random_positive_metric',gram.metric(u*u+w*w,u*v+w*z,v*v+z*z),'exact positive congruence'))
            proposals += [('learned_rank_one',gram.metric(1,r,r*r),'rational rounded training least squares'),
                ('learned_positive_covariance',gram.metric(C+ridge,-B,A+ridge),'exact positive inverse training covariance; ridge=(A+C+1)/64')]
            for family,H,method in proposals:admit('energy',Ks,H,row,g['member_ids'],family,method,baseline)
        base_seen=seen.copy();start=baseline.copy();pscores={p['id']:energy_score(p,observations(p,data,spec['training_points'])) for p in baseline}
        pool=sorted(baseline,key=lambda p:(pscores[p['id']],p['id']))[:spec['promotion_pool']]
        for _ in range(spec['promotion_slots_per_parameter']):
            parent=rng.choice(pool);h=rng.choice([Q(-1),Q(-1,2),Q(1,2),Q(1)])
            S=[Q(1),h,Q(0),Q(1)] if rng.randrange(2) else [Q(1),Q(0),h,Q(1)]
            before=len(start);method={'parent':parent['id'],'production':'rational_congruence','matrix':list(map(str,S)),'training_energy':pscores[parent['id']]}
            admit('energy',parent['kernels'],congruence(parent['metric'],S),row,parent['source_members'],'promoted_congruence',method,start)
            promotions.append(dict(method,admitted=len(start)>before,parameters=row))
        primary+=start;seen=base_seen;aslots=baseline.copy();arng=random.Random(spec['seed']+int(par[:12],16)+701)
        for _ in range(spec['promotion_slots_per_parameter']):
            entries=random_entries(arng,spec)
            if not any(entries):rejected.append({'family':'ablation_random_slot','reason':'zero matrix','parameters':row});continue
            parent=arng.choice(pool);admit('energy',parent['kernels'],gram.metric(*entries),row,parent['source_members'],
                'ablation_random_slot','promotion-disabled random matrix proposal',aslots)
        ablation+=aslots;seen|={p['id'] for p in start}
        singles=[p for p in forms['programs'] if p['parameter_id']==par]
        def score(p):return sum(float(flint.arb(v).mid())**2/float(Q(X)) for X,v in response(p['kernel'],table['inverse'],spec['training_points']).items())
        selected=[p for p in singles if len(p['kernel']['terms'])==1]
        selected += [p for p in sorted(singles,key=lambda p:(score(p),p['id'])) if p not in selected][:spec['single_density_extra_low_energy']]
        rest=[p for p in singles if p not in selected];rng.shuffle(rest);selected+=rest[:spec['single_density_extra_random']]
        ds=[]
        for p in selected:admit('density',[p['kernel'],p['kernel']],gram.metric(1,0,0),row,[p['id']],
            'single_kernel_density','source-form complexity, training energy or frozen random sampling',ds)
        matrix_pool=sorted(start,key=lambda p:(sum(abs(float(flint.arb(v['density_correction_ball']).mid()))/float(Q(X))**Q(1,2)
            for X,v in observations(p,data,spec['training_points']).items()),p['id']))
        for p in matrix_pool[:spec['matrix_density_leads_per_parameter']]:admit('density',p['kernels'],p['metric'],row,p['source_members'],
            'matrix_density','lowest normalized training density correction',ds)
        primary+=ds;ablation+=ds
    return primary,ablation,rejected,promotions,selected_pairs


@lru_cache(maxsize=None)
def bound(kind,eta,margin,nu,d,q,X):
    if kind=='energy':return gram.growth(eta,margin,nu,d,q,X)
    return envelope({'limit':eta,'margin':margin,'approach_power':nu,'log_power':d},q,Q(X))


def env(kind,f,q,X):return bound(kind,f['limit'],f['margin'],f['approach_power'],f['log_power'],q,str(X))


def target_value(kind,row,rho='0'):
    if kind=='density':return abs(flint.arb(row['density_correction_ball']))
    return flint.arb(row['energy_ball'])-real(1+Q(rho))*flint.arb(row['diagonal_ball'])


def fit(kind,obs,f,rho,qs,spec):
    D=int(spec['constant_rule']['upward_denominator']);out={}
    for q in qs:
        maximum=max(flint.arb(0).upper(),*( (target_value(kind,r,rho)/env(kind,f,q,X)).upper() for X,r in obs.items()))
        out[str(q)]=str(Q(max(1,int((maximum*real(spec['constant_rule']['training_margin'])*D).ceil().fmpz())),D))
    return out


def compare(kind,obs,f,rho,constants,qs):
    failures=[];unresolved=[];worst=(0,None)
    for q in qs:
        for X,row in obs.items():
            v=target_value(kind,row,rho);B=real(constants[str(q)])*env(kind,f,q,X);key=f'{q}:{X}'
            if not v<=B:(failures if v>B else unresolved).append(key)
            ratio=max(0,float((v/B).upper()))
            if ratio>worst[0]:worst=(ratio,key)
    return {'failures':failures,'unresolved':unresolved,'maximum_ratio':worst[0],'maximum_ratio_case':worst[1],
        'finite_points_passed':not failures and not unresolved,'uniform_signed_premise_proved':False,'point_comparisons':len(obs)*len(qs)}


def hypotheses(p,obs,spec):
    kind=p['kind'];qs=spec['training_q']+spec['validation_new_q'];out=[]
    rhos=list(map(Q,spec['rho_grid'])) if kind=='energy' else [Q(0)]
    if kind=='energy':
        rr=[(Q(round(float(flint.arb(r['energy_ball']).mid())*2**60),2**60),
            Q(round(float(flint.arb(r['diagonal_ball']).mid())*2**60),2**60),Q(X)) for X,r in obs.items()]
        den=sum((D*D/X**2 for E,D,X in rr),Q(0));num=sum((E*D/X**2 for E,D,X in rr),Q(0))
        if den:
            rho=Q(round((num/den-1)*spec['rho_fit_denominator']),spec['rho_fit_denominator'])
            if abs(rho)<=spec['rho_resource_cap'] and rho not in rhos:rhos.append(rho)
    grids=product(spec[kind+'_limits'],spec[kind+'_margins'],spec['approach_powers'],spec[kind+'_log_powers'],rhos)
    for eta,margin,nu,d,rho in grids:
        f=(gram.energy_frontier if kind=='energy' else density.frontier)(eta,margin,nu,d)
        Cs=fit(kind,obs,f,str(rho),qs,spec)
        if kind=='energy':
            eligible=Q(eta)==Q(1,2) and p['recovery']['all_height_no_common_zero'];attempt=gram.weak_attempt(p,f,rho)
            cost=gram.charge(p,f,rho,Cs,spec['training_q'],spec['energy_cost_query']) if Q(eta)==Q(1,2) else {'status':'above_RH_point_limiting_exponent','best_log_cost':None,'observers':[]}
        else:
            attempt=density.transfer(p,f);eligible=attempt['RH_sufficient_if_uniform']
            cost=density.charge(p,f,Cs,spec['training_q'],spec['density_cost_query']) if Q(eta)==Q(1,4) else {'status':'above_RH_density_limiting_exponent','best_log_cost':None,'observers':[]}
        core={'program_id':p['id'],'kind':kind,'frontier':f,'rho':str(rho),'illustrative_constants_by_q':Cs}
        out.append(dict(core,id=digest(core),RH_sufficient_if_uniform=eligible,recovery_cost=cost,certificate_attempt=attempt))
    return out


def select(candidates,programs,spec):
    ps={p['id']:p for p in programs};out=[]
    def key(c):return (not c['validation']['finite_points_passed'],c['recovery_cost']['best_log_cost'] if c['recovery_cost'].get('best_log_cost') is not None else 1e100,c['validation']['maximum_ratio'],c['id'])
    def include(pool):
        if pool:
            c=min(pool,key=key)
            if c not in out and len(out)<spec['archive_size']:out.append(c)
    for kind in ['energy','density']:
        for ell in sorted({r[1] for r in spec['parameters']},key=Q):
            include([c for c in candidates if c['kind']==kind and c['RH_sufficient_if_uniform'] and ps[c['program_id']]['parameters'][1]==ell])
    for kind in ['energy','density']:
        for nu in spec['approach_powers']:include([c for c in candidates if c['kind']==kind and c['RH_sufficient_if_uniform'] and c['frontier']['approach_power']==nu])
    for label in ['singular','learned','promoted','indefinite','missing_density','weak_energy','weak_density']:
        def category(c):
            p=ps[c['program_id']]
            return (label=='singular' and c['RH_sufficient_if_uniform'] and p['kind']=='energy' and p['metric']['rank']==1 or
                label=='learned' and p['family'].startswith('learned') or label=='promoted' and p['family'].startswith('promoted') or
                label=='indefinite' and not p['metric']['positive_semidefinite'] or label=='missing_density' and p['kind']=='density' and not p['density_recovery']['all_height_recovery'] or
                label=='weak_energy' and p['kind']=='energy' and Q(c['frontier']['limit'])>=1 or
                label=='weak_density' and p['kind']=='density' and Q(c['frontier']['limit'])>=Q(1,2))
        include([c for c in candidates if category(c)])
    for c in sorted(candidates,key=key):
        if len(out)>=spec['archive_size']:break
        if c not in out:out.append(c)
    return out


def worker(directory):
    spec=read(directory/'protocol.json');verify_code(spec);denials=restrict(directory);flint.ctx.prec=spec['precision']
    data=tables(spec,spec['training_points']);write(directory/'discovery_data.json',dict(data,worker_access_denials=denials))
    ps,aps,rejections,promotions,groups=generate(spec,read(directory/'source_forms.json'),data)
    allps={p['id']:p for p in aps+ps};obs={i:observations(p,data,spec['training_points']) for i,p in allps.items()};cs=[]
    for p in allps.values():cs+=hypotheses(p,obs[p['id']],spec)
    batch={'protocol_sha256':digest(spec),'programs':ps,'ablation_programs':aps,'training_observables':obs,'candidates':cs,
        'selected_source_pairs':groups,'rejected_proposals':rejections,'promotions':promotions,'frozen_before_validation':True,'generation_uses_training_only':True}
    write(directory/'candidate_batch.json',batch);print('Frozen',len(ps),'programs and',len(cs),'hypotheses',flush=True)
    vd=tables(spec,spec['validation_points']);vobs={i:observations(p,vd,spec['validation_points']) for i,p in allps.items()}
    validated=[dict(c,validation=compare(c['kind'],vobs[c['program_id']],c['frontier'],c['rho'],c['illustrative_constants_by_q'],spec['training_q']+spec['validation_new_q'])) for c in cs]
    write(directory/'validation_data.json',dict(vd,candidate_batch_sha256=sha(directory/'candidate_batch.json'),program_observables=vobs,candidates=validated))
    ids={p['id'] for p in ps};aids={p['id'] for p in aps};archive=select([c for c in validated if c['program_id'] in ids],ps,spec)
    aarchive=select([c for c in validated if c['program_id'] in aids],aps,spec)
    def best(rows):return min((c['recovery_cost']['best_log_cost'] for c in rows if c['recovery_cost'].get('best_log_cost') is not None),default=None)
    write(directory/'archive.json',{'archive':archive,'ablation_archive':aarchive,'selection_closed':True,'final_data_used':False,
        'ablation_comparison':{'equal_promotion_slot_budgets':True,'proposal_slots':spec['promotion_slots_per_parameter']*len(spec['parameters']),
            'primary_programs':len(ps),'ablation_programs':len(aps),'admitted_promotions':sum(p['admitted'] for p in promotions),
            'best_primary_log_cost':best(archive),'best_ablation_log_cost':best(aarchive)},
        'negative_controls':[{'candidate_id':c['id'],'kind':c['kind'],'same_fitted_constants':True,
            'analytic_status':'globally_false_by_uncancelled_pole_at_one'} for c in archive if c['RH_sufficient_if_uniform'] and
            (c['kind']=='energy' or not flint.arb(allps[c['program_id']]['diagonal_certificate']['main_coefficient_ball']).contains(0))]})
    write(directory/'seal.json',{'protocol_sha256':digest(spec),'files':{n:sha(directory/n) for n in SEALED},
        'selection_closed':True,'final_cases_exist_at_seal':False,'parameter_cases_exist_at_seal':False})
    print('Sealed archive',len(archive),'RH-if-uniform',sum(c['RH_sufficient_if_uniform'] for c in archive),flush=True)


def parameter_cases(directory):
    spec=read(directory/'protocol.json');rule=spec['final_cases'];rng=random.Random(int.from_bytes(os.urandom(32),'big'))
    excluded=set(spec['training_q']+spec['validation_new_q']+spec['parent_final_q_excluded'])|{q for r in spec['retained_failed_runs_are_development'] for q in r['excluded_final_q']}
    qs=sorted(rng.sample([q for q in range(rule['fresh_q_range'][0],rule['fresh_q_range'][1]+1) if q not in excluded],rule['fresh_q_count']))
    write(directory/'parameter_cases.json',{'fresh_q':qs,'seal_sha256':sha(directory/'seal.json'),'generated_after_archive_seal':True,'no_final_scale_information_present':True})


def calibrate(directory):
    spec=read(directory/'protocol.json');verify_code(spec);denials=restrict(directory);flint.ctx.prec=spec['precision']
    pc=read(directory/'parameter_cases.json');batch=read(directory/'candidate_batch.json');ps={p['id']:p for p in batch['programs']};out=[]
    for c in read(directory/'archive.json')['archive']:
        p=ps[c['program_id']];Cs=fit(c['kind'],batch['training_observables'][p['id']],c['frontier'],c['rho'],pc['fresh_q'],spec)
        out.append({'candidate_id':c['id'],'constants':Cs})
    write(directory/'parameter_calibration.json',{'parameters_sha256':digest(pc),'training_only':True,'final_scales_used':False,'worker_access_denials':denials,'illustrative_free_constants':out})
    write(directory/'calibration_seal.json',{'archive_seal_sha256':sha(directory/'seal.json'),'parameter_cases_sha256':sha(directory/'parameter_cases.json'),
        'parameter_calibration_sha256':sha(directory/'parameter_calibration.json'),'final_cases_exist_at_calibration_seal':False})


def generic_inverse(f):
    g=[Q(0)]*len(f);g[1]=1/f[1]
    for n in range(2,len(f)):g[n]=-sum((f[d]*g[n//d] for d in range(2,n+1) if n%d==0),Q(0))/f[1]
    return g


def generic_observation(case,p):
    f=list(map(Q,case['input']));g=generic_inverse(f);X=Q(case['scale']);k,ell,b=map(Q,p['parameters']);vec=[]
    for n in range(1,len(f)):
        y=power(real(X)/n,ell);xk=power(real(X)/n,k)
        vec.append([xk*sum((real(c)*(real(b**j)*y)**m*(-real(b**j)*y).exp() for m,j,c in K['terms']),flint.arb(0)) for K in p['kernels']])
    F=[sum((real(g[n])*vec[n-1][i] for n in range(1,len(f))),flint.arb(0)) for i in range(2)]
    a,h,c=map(real,p['metric']['entries']);E=a*F[0]**2+2*h*F[0]*F[1]+c*F[1]**2
    D=sum((real(g[n]**2)*(a*v[0]**2+2*h*v[0]*v[1]+c*v[1]**2) for n,v in enumerate(vec,1)),flint.arb(0))
    return {'case':case,'program_id':p['id'],'inverse':list(map(str,g)),'response_balls':list(map(serialize,F)),
        'energy_ball':serialize(E),'diagonal_ball':serialize(D),'off_diagonal_ball':serialize(E-D),
        'infinite_tail_claimed':False,'squarefree_Euler_identity_claimed':False}


def final(directory):
    spec=read(directory/'protocol.json');verify_code(spec);seal=read(directory/'seal.json');cal=read(directory/'calibration_seal.json')
    for n,h in seal['files'].items():assert sha(directory/n)==h
    for key,n in [('archive_seal_sha256','seal.json'),('parameter_cases_sha256','parameter_cases.json'),('parameter_calibration_sha256','parameter_calibration.json')]:assert cal[key]==sha(directory/n)
    if (directory/'final_cases.json').exists():raise FileExistsError('Fresh final cases must be retained')
    seed=int.from_bytes(os.urandom(32),'big');rng=random.Random(seed);rule=spec['final_cases']
    excluded=set(spec['parent_final_scales_excluded'])|{n for r in spec['retained_failed_runs_are_development'] for n in r['excluded_final_scales']}
    integers=sorted(rng.sample([n for n in range(rule['range'][0],rule['range'][1]+1) if n not in excluded],rule['count']))
    points=sorted(set(map(Q,integers+rule['boundary']))|{Q(n)+Q(rule['real_offset']) for n in integers})
    batch=read(directory/'candidate_batch.json');arc=read(directory/'archive.json');ps={p['id']:p for p in batch['programs']};ids={c['program_id'] for c in arc['archive']}
    generic=[{'input':['0','1']+[str(Q(rng.randint(-5,5),rng.randint(1,5))) for _ in range(rule['generic_cutoff']-1)],
        'scale':str(Q(rng.randint(2,31),rng.randint(1,7))),'program_id':rng.choice(sorted(ids))} for _ in range(rule['generic_count'])]
    cases={'seed':str(seed),'integers':integers,'points':list(map(str,points)),'generic_inputs':generic,
        'calibration_seal_sha256':digest(cal),'generated_after_calibration_seal':True}
    write(directory/'final_cases.json',cases);pc=read(directory/'parameter_cases.json');calcs={o['candidate_id']:o['constants'] for o in read(directory/'parameter_calibration.json')['illustrative_free_constants']}
    params=sorted({tuple(ps[i]['parameters']) for i in ids});data=tables(spec,points,params);obs={i:observations(ps[i],data,points) for i in ids}
    outcomes=[];controls=[];weak=[];increments=[];qs=spec['training_q']+pc['fresh_q'];flint.ctx.prec=spec['precision']
    for c in arc['archive']:
        p=ps[c['program_id']];Cs=dict(c['illustrative_constants_by_q'],**calcs[c['id']]);rows={str(n):obs[p['id']][str(n)] for n in integers+rule['boundary']}
        o=compare(c['kind'],rows,c['frontier'],c['rho'],Cs,qs)
        freshcost=(gram.charge(p,c['frontier'],c['rho'],Cs,pc['fresh_q'],spec['energy_cost_query']) if c['kind']=='energy' else density.charge(p,c['frontier'],Cs,pc['fresh_q'],spec['density_cost_query'])) if c['RH_sufficient_if_uniform'] else {'status':'not_RH_eligible','best_log_cost':None,'observers':[]}
        outcomes.append(dict(o,candidate_id=c['id'],RH_sufficient_if_uniform=c['RH_sufficient_if_uniform'],fresh_parameter_recovery_cost=freshcost))
        if c['RH_sufficient_if_uniform'] and (c['kind']=='energy' or not flint.arb(p['diagonal_certificate']['main_coefficient_ball']).contains(0)):
            if c['kind']=='density':
                zs=density.value(rows,p['diagonal_certificate'],spec['wrong_density_center_factor']);fake={X:dict(v,density_correction_ball=zs[X]) for X,v in rows.items()}
                gate=density.transfer(p,c['frontier'],spec['wrong_density_center_factor'])
                assert gate['status']=='globally_false_uncancelled_density_pole_at_one'
                control={'control_kind':'wrong_density_center','center_factor':spec['wrong_density_center_factor'],'fake_density_normalizer_is_not_correct':True}
            else:
                k,ell,b=map(Q,p['parameters']);H=Q(spec['counterfeit_tail_cutoff']);vs=responses(p['kernels'],data['tables'][p['parameter_id']],list(map(Q,rows)))
                fv=[]
                for K,v in zip(p['kernels'],vs):
                    frows={}
                    for X,txt in v.items():
                        Xq=Q(X);err=sum((real(abs(Q(a)))*real(b**(j*m))*power(real(Xq),k+ell*m)*power(real(H),1-k-ell*m)/real(k+ell*m-1) for m,j,a in K['terms']),flint.arb(0))
                        frows[X]=serialize(flint.arb(txt)+flint.arb(0,err))
                    fv.append(frows)
                fake=gram.observable(p['kernels'],p['metric'],fv,data['tables'][p['parameter_id']]['squarefree'],p['diagonal_terms'],list(map(Q,rows)))
                control={'control_kind':'counterfeit_inverse_tail','tail_cutoff':str(H),'counterfeit_responses':fv,
                    'diagonal_is_actual_arithmetic_comparator':True,'counterfeit_pair_decomposition_claimed':False}
            controls.append(dict(compare(c['kind'],fake,c['frontier'],c['rho'],Cs,qs),candidate_id=c['id'],complete_control_observables=fake,
                analytic_status='globally_false_by_uncancelled_pole_at_one',actual_arithmetic=False,**control))
    for i in sorted(ids):
        p=ps[i];dc=p['diagonal_certificate'];V=flint.arb(dc['signed_remainder_constant_ball']);A=flint.arb(dc['main_coefficient_ball'])
        gc=density.constants(p['diagonal_terms'],*map(Q,p['parameters'][:2]),dc);J=flint.arb(gc['density_unit_increment_constant_ball'])
        for X,row in obs[i].items():weak.append({'program_id':i,'scale':X,'passed':bool(abs(flint.arb(row['density_correction_ball']))<=V*power(real(X),Q(1,2)))})
        for n in integers:
            diff=abs(flint.arb(obs[i][str(Q(n)+Q(rule['real_offset']))]['density_correction_ball'])-flint.arb(obs[i][str(n)]['density_correction_ball']))
            increments.append({'program_id':i,'integer':n,'difference_ball':serialize(diff),'bound_ball':serialize(J*real(rule['real_offset'])),'passed':bool(diff<=J*real(rule['real_offset']))})
    generic_rows=[generic_observation(case,ps[case['program_id']]) for case in generic]
    write(directory/'final_evaluation.json',{'protocol_sha256':digest(spec),'seal_sha256':digest(seal),'cases_sha256':digest(cases),'calibration_seal_sha256':digest(cal),
        'complete_arithmetic_data':data,'program_observables':obs,'outcomes':outcomes,'negative_controls':controls,
        'all_scale_diagonal_certificate_finite_checks':weak,'density_unit_increment_checks':increments,'generic_inputs':generic_rows,
        'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False})
    print('Fresh signed observables',len(obs),'scales',len(points),'q',qs,flush=True)


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('mode',choices=['run','worker','calibrate','final'],nargs='?',default='run')
    parser.add_argument('--run-dir',type=Path,required=True);parser.add_argument('--source',type=Path);args=parser.parse_args();d=args.run_dir.resolve()
    if args.mode=='worker':worker(d);return
    if args.mode=='calibrate':calibrate(d);return
    if args.mode=='final':final(d);return
    if args.source is None:raise ValueError('Verified complete-tail Mellin source required')
    d.mkdir(parents=True,exist_ok=False);spec=protocol(args.source);write(d/'protocol.json',spec);write(d/'source_forms.json',source_forms(args.source));(d/'frozen_source').mkdir()
    for n in CODE:(d/'frozen_source'/n).write_bytes((BASE/n).read_bytes())
    try:
        subprocess.run([sys.executable,str(BASE/'kernel_correlation_search.py'),'worker','--run-dir',str(d)],check=True,cwd=BASE)
        parameter_cases(d)
        subprocess.run([sys.executable,str(BASE/'kernel_correlation_search.py'),'calibrate','--run-dir',str(d)],check=True,cwd=BASE)
        final(d)
        subprocess.run([sys.executable,str(BASE/'check_kernel_correlations.py'),'--run-dir',str(d)],check=True,cwd=BASE)
        from kernel_correlation_report import summary
        write(d/'summary.json',summary(d));write(BASE/'kernel-correlation-results/latest.json',{'run_directory':str(d)})
    except Exception as exc:
        write(d/'failure.json',{'error_type':type(exc).__name__,'error':str(exc),'original_data_and_outcomes_retained':True});raise


if __name__=='__main__':main()
