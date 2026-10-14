#!/usr/bin/env python3
"""Sealed typed arithmetic search, global certificates and fractional banks."""
import argparse
from collections import defaultdict
from fractions import Fraction as Q
from itertools import product,combinations
from math import ceil
from pathlib import Path
import os,random,socket,subprocess,sys
import flint
from stable_scale_search import BASE,read,write,sha,digest,verify_code
from mellin_kernel_grammar import real,power
import lattice_synthesis_grammar as g
import lattice_zero_bridge as z

CODE=['lattice_synthesis_grammar.py','lattice_zero_bridge.py','lattice_synthesis_search.py',
      'check_lattice_synthesis.py','lattice_synthesis_report.py','lattice_synthesis_proof.txt',
      'test_lattice_synthesis_contracts.py','plot_lattice_synthesis.py']
SEALED=['protocol.json','source_forms.json','discovery_data.json','candidate_batch.json','validation_data.json','archive.json']


def pid(row):return digest({'K':row[0],'ell':row[1],'r':row[2],'rate':'2'})


def source_forms(source):
    batch=read(Path(source)/'candidate_batch.json');out=[]
    for p in batch['programs']:
        for kernel in p['kernels']:
            out.append({'parent_id':p['id'],'parameters':p['parameters'],'terms':kernel['terms']})
    return {'forms':out,'growth_fits_archive_and_final_outcomes_supplied':False,
        'use':'single-rate projections of source forms; exponential rate retuned to 2 as a declared grammar production'}


def protocol(source):
    from kernel_correlation_report import summary
    source=Path(source).resolve();summary(source);old=read(source/'protocol.json');seed=2026100822;rng=random.Random(seed)
    pool=sorted({Q(p,q) for p in range(3,15) for q in range(1,5) if 1<Q(p,q)<=Q(7,2)})
    selected=sorted(rng.sample([r for r in pool if r<2],2)+[rng.choice([r for r in pool if r>=2 and r.denominator==1]),rng.choice([r for r in pool if r>2 and r.denominator!=1])])
    rows=[]
    for ell in sorted({Q(row[1]) for row in old['parameters']}):
        K=min(2*Q(row[0]) for row in old['parameters'] if Q(row[1])==ell)
        rows += [list(map(str,(K,ell,r))) for r in selected]
    failed=[]
    for f in sorted((BASE/'lattice-synthesis-results').glob('*/failure.json')):
        d=f.parent
        failed.append({'run_directory':str(d),'failure_sha256':sha(f),
            'excluded_final_scales':read(d/'final_cases.json').get('integers',[]) if (d/'final_cases.json').exists() else [],
            'excluded_final_q':read(d/'parameter_cases.json').get('fresh_q',[]) if (d/'parameter_cases.json').exists() else [],
            'original_code_sha256':read(d/'protocol.json')['code_sha256'],
            'retained_files_sha256':{p.name:sha(p) for p in d.glob('*.json') if p.name!='failure.json'}})
    hermite=BASE/'lattice-synthesis-results/source/Nathanson_1911.01745.pdf'
    deps=old['named_calibration_dependencies']+[{'path':str(hermite),'sha256':sha(hermite),'url':'https://arxiv.org/pdf/1911.01745',
        'scope':'Theorem 1: Hermite-Sylvester exact real-root certificate; independent checker uses Sturm counting',
        'imported_not_independently_reproved':True}]
    return {'schema':1,'grammar_version':g.VERSION,'seed':seed,'precision':384,
        'source_run':str(source),'source_sha256':{n:sha(source/n) for n in ['protocol.json','verification.json','summary.json','candidate_batch.json']},
        'code_sha256':dict(old['code_sha256'],**{n:sha(BASE/n) for n in CODE}),'this_stage_source_files':CODE,
        'named_calibration_dependencies':deps,'parameters':rows,'rate':'2','maximum_moment':4,
        'r_enumeration':{'numerators':[3,14],'denominators':[1,4],'upper':'7/2','pool':list(map(str,pool)),
            'selection':'seeded two distinct below 2, one integer >=2, one noninteger >2, before data',
            'selected':list(map(str,selected)),'semantic_denominator_cap':False,'r_semantics':'any rational r>1'},
        'initial_atoms':[0,1,2],'two_atom_coefficients':[-2,-1,1,2],'random_initial_per_context':5,
        'random_coefficient_numerators':[-4,4],'random_coefficient_denominators':[1,2,3,4],
        'parent_projections_per_ell':2,'learning':'two-dimensional rational least squares on anonymous raw unit response tables, leading moment-2 coefficient fixed to 1',
        'learning_denominator_resource':4096,'learning_binary_quantization_bits':80,
        'learning_has_no_analytic_pole_locations_or_residues':True,
        'promotion_slots_per_context':4,'promotion_pool':4,'promotion_lambdas':['-2','-1','-1/2','-1/3','-1/6','0','1/6','1/3','1/2','1','2','3'],
        'promotion_rule':'apply y*d/dy-lambda to a training-ranked shape; exact rational production; no estimate inferred from mutation',
        'ablation':'same initial and learned programs; replace each promotion slot by a seeded random shape',
        'training_points':[32,64,128,256],'validation_points':[384,512],
        'training_q':[2,3,6,12],'validation_new_q':[5,10,17],
        'ordinary_limits':['1/2','3/4','1'],'ordinary_margins':['1/16','1/4'],'approach_powers':['1/6','1','2'],'log_powers':['0','1/2'],
        'reference_decay_orders':['1/6','1/3','1/2','1'],'reference_ray_grammar':{'kernel_pi_fractions':['1/6','1/4','1/3'],'allocation_fractions':['1/4','1/2','3/4']},
        'constant_rule':{'training_margin':'3/2','upward_denominator':str(2**128),'minimum':str(Q(1,2**128))},
        'constants_scope':'free finite constant for every q and each bank member; no constant growth law; training-only calibration',
        'cost_query':['5/8','16'],'archive_size':24,'bank_limit':12,
        'bank_selection':'validation then best training observer for each r and ell, then exact complementary pair intersection; no nominated dilation pair',
        'selection':'validation, charged conditional observer, finite ratio; preserve fractional constraints, complementary banks, learned, real/complex, missing-bridge and weak regimes',
        'final_cases':{'count':3,'range':[1025,2048],'real_offset':'1/3','boundary':[1,2],'fresh_q_count':3,'fresh_q_range':[19,223]},
        'parent_final_scales_excluded':read(source/'final_cases.json')['integers'],'parent_final_q_excluded':read(source/'parameter_cases.json')['fresh_q'],
        'retained_failed_runs_are_development':failed,'negative_control':'attempt to apply true unit-channel certificate to actual inverse arithmetic; reject by proof input type',
        'proof_backends':['complete generalized lattice tails','weak actual density count','rotated Gamma integral and fully bounded reference contour',
            'post-rewrite sign-loss barrier including actual squarefree support','Hermite and native operator-root exclusion',
            'fractional zero chains and exact exceptional-set intersections','fully charged conditional ordinary-zeta observers'],
        'design_assumptions':['common positive rational rate','linear finite integer moments','K>1 and ell>0','r>1 generalized dilation',
            'supplied proof methods and ranking criteria','bounded numerator/denominator sampling is a resource decision'],
        'developer_preflight':'public contracts and generic independent arithmetic checks only; no nominated candidate or expected search winner',
        'generator_model_literature_network_access':False,'not_autonomous_proof_invention':True,'historical_priority_is_acceptance_gate':False,
        'new_prime_distribution_estimate_imported':False,'machine_formalized':False,'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False}


def restrict(directory):
    spec=read(directory/'protocol.json');allowed={str((BASE/n).resolve()) for n in spec['code_sha256']}
    allowed|={str((directory/n).resolve()) for n in SEALED+['seal.json','parameter_cases.json','parameter_calibration.json','calibration_seal.json']}
    def audit(event,args):
        if event=='open' and not isinstance(args[0],int) and str(Path(args[0]).resolve()) not in allowed:raise PermissionError('Discovery file denied')
        if event.startswith('socket.') or event in ('subprocess.Popen','os.system','os.posix_spawn','os.posix_spawnp'):raise PermissionError('External access denied')
    sys.addaudithook(audit);denied={}
    for label,action in [('private_final',lambda:open(directory/'final_cases.json')),('parent_outcomes',lambda:open(Path(spec['source_run'])/'final_evaluation.json')),
        ('parent_full_batch',lambda:open(Path(spec['source_run'])/'candidate_batch.json')),('literature',lambda:open(spec['named_calibration_dependencies'][-1]['path'])),
        ('network',lambda:socket.socket()),('subprocess',lambda:subprocess.run([sys.executable,'-c','pass']))]:
        try:action()
        except PermissionError:denied[label]=True
        else:raise AssertionError('Isolation probe failed')
    return denied


def tables(spec,points,rows=None):
    out={}
    for row in spec['parameters'] if rows is None else rows:
        out[pid(row)]=g.complete_table(*row,spec['rate'],points,maximum_moment=spec['maximum_moment'],min_prec=spec['precision'])
        print('Complete typed lattice',row,'pairs',out[pid(row)]['prefix_pairs'],flush=True)
    return {'tables':out,'all_infinite_tails_included':True}


def anonymous_learn(rows,points,spec):
    """Only three numeric response columns and scale weights enter this fit."""
    D=2**spec['learning_binary_quantization_bits']
    data=[[Q(round(Q(flint.arb(rows[f'{m}:{X}']).mid().str(55,radius=False))*D),D) for m in range(3)] for X in points]
    A=sum((v[0]**2/Q(X)**2 for X,v in zip(points,data)),Q(0));B=sum((v[0]*v[1]/Q(X)**2 for X,v in zip(points,data)),Q(0))
    C=sum((v[1]**2/Q(X)**2 for X,v in zip(points,data)),Q(0));U=-sum((v[0]*v[2]/Q(X)**2 for X,v in zip(points,data)),Q(0));V=-sum((v[1]*v[2]/Q(X)**2 for X,v in zip(points,data)),Q(0))
    det=A*C-B*B
    if not det:return None,{'status':'rank_deficient_anonymous_response_table'}
    raw=[(U*C-B*V)/det,(A*V-B*U)/det,Q(1)];rounded=[x.limit_denominator(spec['learning_denominator_resource']) for x in raw]
    return g.shape(list(enumerate(rounded))),{'status':'anonymous_response_least_squares','rounded_coefficients':list(map(str,rounded)),
        'unrounded_coefficients':list(map(str,raw)),'input_contains_poles_or_arithmetic_names':False}


def random_shape(rng,spec):
    moments=sorted(rng.sample(range(spec['maximum_moment']+1),rng.randint(1,4)));terms=[]
    for m in moments:
        c=Q(rng.randint(*spec['random_coefficient_numerators']),rng.choice(spec['random_coefficient_denominators']))
        if c:terms.append([m,c])
    return g.shape(terms or [[moments[0],1]],spec['rate'])


def build(c,row,family,method):
    res=g.residues(c,row);bridge=z.root_certificate(c,row);exceptions=z.exceptional_real_parts(row[2])
    return {'id':digest({'shape':c,'parameters':row}),'parameter_id':pid(row),'parameters':row,'shape':c,
        'family':family,'origins':[{'family':family,'method':method}],
        'residues':res,'zero_bridge':bridge,'zero_exceptions':exceptions,
        'weak_actual':g.weak_actual(c,row),'sign_loss_barrier':g.sign_loss_barrier(c,row,res),
        'global_constants':g.global_constants(c,row,res),
        'reference_decay_certificates':{},'actual_RH_uniform_estimate_proved':False}


def obs(p,data,points):return g.responses(p['shape'],data['tables'][p['parameter_id']],points,p['residues'])
def training_score(rows,r):return max(float((abs(flint.arb(v['inverse_centered_ball']))/power(real(X),1/Q(r))).upper()) for X,v in rows.items())


def generate(spec,forms,data):
    rng=random.Random(spec['seed']);base={};primary={};ablation={};promotions=[];learned=[];rejects=[]
    def add(store,c,row,family,method):
        key=digest({'shape':c,'parameters':row})
        p=base.get(key) or primary.get(key) or ablation.get(key)
        if p is None:p=build(c,row,family,method)
        elif {'family':family,'method':method} not in p['origins']:p['origins'].append({'family':family,'method':method})
        store[key]=p;return p
    for row in spec['parameters']:
        local=[]
        def put(c,family,method):
            p=add(base,c,row,family,method)
            if p not in local:local.append(p)
        for m in spec['initial_atoms']:put(g.shape([[m,1]],spec['rate']),'baseline_atom','frozen moment grammar')
        for m,n in combinations(spec['initial_atoms'],2):
            for c in spec['two_atom_coefficients']:put(g.shape([[m,c],[n,1]],spec['rate']),'baseline_two_atoms','frozen coefficient grid')
        projections=[]
        for f in forms['forms']:
            if Q(f['parameters'][1])!=Q(row[1]):continue
            groups=defaultdict(list)
            for m,j,c in f['terms']:groups[j].append([m,c])
            projections += [g.shape(v,spec['rate']) for v in groups.values()]
        unique={digest(c):c for c in projections}
        for c in sorted(unique.values(),key=lambda c:(len(c['terms']),c['maximum_moment'],digest(c)))[:spec['parent_projections_per_ell']]:put(c,'source_projection','single-rate source projection; retune rate to 2')
        for _ in range(spec['random_initial_per_context']):put(random_shape(rng,spec),'baseline_random','frozen seeded rational grammar')
        c,record=anonymous_learn(data['tables'][pid(row)]['values']['unit'],spec['training_points'],spec)
        if c is not None:put(c,'learned_anonymous_unit','anonymous raw unit responses only')
        learned.append(dict(record,parameter_id=pid(row),shape=c))
        pool=sorted(local,key=lambda p:(training_score(obs(p,data,spec['training_points']),row[2]),p['id']))[:spec['promotion_pool']]
        for slot in range(spec['promotion_slots_per_context']):
            parent=rng.choice(pool);lam=Q(rng.choice(spec['promotion_lambdas']));terms=defaultdict(Q)
            for m,a in parent['shape']['terms']:terms[m]+=(m-lam)*Q(a);terms[m+1]-=Q(a)
            c=g.shape([[m,a] for m,a in terms.items()],spec['rate']);admitted=c['maximum_moment']<=spec['maximum_moment']
            record={'parameter_id':pid(row),'slot':slot,'parent_id':parent['id'],'lambda':str(lam),'shape':c,'admitted':admitted}
            promotions.append(record)
            if admitted:add(primary,c,row,'promoted_Euler_derivative',f'y*d/dy-{lam}')
            else:rejects.append(dict(record,reason='moment resource cap, not a mathematical rejection'))
            add(ablation,random_shape(rng,spec),row,'ablation_random_slot','equal proposal slot budget')
    primary=dict(base,**primary);ablation=dict(base,**ablation)
    allps={**primary,**ablation}
    for p in allps.values():
        p['reference_decay_certificates']={a:g.reference_decay(p['shape'],p['parameters'],a) for a in spec['reference_decay_orders']}
    return list(primary.values()),list(ablation.values()),learned,promotions,rejects


def fit(rows,f,qs,spec):
    flint.ctx.prec=512;D=int(spec['constant_rule']['upward_denominator']);margin=real(spec['constant_rule']['training_margin']);out={}
    for q in qs:
        value=max((abs(flint.arb(v['inverse_centered_ball']))/g.env(f,q,X) for X,v in rows.items()),key=lambda a:float(a.upper()))
        out[str(q)]=str(max(Q(spec['constant_rule']['minimum']),Q(ceil(Q((margin*value).upper().str(70,radius=False))*D),D)))
    return out


def compare(rows,f,Cs,qs):
    failures=[];unresolved=[];worst=(0,None)
    for q in qs:
        for X,v in rows.items():
            V=abs(flint.arb(v['inverse_centered_ball']));B=real(Cs[str(q)])*g.env(f,q,X);label=f'{q}:{X}'
            if not V<=B:(failures if V>B else unresolved).append(label)
            ratio=float((V/B).upper())
            if ratio>worst[0]:worst=(ratio,label)
    return {'finite_points_passed':not failures and not unresolved,'failures':failures,'unresolved':unresolved,
        'maximum_ratio':worst[0],'maximum_ratio_case':worst[1],'point_comparisons':len(qs)*len(rows),'uniform_signed_premise_proved':False}


def hypotheses(p,rows,spec):
    out=[];qs=spec['training_q']+spec['validation_new_q']
    for eta,margin,nu,d in product(spec['ordinary_limits'],spec['ordinary_margins'],spec['approach_powers'],spec['log_powers']):
        f=g.frontier(p['parameters'][2],eta,margin,nu,d);Cs=fit(rows,f,qs,spec)
        critical=Q(eta)==Q(1,2);safe=p['zero_bridge']['all_right_half_ordinary_zeros_preserved'] and p['zero_exceptions']['complete']
        core={'program_id':p['id'],'frontier':f,'illustrative_constants_by_q':Cs}
        cost=g.charge(p,f,Cs,spec['training_q'],spec['cost_query']) if critical else {'best_log_cost':None,'status':'above_critical_ordinary_limit','observers':[]}
        out.append(dict(core,id=digest(core),critical_zero_constraint_if_uniform=critical and safe,
            RH_sufficient_if_uniform=critical and safe and not p['zero_exceptions']['real_parts'],
            recovery_cost=cost,certificate_attempt=g.attempt(p,f)))
    return out


def rank(c):return (not c['validation']['finite_points_passed'],c['recovery_cost']['best_log_cost'] if c['recovery_cost'].get('best_log_cost') is not None else 1e100,c['validation']['maximum_ratio'],c['id'])


def assemble_banks(candidates,programs,spec):
    ps={p['id']:p for p in programs};leads={}
    for c in candidates:
        if not c['critical_zero_constraint_if_uniform']:continue
        p=ps[c['program_id']];key=(p['parameters'][1],p['parameters'][2])
        if key not in leads or rank(c)<rank(leads[key]):leads[key]=c
    banks=[]
    for c,d in combinations(leads.values(),2):
        p,t=ps[c['program_id']],ps[d['program_id']]
        if p['parameters'][1]!=t['parameters'][1] or Q(p['parameters'][2])>=2 or Q(t['parameters'][2])>=2:continue
        certificate=z.complementary_certificate([p,t])
        if not certificate['RH_sufficient_if_every_member_uniform']:continue
        costs=[v['recovery_cost']['best_log_cost'] for v in [c,d]]
        log_cost=max(costs)+__import__('math').log(sum(__import__('math').exp(x-max(costs)) for x in costs)) if all(x is not None for x in costs) else None
        banks.append({'id':digest({'member_candidate_ids':sorted([c['id'],d['id']])}),'member_candidate_ids':[c['id'],d['id']],
            'certificate':certificate,'validation_finite_points_passed':all(v['validation']['finite_points_passed'] for v in [c,d]),
            'joint_log_cost':log_cost,'every_member_observer_charged':True,'uniform_signed_premises_proved':False})
    return sorted(banks,key=lambda b:(not b['validation_finite_points_passed'],b['joint_log_cost'] if b['joint_log_cost'] is not None else 1e100,b['id']))[:spec['bank_limit']]


def select(candidates,programs,banks,spec):
    ps={p['id']:p for p in programs};by={c['id']:c for c in candidates};out=[]
    def include(pool):
        if pool:
            c=min(pool,key=rank)
            if c not in out and len(out)<spec['archive_size']:out.append(c)
    for b in banks[:3]:
        for i in b['member_candidate_ids']:include([by[i]])
    for family in ['learned_anonymous_unit','promoted_Euler_derivative']:
        include([c for c in candidates if any(o['family']==family for o in ps[c['program_id']]['origins']) and c['critical_zero_constraint_if_uniform']])
    include([c for c in candidates if not ps[c['program_id']]['zero_bridge']['all_right_half_ordinary_zeros_preserved']])
    include([c for c in candidates if ps[c['program_id']]['zero_bridge']['kind']=='certified_finite_operator_root_exclusion'])
    include([c for c in candidates if Q(c['frontier']['ordinary_limit'])==1])
    for ell in sorted({row[1] for row in spec['parameters']},key=Q):include([c for c in candidates if c['RH_sufficient_if_uniform'] and ps[c['program_id']]['parameters'][1]==ell])
    for family in ['learned_anonymous_unit','promoted_Euler_derivative']:
        for ell in sorted({row[1] for row in spec['parameters']},key=Q):include([c for c in candidates if ps[c['program_id']]['parameters'][1]==ell and any(o['family']==family for o in ps[c['program_id']]['origins']) and c['critical_zero_constraint_if_uniform']])
    for c in sorted(candidates,key=rank):
        if len(out)>=spec['archive_size']:break
        if c not in out:out.append(c)
    return out


def worker(directory):
    spec=read(directory/'protocol.json');verify_code(spec);denied=restrict(directory)
    data=tables(spec,spec['training_points']);write(directory/'discovery_data.json',dict(data,worker_access_denials=denied))
    ps,aps,learned,promotions,rejects=generate(spec,read(directory/'source_forms.json'),data)
    allps={p['id']:p for p in aps+ps};observations={i:obs(p,data,spec['training_points']) for i,p in allps.items()};cs=[]
    for p in allps.values():cs+=hypotheses(p,observations[p['id']],spec)
    write(directory/'candidate_batch.json',{'protocol_sha256':digest(spec),'programs':ps,'ablation_programs':aps,'training_observables':observations,
        'candidates':cs,'learned_response_records':learned,'promotions':promotions,'rejected_proposals':rejects,
        'frozen_before_validation':True,'generation_uses_training_only':True})
    print('Frozen programs',len(ps),'hypotheses',len(cs),flush=True)
    vd=tables(spec,spec['validation_points']);vobs={i:obs(p,vd,spec['validation_points']) for i,p in allps.items()}
    validated=[dict(c,validation=compare(vobs[c['program_id']],c['frontier'],c['illustrative_constants_by_q'],spec['training_q']+spec['validation_new_q'])) for c in cs]
    write(directory/'validation_data.json',dict(vd,candidate_batch_sha256=sha(directory/'candidate_batch.json'),program_observables=vobs,candidates=validated))
    ids={p['id'] for p in ps};aids={p['id'] for p in aps};primary=[c for c in validated if c['program_id'] in ids];ablation=[c for c in validated if c['program_id'] in aids]
    banks=assemble_banks(primary,ps,spec);abanks=assemble_banks(ablation,aps,spec);archive=select(primary,ps,banks,spec);aarchive=select(ablation,aps,abanks,spec)
    def best(rows):return min((c['recovery_cost']['best_log_cost'] for c in rows if c['recovery_cost'].get('best_log_cost') is not None),default=None)
    references=sorted(ps,key=lambda p:(not p['residues']['both_reference_residues_vanish'],
        not any(o['family']=='learned_anonymous_unit' for o in p['origins']),p['reference_decay_certificates']['1']['best_ray']['log_constant'],p['id']))[:6]
    write(directory/'archive.json',{'archive':archive,'ablation_archive':aarchive,'banks':banks,'ablation_banks':abanks,'reference_program_ids':[p['id'] for p in references],
        'selection_closed':True,'final_data_used':False,'negative_controls':[{'program_id':p['id'],'certificate_order':'1','expected_rejection':'arithmetic_input_type_mismatch'} for p in references],
        'ablation_comparison':{'equal_promotion_slot_budgets':True,'proposal_slots':spec['promotion_slots_per_context']*len(spec['parameters']),
            'admitted_promotions':sum(p['admitted'] for p in promotions),'primary_programs':len(ps),'ablation_programs':len(aps),
            'best_primary_log_cost':best(archive),'best_ablation_log_cost':best(aarchive)}})
    write(directory/'seal.json',{'protocol_sha256':digest(spec),'files':{n:sha(directory/n) for n in SEALED},'selection_closed':True,'final_cases_exist_at_seal':False,'parameter_cases_exist_at_seal':False})
    print('Sealed candidates',len(archive),'complementary banks',len(banks),flush=True)


def parameter_cases(directory):
    spec=read(directory/'protocol.json');rule=spec['final_cases'];rng=random.Random(int.from_bytes(os.urandom(32),'big'))
    excluded=set(spec['training_q']+spec['validation_new_q']+spec['parent_final_q_excluded'])|{q for r in spec['retained_failed_runs_are_development'] for q in r['excluded_final_q']}
    qs=sorted(rng.sample([q for q in range(rule['fresh_q_range'][0],rule['fresh_q_range'][1]+1) if q not in excluded],rule['fresh_q_count']))
    write(directory/'parameter_cases.json',{'fresh_q':qs,'seal_sha256':sha(directory/'seal.json'),'generated_after_archive_seal':True,'no_final_scale_information_present':True})


def calibrate(directory):
    spec=read(directory/'protocol.json');verify_code(spec);denied=restrict(directory);pc=read(directory/'parameter_cases.json');batch=read(directory/'candidate_batch.json');arc=read(directory/'archive.json')
    by={c['id']:c for c in batch['candidates']};ids={c['id'] for c in arc['archive']}|{i for b in arc['banks'] for i in b['member_candidate_ids']};out=[]
    for i in sorted(ids):
        c=by[i];Cs=fit(batch['training_observables'][c['program_id']],c['frontier'],pc['fresh_q'],spec);out.append({'candidate_id':i,'constants':Cs})
    write(directory/'parameter_calibration.json',{'parameters_sha256':digest(pc),'training_only':True,'final_scales_used':False,'worker_access_denials':denied,'illustrative_free_constants':out})
    write(directory/'calibration_seal.json',{'archive_seal_sha256':sha(directory/'seal.json'),'parameter_cases_sha256':sha(directory/'parameter_cases.json'),
        'parameter_calibration_sha256':sha(directory/'parameter_calibration.json'),'final_cases_exist_at_calibration_seal':False})


def final(directory):
    spec=read(directory/'protocol.json');verify_code(spec);seal=read(directory/'seal.json');cal=read(directory/'calibration_seal.json')
    for n,h in seal['files'].items():assert sha(directory/n)==h
    for key,n in [('archive_seal_sha256','seal.json'),('parameter_cases_sha256','parameter_cases.json'),('parameter_calibration_sha256','parameter_calibration.json')]:assert cal[key]==sha(directory/n)
    rule=spec['final_cases'];rng=random.Random(int.from_bytes(os.urandom(32),'big'));excluded=set(spec['parent_final_scales_excluded'])|{x for r in spec['retained_failed_runs_are_development'] for x in r['excluded_final_scales']}
    integers=sorted(rng.sample([x for x in range(rule['range'][0],rule['range'][1]+1) if x not in excluded],rule['count']));points=list(map(str,rule['boundary']+integers))+[str(Q(x)+Q(rule['real_offset'])) for x in integers]
    cases={'integers':integers,'points':points,'calibration_seal_sha256':digest(cal),'generated_after_calibration_seal':True};write(directory/'final_cases.json',cases)
    batch=read(directory/'candidate_batch.json');arc=read(directory/'archive.json');by={c['id']:c for c in batch['candidates']};ps={p['id']:p for p in batch['programs']}
    ids={c['id'] for c in arc['archive']}|{i for b in arc['banks'] for i in b['member_candidate_ids']};pids={by[i]['program_id'] for i in ids}|set(arc['reference_program_ids'])
    rows=[row for row in spec['parameters'] if any(ps[i]['parameters']==row for i in pids)];data=tables(spec,points,rows);fobs={i:obs(ps[i],data,points) for i in sorted(pids)}
    fresh=read(directory/'parameter_cases.json')['fresh_q'];calibrated={r['candidate_id']:r['constants'] for r in read(directory/'parameter_calibration.json')['illustrative_free_constants']};out=[]
    for i in sorted(ids):
        c=by[i];Cs={**c['illustrative_constants_by_q'],**calibrated[i]};qs=spec['training_q']+spec['validation_new_q']+fresh
        out.append(dict(compare(fobs[c['program_id']],c['frontier'],Cs,qs),candidate_id=i,constants=Cs,
            recovery_cost=g.charge(ps[c['program_id']],c['frontier'],Cs,qs,spec['cost_query']) if Q(c['frontier']['ordinary_limit'])==Q(1,2) else {'status':'above_critical_ordinary_limit','best_log_cost':None,'observers':[]}))
    outcomes={o['candidate_id']:o for o in out};bank_out=[]
    for b in arc['banks']:bank_out.append({'bank_id':b['id'],'finite_points_passed':all(outcomes[i]['finite_points_passed'] for i in b['member_candidate_ids']),
        'uniform_signed_premises_proved':False,'every_member_tested':True})
    references=[];controls=[]
    for i in arc['reference_program_ids']:
        p=ps[i]
        for order,cert in p['reference_decay_certificates'].items():
            ratios=[]
            for X,row in fobs[i].items():
                V=abs(flint.arb(row['unit_two_residue_residual_ball']));B=flint.arb(cert['constant_ball'])*power(real(X),-Q(order));assert V<=B
                ratios.append(float((V/B).upper()))
            references.append({'program_id':i,'order':order,'all_fresh_points_enclosed':True,'maximum_ratio':max(ratios),
                'global_premise_proved':True,'arithmetic_model':'unit','actual_inverse_estimate_proved':False})
        try:g.enforce_certificate_arithmetic(p['reference_decay_certificates']['1'],'inverse')
        except ValueError:controls.append({'program_id':i,'typed_alias_rejected':True,'reference_bound_itself_is_true':True,'actual_growth_counterexample_claimed':False})
        else:raise AssertionError('Arithmetic alias accepted')
    write(directory/'final_evaluation.json',{'protocol_sha256':digest(spec),'seal_sha256':digest(seal),'cases_sha256':digest(cases),'calibration_seal_sha256':digest(cal),
        'data':data,'program_observables':fobs,'outcomes':out,'bank_outcomes':bank_out,'reference_bound_outcomes':references,'negative_controls':controls,
        'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False})


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('mode',choices=['run','worker','calibrate','final'],nargs='?',default='run');parser.add_argument('--run-dir',type=Path,required=True);parser.add_argument('--source',type=Path);args=parser.parse_args();d=args.run_dir.resolve()
    if args.mode=='worker':worker(d);return
    if args.mode=='calibrate':calibrate(d);return
    if args.mode=='final':final(d);return
    if args.source is None:raise ValueError('Verified signed Gram source required')
    d.mkdir(parents=True,exist_ok=False);spec=protocol(args.source);write(d/'protocol.json',spec);write(d/'source_forms.json',source_forms(args.source));(d/'frozen_source').mkdir()
    for n in CODE:(d/'frozen_source'/n).write_bytes((BASE/n).read_bytes())
    try:
        subprocess.run([sys.executable,str(BASE/'lattice_synthesis_search.py'),'worker','--run-dir',str(d)],check=True,cwd=BASE);parameter_cases(d)
        subprocess.run([sys.executable,str(BASE/'lattice_synthesis_search.py'),'calibrate','--run-dir',str(d)],check=True,cwd=BASE);final(d)
        subprocess.run([sys.executable,str(BASE/'check_lattice_synthesis.py'),'--run-dir',str(d)],check=True,cwd=BASE)
        from lattice_synthesis_report import summary,text_report
        s=summary(d);write(d/'summary.json',s);(d/'report.txt').write_text(text_report(s));write(BASE/'lattice-synthesis-results/latest.json',{'run_directory':str(d)})
    except Exception as exc:write(d/'failure.json',{'error_type':type(exc).__name__,'error':str(exc),'original_data_and_outcomes_retained':True});raise


if __name__=='__main__':main()
