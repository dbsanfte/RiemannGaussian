#!/usr/bin/env python3
"""Frozen signed-kernel search, free cofinal constants, complete inverse tails."""
import argparse
from fractions import Fraction as Q
from itertools import combinations, product as cartesian
from math import ceil
from pathlib import Path
import os, random, socket, subprocess, sys
import flint
from estimate_grammar import inverse_one_prefix
from stable_scale_search import BASE,read,write,sha,digest,verify_code
from mellin_kernel_grammar import (VERSION,real,power,serialize,canonical,poly,encode,plus,
    linear_solve,bank_certificate,frontier,theta,envelope,primitive_table,response,
    global_certificate,charged_cost,certificate_attempt)

CODE=['mellin_kernel_grammar.py','mellin_kernel_search.py','check_mellin_kernels.py',
      'mellin_kernel_report.py','mellin_kernel_proof.txt']
SEALED=['protocol.json','discovery_data.json','candidate_batch.json','validation_data.json','archive.json']


def protocol(source):
    from mertens_limit_report import summary
    source=Path(source).resolve();summary(source);old=read(source/'protocol.json')
    failed=[]
    for f in sorted((BASE/'mellin-kernel-results').glob('*/failure.json')):
        d=f.parent;cases=read(d/'final_cases.json') if (d/'final_cases.json').exists() else {}
        failed.append({'run_directory':str(d),'failure_sha256':sha(f),
            'excluded_final_scales':cases.get('integers',[]),
            'excluded_final_q':read(d/'parameter_cases.json').get('fresh_q',[]) if (d/'parameter_cases.json').exists() else [],
            'original_code_sha256':read(d/'protocol.json')['code_sha256'],
            'retained_files_sha256':{p.name:sha(p) for p in d.glob('*.json') if p.name!='failure.json'}})
    dependencies=[{'path':str(BASE/'mellin-kernel-results/source'/name),'sha256':sha(BASE/'mellin-kernel-results/source'/name),
        'url':url,'scope':scope,'imported_not_independently_reproved':True} for name,url,scope in [
        ('TitchmarshZeta.pdf','https://sites.math.rutgers.edu/~zeilberg/EM18/TitchmarshZeta.pdf',
         'Theorem 14.25(C), printed p.370: RH iff M(x)=O_epsilon(x^(1/2+epsilon)); converse calibration only'),
        ('AgarwalGargMaji_2202.00637.pdf','https://arxiv.org/pdf/2202.00637',
         'Theorem 1.2: Riesz-type criterion; separate known-operator calibration only')]]
    parameters=[['3/2','1/3','2'],['3/2','1/2','3/2'],['3/2','1','2'],['3/2','2','3/2'],
                ['2','1/3','3/2'],['2','1/2','2'],['2','1','3/2'],['2','2','2'],['2','3','2'],['2','6','2']]
    return {'schema':1,'grammar_version':VERSION,'seed':2026100837,'precision':384,
        'source_run':str(source),'source_sha256':{n:sha(source/n) for n in ['protocol.json','verification.json','summary.json']},
        'code_sha256':dict(old['code_sha256'],**{n:sha(BASE/n) for n in CODE}),
        'this_stage_source_files':CODE,'named_calibration_dependencies':dependencies,
        'parameters':parameters,'maximum_moment':2,'maximum_dilation':2,
        'enum_two_atom_coefficients':['-1','1'],'random_proposals_per_parameter':16,
        'moment_nullspaces_per_parameter':4,'least_squares_per_parameter':4,
        'coefficient_resource_cap':16,'coefficient_rounding_denominator':64,
        'promotion_slots_per_parameter':8,'promotion_pool':6,
        'promotion_rule':'sample training-energy pool; apply a rational signed dilation or Euler derivative; resource checks then canonicalize',
        'ablation':'same base and learning proposals, replace eight promotion proposal slots by seeded random kernels',
        'bank_pairs_per_parameter':10,'bank_pool':8,
        'bank_rule':'single kernels plus seeded pairs from low normalized training-response energy; exact bounded Bezout search without target labels',
        'certificate_multiplier_degree':1,'certificate_target_rising_order':2,
        'training_points':[1,2,4,8,16,32,64,128],
        'validation_points':[193,256,384],'training_q':[2,3,6,12],'validation_new_q':[5,10,17],
        'frontier_limits':['1/2','3/4','1'],'frontier_margins':['1/4'],
        'frontier_approach_powers':['1/6','1/2','1','2'],'frontier_log_powers':['0','1'],
        'constant_rule':{'training_margin':'3/2','upward_denominator':str(2**128),'minimum':str(Q(1,2**128))},
        'constants_scope':'independent C_(kernel,q); no bounded/polynomial growth law in q; fit only training scales',
        'prefix_rule':'N=max(256,2*ceil(max(points))); every coefficient through N, all n>N included using reciprocal-zeta moments',
        'cost_query':['5/8','16'],'archive_size':16,
        'selection':'best charged recovery cost across RH-if-uniform construction and root regimes; preserve uncertified and above-threshold leads; fill by validation and cost',
        'final_cases':{'count':3,'range':[513,1024],'real_offset':'1/3','boundary':[1,2],
            'fresh_q_count':3,'fresh_q_range':[19,211],'generic_count':4,'generic_cutoff':24},
        'final_freshness_scope':'new operators and randomly drawn scales/parameters; finite inverse coefficients overlap earlier research',
        'retained_failed_runs_are_development':failed,
        'counterfeit_tail_cutoff':str(2**200),
        'supplied_backends':['complete reciprocal-zeta tail','bivariate exact Mellin identity',
            'rational Bezout and disk dominance','cofinal free-constant continuation','unimodal weak bound and unit derivative'],
        'developer_preflight':'training-sized scalar enclosures, one parameter training generator/bank assembly, and primitive cost plumbing; no validation, final cases or selected archive observed',
        'generator_model_literature_network_access':False,'not_autonomous_proof_invention':True,
        'new_prime_distribution_estimate_imported':False,'historical_priority_is_acceptance_gate':False,
        'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False}


def restrict(directory,calibration=False):
    spec=read(directory/'protocol.json')
    allowed={str((BASE/n).resolve()) for n in spec['code_sha256']}
    names=SEALED+['seal.json','parameter_cases.json','parameter_calibration.json','calibration_seal.json']
    allowed|={str((directory/n).resolve()) for n in names}
    def audit(event,args):
        if event=='open' and not isinstance(args[0],int) and str(Path(args[0]).resolve()) not in allowed:
            raise PermissionError('Discovery/calibration file access denied')
        if event.startswith('socket.') or event in ('subprocess.Popen','os.system','os.posix_spawn','os.posix_spawnp'):
            raise PermissionError('External access denied')
    sys.addaudithook(audit);denied={}
    for label,action in [('private_final',lambda:open(directory/'final_cases.json')),
        ('literature',lambda:open(spec['named_calibration_dependencies'][0]['path'])),
        ('network',lambda:socket.socket()),('subprocess',lambda:subprocess.run([sys.executable,'-c','pass']))]:
        try:action()
        except PermissionError:denied[label]=True
        else:raise AssertionError('Isolation probe failed')
    return denied


def parameter_id(row):return digest({'k':row[0],'ell':row[1],'base':row[2]})


def make_tables(spec,points,parameters=None):
    rows=spec['parameters'] if parameters is None else parameters
    N=max(256,2*ceil(max(map(Q,points))));mu=inverse_one_prefix(N);data={}
    for row in rows:
        data[parameter_id(row)]=primitive_table(mu,*map(Q,row),points,
            spec['maximum_moment'],spec['maximum_dilation'],spec['precision'])
        print('Complete tail',row,'cutoff',N,'precision',data[parameter_id(row)]['resources']['precision'],flush=True)
    flint.ctx.prec=spec['precision']
    return {'cutoff':N,'inverse_coefficient_sha256':digest(mu),'tables':data,'all_infinite_tails_included':True}


def energy(kernel,table,points):
    vals=response(kernel,table,points)
    return sum(float(flint.arb(v).mid())**2/float(Q(x)) for x,v in vals.items())


def random_kernel(rng,spec):
    atoms=[(m,j) for m in range(spec['maximum_moment']+1) for j in range(spec['maximum_dilation']+1)]
    support=rng.sample(atoms,rng.randint(2,5))
    return [[m,j,str(Q(rng.randint(-8,8),4))] for m,j in support]


def generate(spec,table,row):
    pid=parameter_id(row);rng=random.Random(spec['seed']+int(pid[:12],16));atoms=[(m,j)
        for m in range(spec['maximum_moment']+1) for j in range(spec['maximum_dilation']+1)]
    proposals=[('primitive',[[m,j,1]],'anonymous atom') for m,j in atoms]
    for (m,j),(r,h) in combinations(atoms,2):
        for c in spec['enum_two_atom_coefficients']:
            proposals.append(('signed_two_atom',[[m,j,1],[r,h,c]],'cost bounded two-atom enumeration'))
    for _ in range(spec['random_proposals_per_parameter']):
        proposals.append(('signed_rational',random_kernel(rng,spec),'seeded sparse signed coefficients'))
    for trial in range(spec['moment_nullspaces_per_parameter']):
        support=rng.sample(atoms,5);order=1+trial%3
        def coefficient(atom,p):
            m,j=atom
            return Q(0) if p<m else Q(row[2])**(j*p)*Q((-1)**(p-m),__import__('math').factorial(p-m))
        columns=[{(p,0):coefficient(atom,p) for p in range(order)} for atom in support[1:]]
        target={(p,0):-coefficient(support[0],p) for p in range(order)}
        tail=linear_solve(columns,target)
        if tail is not None:proposals.append(('small_argument_nullspace',[[m,j,str(c)] for (m,j),c in zip(support,[Q(1)]+tail)],
            'exact nullspace of consecutive Taylor moments; support sampled without a nominated stencil'))
    for trial in range(spec['least_squares_per_parameter']):
        support=[(0,0)]+rng.sample(atoms[1:],3+trial%2);points=spec['training_points'][2:]
        R=[[Q(round(float(flint.arb(table['values'][f'{m}:{j}:{x}']).mid())*2**60),2**60)
            for m,j in support] for x in points]
        gram=[{(r,0):sum((values[a]*values[r+1]/x for values,x in zip(R,points)),Q(0))
               for r in range(len(support)-1)} for a in range(1,len(support))]
        rhs={(r,0):-sum((values[0]*values[r+1]/x for values,x in zip(R,points)),Q(0)) for r in range(len(support)-1)}
        fitted=linear_solve(gram,rhs)
        if fitted is not None:
            unit=spec['coefficient_rounding_denominator'];cs=[Q(1)]+[Q(round(c*unit),unit) for c in fitted]
            proposals.append(('learned_response',[[m,j,str(c)] for (m,j),c in zip(support,cs)],
                'exact least squares on quantized anonymous training responses'))
    baseline=[];rejected=[];seen=set()
    def admit(family,terms,method,output):
        try:K=canonical(terms)
        except ValueError:rejected.append({'family':family,'reason':'zero or invalid kernel','terms':terms});return
        if K['maximum_moment']>spec['maximum_moment'] or K['maximum_dilation']>spec['maximum_dilation'] or max(abs(Q(c)) for m,j,c in K['terms'])>spec['coefficient_resource_cap']:
            rejected.append({'family':family,'reason':'declared resource cap','kernel':K});return
        kid=digest({'parameters':row,'kernel':K})
        if kid in seen:rejected.append({'family':family,'reason':'duplicate normalized kernel','kernel':K});return
        seen.add(kid);output.append({'id':kid,'parameter_id':pid,'parameters':row,'kernel':K,'family':family,'method':method})
    for p in proposals:admit(*p,baseline)
    pool=sorted(baseline,key=lambda p:(energy(p['kernel'],table,spec['training_points']),p['id']))[:spec['promotion_pool']]
    primary=baseline.copy();ablation=baseline.copy();base_seen=seen.copy();promotions=[]
    for _ in range(spec['promotion_slots_per_parameter']):
        parent=rng.choice(pool);terms=[];mode=rng.choice(['dilation','Euler_derivative'])
        multiplier=rng.choice([Q(-1),Q(-1,2),Q(1,2),Q(1)])
        for m,j,c in parent['kernel']['terms']:
            if mode=='dilation':terms.extend([[m,j,c],[m,j+1,str(Q(c)*multiplier)]])
            else:terms.extend([[m,j,str(m*Q(c))],[m+1,j,str(-Q(c))]])
        before=len(primary);method={'parent':parent['id'],'production':mode,'dilation_multiplier':str(multiplier) if mode=='dilation' else None}
        admit('promoted_'+mode,terms,method,primary)
        promotions.append(dict(method,terms=terms,admitted=len(primary)>before))
    seen=base_seen;arng=random.Random(spec['seed']+int(pid[:12],16)+901)
    for _ in range(spec['promotion_slots_per_parameter']):admit('ablation_random_slot',random_kernel(arng,spec),'promotion-disabled proposal slot',ablation)
    return primary,ablation,rejected,promotions


def assemble_banks(programs,spec,data):
    byid={p['id']:p for p in programs};banks=[]
    for row in spec['parameters']:
        pid=parameter_id(row);ps=[p for p in programs if p['parameter_id']==pid]
        pool=sorted(ps,key=lambda p:(energy(p['kernel'],data[pid],spec['training_points']),p['id']))[:spec['bank_pool']]
        rng=random.Random(spec['seed']+int(pid[:12],16)+117)
        pairs=list(combinations(pool,2));rng.shuffle(pairs)
        groups=[[p] for p in ps]+[list(pair) for pair in pairs[:spec['bank_pairs_per_parameter']]]
        for group in groups:
            ids=sorted(p['id'] for p in group);Ks=[byid[i]['kernel'] for i in ids]
            cert=bank_certificate(Ks,spec['certificate_multiplier_degree'],spec['certificate_target_rising_order'])
            banks.append({'id':digest({'members':ids}),'member_ids':ids,'parameter_id':pid,'parameters':row,
                'family':'joint_bank' if len(group)>1 else group[0]['family'],'recovery_certificate':cert,
                'contains_individually_uncertified_member':any(not bank_certificate([K])['all_height_no_common_zero'] for K in Ks)})
    return banks


def fitted_constants(values,f,qs,spec):
    rule=spec['constant_rule'];D=int(rule['upward_denominator']);out={}
    for q in qs:
        maximum=max((abs(flint.arb(v))/envelope(f,q,Q(X))).upper() for X,v in values.items())
        out[str(q)]=str(Q(max(1,int((maximum*real(rule['training_margin'])*D).ceil().fmpz())),D))
    return out


def compare(values,f,constants,qs):
    failures=[];unresolved=[];worst=(0,None)
    for i,rows in enumerate(values):
        for q in qs:
            for X,txt in rows.items():
                B=real(constants[i][str(q)])*envelope(f,q,Q(X));v=abs(flint.arb(txt));key=f'{i}:{q}:{X}'
                if not v<=B:(failures if v>B else unresolved).append(key)
                ratio=float((v/B).upper())
                if ratio>worst[0]:worst=(ratio,key)
    return {'failures':failures,'unresolved':unresolved,'maximum_ratio':worst[0],'maximum_ratio_case':worst[1],
            'finite_points_passed':not failures and not unresolved,'uniform_signed_premise_proved':False,
            'point_comparisons':sum(len(v) for v in values)*len(qs)}


def estimates(bank,ps,train,spec,gcs):
    ids=bank['member_ids'];Ks=[ps[i]['kernel'] for i in ids];rows=[train[i] for i in ids];qs=spec['training_q']+spec['validation_new_q'];out=[]
    for eta,margin,nu,ell in cartesian(spec['frontier_limits'],spec['frontier_margins'],spec['frontier_approach_powers'],spec['frontier_log_powers']):
        f=frontier(eta,margin,nu,ell);Cs=[fitted_constants(v,f,qs,spec) for v in rows]
        cert=bank['recovery_certificate'];eligible=f['RH_sufficient_if_uniform_and_bank_recovers'] and cert['all_height_no_common_zero']
        cost=charged_cost(Ks,cert,*map(Q,bank['parameters']),f,Cs,spec['training_q'],[gcs[i] for i in ids],spec['cost_query']) if Q(eta)<=Q(1,2) else {'status':'above_RH_limiting_exponent','best_log_cost':None,'observers':[]}
        core={'bank_id':bank['id'],'frontier':f,'illustrative_constants_by_member_and_q':Cs}
        out.append(dict(core,id=digest(core),RH_sufficient_if_uniform=eligible,recovery_cost=cost,
            certificate_attempt=certificate_attempt(f,Ks,[gcs[i] for i in ids])))
    return out


def select(banks,candidates,spec,ps):
    bs={b['id']:b for b in banks};chosen=[]
    def key(c):return (not c['validation']['finite_points_passed'],
        c['recovery_cost']['best_log_cost'] if c['recovery_cost'].get('best_log_cost') is not None else 1e100,
        c['validation']['maximum_ratio'],c['id'])
    def include(pool):
        if pool:
            c=min(pool,key=key)
            if c not in chosen:chosen.append(c)
    rh=[c for c in candidates if c['RH_sufficient_if_uniform']]
    for ell in sorted({row[1] for row in spec['parameters']},key=Q):include([c for c in rh if bs[c['bank_id']]['parameters'][1]==ell])
    for nu in spec['frontier_approach_powers']:include([c for c in rh if c['frontier']['approach_power']==nu])
    include([c for c in rh if bs[c['bank_id']]['family']=='joint_bank' and bs[c['bank_id']]['contains_individually_uncertified_member']])
    include([c for c in rh if bs[c['bank_id']]['family'].startswith('promoted_')])
    include([c for c in candidates if not bs[c['bank_id']]['recovery_certificate']['all_height_no_common_zero']])
    include([c for c in candidates if Q(c['frontier']['limit'])==Q(3,4)])
    include([c for c in candidates if Q(c['frontier']['limit'])==1])
    for c in sorted(rh,key=key):
        if len(chosen)>=spec['archive_size']:break
        if c not in chosen:chosen.append(c)
    return chosen[:spec['archive_size']]


def worker(directory):
    spec=read(directory/'protocol.json');verify_code(spec);denials=restrict(directory);flint.ctx.prec=spec['precision']
    discovery=make_tables(spec,spec['training_points']);write(directory/'discovery_data.json',dict(discovery,worker_access_denials=denials))
    programs=[];ablation=[];rejections=[];promotions=[]
    for row in spec['parameters']:
        p,a,r,m=generate(spec,discovery['tables'][parameter_id(row)],row);programs+=p;ablation+=a
        rejections.extend(dict(v,parameters=row) for v in r);promotions.extend(dict(v,parameters=row) for v in m)
    allps={p['id']:p for p in ablation+programs};gcs={i:global_certificate(p['kernel'],*map(Q,p['parameters']),spec['precision']) for i,p in allps.items()}
    train={i:response(p['kernel'],discovery['tables'][p['parameter_id']],spec['training_points']) for i,p in allps.items()}
    banks=assemble_banks(programs,spec,discovery['tables']);abanks=assemble_banks(ablation,spec,discovery['tables'])
    allbs={b['id']:b for b in abanks+banks};candidates=[]
    for b in allbs.values():candidates+=estimates(b,allps,train,spec,gcs)
    batch={'protocol_sha256':digest(spec),'programs':programs,'ablation_programs':ablation,'banks':banks,'ablation_banks':abanks,
        'global_certificates':gcs,'training_responses':train,'candidates':candidates,'rejected_proposals':rejections,
        'promotions':promotions,'frozen_before_validation':True,'generation_uses_training_only':True}
    write(directory/'candidate_batch.json',batch);print('Frozen candidates',len(programs),len(banks),len(candidates),flush=True)
    vdata=make_tables(spec,spec['validation_points']);vrows={i:response(p['kernel'],vdata['tables'][p['parameter_id']],spec['validation_points']) for i,p in allps.items()}
    validated=[dict(c,validation=compare([vrows[i] for i in allbs[c['bank_id']]['member_ids']],c['frontier'],
        c['illustrative_constants_by_member_and_q'],spec['training_q']+spec['validation_new_q'])) for c in candidates]
    write(directory/'validation_data.json',dict(vdata,candidate_batch_sha256=sha(directory/'candidate_batch.json'),
        program_responses=vrows,candidates=validated))
    bids={b['id'] for b in banks};aids={b['id'] for b in abanks}
    archive=select(banks,[c for c in validated if c['bank_id'] in bids],spec,allps)
    aarchive=select(abanks,[c for c in validated if c['bank_id'] in aids],spec,allps)
    best=lambda rows:min((c['recovery_cost']['best_log_cost'] for c in rows if c['recovery_cost'].get('best_log_cost') is not None),default=None)
    write(directory/'archive.json',{'archive':archive,'ablation_archive':aarchive,'selection_closed':True,'final_data_used':False,
        'ablation_comparison':{'equal_promotion_slot_budgets':True,'primary_programs':len(programs),'ablation_programs':len(ablation),
            'primary_banks':len(banks),'ablation_banks':len(abanks),'admitted_promotions':sum(p['admitted'] for p in promotions),
            'best_primary_log_cost':best(archive),'best_ablation_log_cost':best(aarchive)},
        'counterfeit_negative_controls':[{'candidate_id':c['id'],'bank_id':c['bank_id'],
            'analytic_status':'globally_false_by_uncancelled_counterfeit_pole_at_one',
            'cutoff':spec['counterfeit_tail_cutoff'],'same_numerical_constants':True} for c in archive if c['RH_sufficient_if_uniform']]})
    write(directory/'seal.json',{'protocol_sha256':digest(spec),'files':{n:sha(directory/n) for n in SEALED},
        'selection_closed':True,'final_cases_exist_at_seal':False,'parameter_cases_exist_at_seal':False})
    print('Sealed archive',len(archive),'RH-if-uniform',sum(c['RH_sufficient_if_uniform'] for c in archive),flush=True)


def parameter_cases(directory):
    spec=read(directory/'protocol.json');seal=read(directory/'seal.json');rule=spec['final_cases'];rng=random.Random(int.from_bytes(os.urandom(32),'big'))
    excluded=set(spec['training_q']+spec['validation_new_q'])|{q for r in spec['retained_failed_runs_are_development'] for q in r['excluded_final_q']}
    qs=sorted(rng.sample([q for q in range(rule['fresh_q_range'][0],rule['fresh_q_range'][1]+1) if q not in excluded],rule['fresh_q_count']))
    write(directory/'parameter_cases.json',{'fresh_q':qs,'seal_sha256':digest(seal),'generated_after_archive_seal':True,
        'no_final_scale_information_present':True})


def calibrate(directory):
    spec=read(directory/'protocol.json');verify_code(spec);denials=restrict(directory,True);flint.ctx.prec=spec['precision']
    pc=read(directory/'parameter_cases.json');batch=read(directory/'candidate_batch.json');bs={b['id']:b for b in batch['banks']};out=[]
    for c in read(directory/'archive.json')['archive']:
        rows=[batch['training_responses'][i] for i in bs[c['bank_id']]['member_ids']]
        constants=[fitted_constants(v,c['frontier'],pc['fresh_q'],spec) for v in rows]
        out.append({'candidate_id':c['id'],'constants':constants})
    write(directory/'parameter_calibration.json',{'parameters_sha256':digest(pc),'training_only':True,'final_scales_used':False,
        'worker_access_denials':denials,'illustrative_free_constants':out})
    write(directory/'calibration_seal.json',{'archive_seal_sha256':sha(directory/'seal.json'),
        'parameter_cases_sha256':sha(directory/'parameter_cases.json'),
        'parameter_calibration_sha256':sha(directory/'parameter_calibration.json'),
        'final_cases_exist_at_calibration_seal':False})


def finite_inverse(f):
    out=[Q(0)]*len(f);out[1]=1/Q(f[1])
    for n in range(2,len(f)):out[n]=-sum((Q(f[d])*out[n//d] for d in range(2,n+1) if n%d==0),Q(0))/Q(f[1])
    return out


def final(directory):
    spec=read(directory/'protocol.json');verify_code(spec);seal=read(directory/'seal.json');cal=read(directory/'calibration_seal.json')
    for n,h in seal['files'].items():assert sha(directory/n)==h
    for key,n in [('archive_seal_sha256','seal.json'),('parameter_cases_sha256','parameter_cases.json'),('parameter_calibration_sha256','parameter_calibration.json')]:assert cal[key]==sha(directory/n)
    if (directory/'final_cases.json').exists():raise FileExistsError('Final cases must be retained')
    seed=int.from_bytes(os.urandom(32),'big');rng=random.Random(seed);rule=spec['final_cases'];excluded={n for r in spec['retained_failed_runs_are_development'] for n in r['excluded_final_scales']}
    integers=sorted(rng.sample([n for n in range(rule['range'][0],rule['range'][1]+1) if n not in excluded],rule['count']))
    points=sorted(set(map(Q,integers+rule['boundary']))|{Q(n)+Q(rule['real_offset']) for n in integers})
    generic=[{'input':['0','1']+[str(Q(rng.randint(-5,5),rng.randint(1,5))) for _ in range(rule['generic_cutoff']-1)],
        'scale':str(Q(rng.randint(2,31),rng.randint(1,7))),'parameters':rng.choice(spec['parameters'])} for _ in range(rule['generic_count'])]
    cases={'seed':str(seed),'integers':integers,'points':list(map(str,points)),'generic_inputs':generic,
        'calibration_seal_sha256':digest(cal),'generated_after_calibration_seal':True}
    write(directory/'final_cases.json',cases);batch=read(directory/'candidate_batch.json');arc=read(directory/'archive.json');ps={p['id']:p for p in batch['programs']};bs={b['id']:b for b in batch['banks']}
    pc=read(directory/'parameter_cases.json');calcs={o['candidate_id']:o['constants'] for o in read(directory/'parameter_calibration.json')['illustrative_free_constants']}
    ids={i for c in arc['archive'] for i in bs[c['bank_id']]['member_ids']};params={tuple(ps[i]['parameters']) for i in ids};data=make_tables(spec,points,sorted(params))
    vals={i:response(ps[i]['kernel'],data['tables'][ps[i]['parameter_id']],points) for i in ids};outcomes=[];controls=[];increments=[];weak=[]
    qs=spec['training_q']+pc['fresh_q'];flint.ctx.prec=spec['precision']
    for c in arc['archive']:
        bank=bs[c['bank_id']];Cs=[dict(old,**new) for old,new in zip(c['illustrative_constants_by_member_and_q'],calcs[c['id']])]
        rows=[{str(n):vals[i][str(n)] for n in integers+rule['boundary']} for i in bank['member_ids']]
        o=compare(rows,c['frontier'],Cs,qs);outcomes.append(dict(o,candidate_id=c['id'],RH_sufficient_if_uniform=c['RH_sufficient_if_uniform']))
        if c['RH_sufficient_if_uniform']:
            H=Q(spec['counterfeit_tail_cutoff']);fake=[]
            for i in bank['member_ids']:
                k,ell,b=map(Q,ps[i]['parameters']);frows={}
                for X,txt in rows[bank['member_ids'].index(i)].items():
                    X=Q(X);E=sum((real(abs(Q(v)))*real(b**(j*m))*power(real(X),k+ell*m)
                        *power(real(H),1-k-ell*m)/real(k+ell*m-1) for m,j,v in ps[i]['kernel']['terms']),flint.arb(0))
                    frows[str(X)]=serialize(flint.arb(txt)+flint.arb(0,E))
                fake.append(frows)
            controls.append(dict(compare(fake,c['frontier'],Cs,qs),candidate_id=c['id'],complete_counterfeit_enclosures=fake,
                analytic_status='globally_false_by_uncancelled_counterfeit_pole_at_one',actual_arithmetic=False))
    for i in ids:
        gc=batch['global_certificates'][i];W=flint.arb(gc['constant_ball']);J=flint.arb(gc['unit_increment_constant_ball'])
        for X,v in vals[i].items():weak.append({'program_id':i,'scale':X,'passed':bool(abs(flint.arb(v))<=W*real(X))})
        for n in integers:
            diff=abs(flint.arb(vals[i][str(Q(n)+Q(rule['real_offset']))])-flint.arb(vals[i][str(n)]))
            increments.append({'program_id':i,'integer':n,'difference_ball':serialize(diff),
                'bound_ball':serialize(J*real(rule['real_offset'])),'passed':bool(diff<=J*real(rule['real_offset']))})
    generic_rows=[]
    for case in generic:
        f=list(map(Q,case['input']));g=finite_inverse(f);X=Q(case['scale']);k,ell,b=map(Q,case['parameters']);atoms=[]
        for m in range(spec['maximum_moment']+1):
            for j in range(spec['maximum_dilation']+1):
                v=flint.arb(0)
                for n in range(1,len(g)):
                    y=real(b**j)*power(real(X)/n,ell);v+=real(g[n])*power(real(X)/n,k)*y**m*(-y).exp()
                atoms.append({'moment':m,'dilation':j,'finite_response_ball':serialize(v)})
        generic_rows.append({'case':case,'inverse':list(map(str,g)),'finite_atom_responses':atoms,'infinite_tail_claimed':False})
    write(directory/'final_evaluation.json',{'protocol_sha256':digest(spec),'seal_sha256':digest(seal),'cases_sha256':digest(cases),
        'calibration_seal_sha256':digest(cal),'complete_arithmetic_data':data,'program_responses':vals,'outcomes':outcomes,
        'counterfeit_controls':controls,'unit_increment_checks':increments,'weak_bound_checks':weak,'generic_inputs':generic_rows,
        'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False})
    print('Fresh complete infinite sums checked',len(vals),'kernels',len(points),'scales',len(qs),'parameters',flush=True)


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('mode',choices=['run','worker','calibrate','final'],nargs='?',default='run')
    parser.add_argument('--run-dir',type=Path,required=True);parser.add_argument('--source',type=Path)
    args=parser.parse_args();d=args.run_dir.resolve()
    if args.mode=='worker':worker(d);return
    if args.mode=='calibrate':calibrate(d);return
    if args.mode=='final':final(d);return
    if args.source is None:raise ValueError('Verified Mertens compatibility source required')
    d.mkdir(parents=True,exist_ok=False);spec=protocol(args.source);write(d/'protocol.json',spec);(d/'frozen_source').mkdir()
    for n in CODE:(d/'frozen_source'/n).write_bytes((BASE/n).read_bytes())
    try:
        subprocess.run([sys.executable,str(BASE/'mellin_kernel_search.py'),'worker','--run-dir',str(d)],check=True,cwd=BASE)
        parameter_cases(d)
        subprocess.run([sys.executable,str(BASE/'mellin_kernel_search.py'),'calibrate','--run-dir',str(d)],check=True,cwd=BASE)
        final(d)
        subprocess.run([sys.executable,str(BASE/'check_mellin_kernels.py'),'--run-dir',str(d)],check=True,cwd=BASE)
        from mellin_kernel_report import summary
        write(d/'summary.json',summary(d));write(BASE/'mellin-kernel-results/latest.json',{'run_directory':str(d)})
    except Exception as exc:
        write(d/'failure.json',{'error_type':type(exc).__name__,'error':str(exc),'original_data_and_outcomes_retained':True});raise


if __name__=='__main__':main()
