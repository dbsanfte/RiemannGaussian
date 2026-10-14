"""Pole-admitted signed arithmetic work search with a fresh independent test."""
import argparse
from collections import Counter
from concurrent.futures import ProcessPoolExecutor,as_completed
from fractions import Fraction as Q
import gzip
import json
import multiprocessing as mp
from pathlib import Path
import re
import resource
import subprocess
import sys
import time
from flint import arb,ctx
import core_signed_work as P
import check_core_signed_work as C
import core_bound_synthesis as FIT
import core_pole_growth_obstruction as POLE
import centered_product_fibers as SERIAL
from prime_bank_candidates import Meter

ROOT=Path(__file__).resolve().parent
PARENT=ROOT/'core-bound-results/pilot-001'
FEEDBACK=PARENT/'pole-feedback-001'
SOURCE_PARENT=ROOT/'joint-preconditioner-results/pilot-001'
INPUT='candidate10_core_bound_obligation.json'
HEAD=[2**j for j in range(10)]
TRAIN=[1024,2048,4096,8192,16384]
VALIDATE=[32768,65536]
FINAL=[65536,98304,131072]
DISCOVERY=sorted(set(HEAD+TRAIN+VALIDATE+[2*x for x in TRAIN+VALIDATE]))
SCALES=sorted(set(DISCOVERY+FINAL+[2*x for x in FINAL]))
H=2*max(SCALES)-1
MAIN_CAP=750000000
CAPS={'producer':800000000,'checker':1600000000}
TOTAL=4000000000
SECONDS=3600
RESERVE=4000000
TESTS=['test_core_signed_work','test_check_core_signed_work']
RECEIPTS=['core_signed_work_producer_development.json','core_signed_work_checker_development.json']
SOURCES=['core_signed_work.py','check_core_signed_work.py','run_core_signed_work.py',
         'core_signed_work_protocol.txt','core_bound_synthesis.py','core_pole_growth_obstruction.py',
         'joint_preconditioned_source.py','prime_bank_candidates.py','centered_product_fibers.py',INPUT,
         'CORE_SIGNED_WORK_REVIEW_007.txt','CORE_CROSS_STORAGE_REVIEW_007.txt']+RECEIPTS+[t+'.py' for t in TESTS]
VECTORS=['core','F','log_prefix']+['mode:'+n for n in P.MODES]+['prefix:'+n for n in P.MODES]
MEASURES=['energy_filtered','critical_energy','prime_log_work','memory_cross','work']


def read(path):return json.loads(Path(path).read_text())


def write(path,data):
    with Path(path).open('x') as f:json.dump(data,f,indent=2,sort_keys=True);f.write('\n')


def parents():
    from run_core_pole_feedback import verify
    verify(FEEDBACK)
    if (ROOT/INPUT).read_bytes()!=(FEEDBACK/'next_search_input.json').read_bytes():raise ValueError('published original signed target')
    p=read(ROOT/INPUT)
    if p['whole_signed_bound_proved'] or p['RH_proved']:raise ValueError('open actual source obligation')
    return p


def receipts():
    out={n:read(ROOT/n) for n in RECEIPTS}
    for r in out.values():
        if not r['runs'] or r['runs'][-1]['returncode'] or r['operations']!=sum(t['operations'] for t in r['runs']):
            raise ValueError('passed last owned development checks with cumulative work')
    return out


def specification():
    return dict(schema='core-signed-work-search-v1',parent=parents(),
        grammar=dict(program_count=117,target_filters='13 full signed sixth-exponent delays',etas=list(P.ETA),
            rhos=list(P.RHOS),forcing_log_powers=list(P.LOG_POWERS),raw_hypotheses=1170,
            preadmitted_hypotheses=567),
        observable='complete signed shell W_eta=(1-eta)*N_G+eta*integral G B_G/(x^2 log x)',
        required_bound='W_eta(2X)<=rho W_eta(X)+C(1+log2X)^k for every dyadic X>=1024',
        finite_head=HEAD,training=TRAIN,validation=VALIDATE,final=FINAL,source_horizon=H,
        discovery_horizon=262143,final_fresh_child='[262144,524288), from final dyadic parent131072',
        irregular_probe='parent98304 is outside the dyadic theorem domain',
        gates_before_source_responses=['critical pole minimum degree after signed history recovery','paid delay inverse'],
        zero_constant_gate='after training, C0 implies bounded work and is rejected before ranking',
        constant_fit='integer ceil of5/4 times maximum nonnegative signed training ratio; no validation/final refit',
        ranking=['finite failure count','conditional full-core log degree','expression complexity','program ordinal','rho','forcing degree'],
        selection='best admitted per eta plus an eta1 critical-delay lane; deduplicate; freeze before new source',
        source_methods=['complete prime-local Euler coefficients','independent complete direct Mobius convolutions'],
        signed_work_methods=['stream12 complete moment sums, E1 cell integrals','literal scalar cells, Ei integrals'],
        source_bank='independent all-prime-power coefficient/prefix identity for every n throughH',
        all_vectors=VECTORS,all_source_crosses_and_units=True,models_in_generator_or_selection=False,
        main_cap=MAIN_CAP,worker_caps=CAPS,total_operations_limit=TOTAL,metadata_reserve=RESERVE,
        worker_seconds=SECONDS,main_seconds=4*SECONDS,workers=2,per_process_memory=4*1024**3,
        aggregate_memory_limit=16*1024**3,development=receipts(),hashes=False,
        all_scale_signed_control_proved=False,whole_signed_bound_proved=False,RH_proved=False)


def freeze(directory):
    directory=Path(directory).resolve();spec=specification()
    if directory.exists():raise FileExistsError('new study directory')
    directory.mkdir(parents=True);(directory/'source_snapshot').mkdir()
    for name in SOURCES:(directory/'source_snapshot'/name).write_bytes((ROOT/name).read_bytes())
    write(directory/'source_files.json',SOURCES);write(directory/'protocol.json',spec)
    (directory/'pole_witness.json').write_bytes((FEEDBACK/'pole_witness.json').read_bytes())
    write(directory/'source_program.json',read(SOURCE_PARENT/'selection.json')['selected'])


def verify(directory):
    if read(directory/'source_files.json')!=SOURCES:raise ValueError('full source manifest')
    for name in SOURCES:
        if (ROOT/name).read_bytes()!=(directory/'source_snapshot'/name).read_bytes():raise ValueError('changed frozen source '+name)
    if read(directory/'protocol.json')!=specification():raise ValueError('unchanged protocol')
    if (directory/'pole_witness.json').read_bytes()!=(FEEDBACK/'pole_witness.json').read_bytes():raise ValueError('unchanged certified pole witness')
    if read(directory/'source_program.json')!=read(SOURCE_PARENT/'selection.json')['selected']:raise ValueError('complete exact source AST')


def limit():
    _,hard=resource.getrlimit(resource.RLIMIT_AS);resource.setrlimit(resource.RLIMIT_AS,(4*1024**3,hard))


def compare(a,b,meter):
    a,b=arb(a),arb(b);meter.charge(16)
    if not SERIAL.tight(a) or not SERIAL.tight(b) or not a.overlaps(b):raise ArithmeticError('independent tight enclosure disagreement')


def shape_key(r):return (r['program_id'],r['rho'],r['log_power'])


def compile_grammar(directory,meter):
    witness=read(directory/'pole_witness.json');programs=P.catalogue(meter);shapes=[]
    for row in programs:
        C.verify_recovery(P.recovery_certificate(row['program']),meter)
        for rho in P.RHOS:
            for k in P.LOG_POWERS:
                gate=P.admission(row['program'],rho,k,witness)
                shapes.append(dict(program_id=row['id'],program=row['program'],rho=rho,log_power=k,
                    lane=row['lane'],complexity=row['complexity'],admission=gate,
                    status='awaiting_finite_evaluation' if gate['admitted'] else gate['reason']))
                meter.charge(300)
    if len(shapes)!=1170 or sum(r['admission']['admitted'] for r in shapes)!=567:raise ValueError('declared exact admission scope')
    write(directory/'programs.json',programs);write(directory/'hypothesis_shapes.json',shapes)
    write(directory/'prime_log_identity.json',P.prime_log_certificate(read(directory/'source_program.json')))
    return programs,shapes,witness


def select(directory,programs,shapes,witness,state,tables,meter):
    cache={};values={};winners={};counts=Counter();records=[]
    Ru=arb(read(PARENT/'producer_cases.json')['R_u'])
    references=[]
    for row in programs:
        cert=P.weak_reference(row['program']);C.verify_weak(cert,Ru,meter);references.append(cert)
    write(directory/'proved_reference_bounds.json',references)
    def rank(r):
        return (r['status']!='finite_survivor_open_uniform_premise',r['validation']['failed'],
                r['admission']['implied_core_log_degree'],r['complexity'],r['program_id'],Q(r['rho']),r['log_power'])
    for original in shapes:
        r=dict(original);pid=r['program_id'];p=r['program']
        if not r['admission']['admitted']:
            records.append(r);counts[r['status']]+=1;continue
        if pid not in values:values[pid]={X:P.measure(p,X,tables,meter,cache) for X in DISCOVERY}
        allrows=values[pid];rows={X:dict(majorant=v['work']) for X,v in allrows.items()}
        constant=FIT.fit(rows,TRAIN,r['rho'],'0',r['log_power'],meter)
        training=FIT.score(rows,TRAIN,r['rho'],'0',r['log_power'],constant,meter)
        validation=FIT.score(rows,VALIDATE,r['rho'],'0',r['log_power'],constant,meter)
        gate=P.admission(p,r['rho'],r['log_power'],witness,constant)
        B=str(max(0,int(rows[1024]['majorant'].upper().ceil().unique_fmpz())))
        E=str(max(int(allrows[X]['energy_filtered'].upper().ceil().unique_fmpz()) for X in HEAD))
        cert=P.recurrence_certificate(p,r['rho'],r['log_power'],constant,B,E)
        C.verify_recurrence(cert,meter)
        r.update(constant=constant,base_bound=B,head_bound=E,training=training,validation=validation,
                 admission=gate,conditional_certificate=cert,
                 status='zero_forcing_pole_obstruction' if not gate['admitted'] else
                        'finite_counterexample' if validation['failed'] else 'finite_survivor_open_uniform_premise')
        records.append(r);counts[r['status']]+=1;meter.charge(1000)
        if gate['admitted']:
            lanes=[r['lane']]
            if p['eta']=='1' and p['target_filter']['sign'] and p['target_filter']['theta']=='1/2':lanes.append('critical_delay_eta1')
            for lane in lanes:
                if lane not in winners or rank(r)<rank(winners[lane]):winners[lane]=r
    with gzip.open(directory/'hypotheses.jsonl.gz','xt',compresslevel=1) as f:
        for r in records:json.dump(r,f);f.write('\n')
    selected=[];seen={}
    for lane,r in sorted(winners.items()):
        k=shape_key(r)
        if k in seen:selected[seen[k]]['selection_lanes'].append(lane);continue
        seen[k]=len(selected)
        selected.append(dict(r,selection_lanes=[lane],discovery_values=SERIAL.serialize(values[r['program_id']]),next_obligation=P.obligation(r)))
    if len(selected)>10:raise ValueError('declared structural selection budget')
    result=dict(selected=selected,programs=len(programs),raw_hypotheses=len(shapes),preadmitted_hypotheses=567,
                status_counts=dict(counts),selected_before_fresh_source_generation=True,
                all_scale_work_bounds_proved=0,whole_signed_bound_proved=False,RH_proved=False)
    write(directory/'selection.json',result)
    print(json.dumps(dict(stage='signed_bounds_frozen',selected=len(selected),counts=dict(counts),operations=meter.operations)),flush=True)
    return result


def export_vectors(directory,role,state,meter):
    rows={n:state[n] for n in VECTORS[:3]}
    rows.update({'mode:'+n:state['modes'][n] for n in P.MODES})
    rows.update({'prefix:'+n:state['prefixes'][n] for n in P.MODES})
    with gzip.open(directory/(role+'_vectors.jsonl.gz'),'xt',compresslevel=1) as f:
        for name,values in rows.items():
            meter.charge(10*len(values));json.dump(dict(name=name,values=[SERIAL.encode(v) for v in values]),f);f.write('\n')


def worker(role,directory,selected,source_program):
    directory=Path(directory);ctx.prec=160 if role=='producer' else 192
    m=Meter(CAPS[role],SECONDS);start=time.monotonic();status='FAILED'
    try:
        state=P.source(H,source_program,m) if role=='producer' else C.source(H,m)
        print(json.dumps(dict(stage=role+'_source',H=H,operations=m.operations)),flush=True)
        if not 0<state['R_u']<=5:raise ArithmeticError('certified source residue ceiling')
        if role=='checker':
            bank=C.verify_logbank(state,m);bound=arb(2)**(-65)
            for n in range(H+1):
                for k in ('coefficients','prefix','coefficient_residual','prefix_residual'):
                    if not SERIAL.tight(bank[k][n]):raise ArithmeticError('tight full prime bank')
                if abs(bank['coefficient_residual'][n]).upper()>bound or abs(bank['prefix_residual'][n]).upper()>bound:
                    raise ArithmeticError('whole prime bank residual radius')
                m.charge(24)
            write(directory/'prime_bank_verification.json',dict(verified=True,coefficient_comparisons=H+1,prefix_comparisons=H+1,
                absolute_residual_bound='2^-65',all_actual_primes_and_powers=True,all_unit_cofactors=True,
                all_scale_signed_control_proved=False,whole_signed_bound_proved=False,RH_proved=False))
            del bank
            print(json.dumps(dict(stage='checker_prime_bank_verified',operations=m.operations)),flush=True)
        if role=='producer':tables=P.tables(state,SCALES,m);cache={}
        cases={}
        for record in selected:
            pid=str(record['program_id']);p=record['program']
            values={X:(P.measure(p,X,tables,m,cache) if role=='producer' else C.measure(p,X,state,m)) for X in SCALES}
            cases[pid]={str(X):{k:values[X][k] for k in ['X']+MEASURES} for X in SCALES}
            print(json.dumps(dict(stage=role+'_candidate',id=pid,operations=m.operations)),flush=True)
        write(directory/(role+'_cases.json'),SERIAL.serialize(dict(cases=cases,R_u=state['R_u'],H=H,precision=ctx.prec,
              whole_signed_bound_proved=False,RH_proved=False)))
        export_vectors(directory,role,state,m);status='COMPLETE'
    finally:
        resources=dict(status=status,operations=m.operations,peak_cells=m.peak_cells,
                       elapsed_seconds=time.monotonic()-start,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
        write(directory/(role+'_resources.json'),resources)
    return resources


def audit_vectors(directory,meter):
    count=old_count=0
    with gzip.open(directory/'producer_vectors.jsonl.gz','rt') as a,gzip.open(directory/'checker_vectors.jsonl.gz','rt') as b,gzip.open(PARENT/'producer_vectors.jsonl.gz','rt') as old:
        for name in VECTORS:
            x,y,z=json.loads(next(a)),json.loads(next(b)),json.loads(next(old))
            if z['name']=='log_abel':z=json.loads(next(old))
            if x['name']!=name or y['name']!=name or z['name']!=name or len(x['values'])!=H+1 or len(y['values'])!=H+1 or len(z['values'])!=262144:
                raise ValueError('complete corresponding source arrays')
            for n,(v,w) in enumerate(zip(x['values'],y['values'])):
                compare(v,w,meter);count+=1
                if n<262144:compare(w,z['values'][n],meter);old_count+=1
            print(json.dumps(dict(stage='source_vector_verified',name=name,entries=H+1)),flush=True)
        if a.read() or b.read() or old.read():raise ValueError('unverified extra source vector')
    return count,old_count


def run(directory):
    directory=Path(directory).resolve();verify(directory);limit();start=time.monotonic()
    write(directory/'started.json',dict(attempt=1))
    tests=subprocess.run([sys.executable,'-B','-m','unittest',*TESTS],capture_output=True,text=True,cwd=ROOT,timeout=60)
    counts=re.findall(r'^SYNTHETIC_WORK module=(\w+) operations=(\d+)$',tests.stdout,re.M)
    frozen=sum(int(n) for _,n in counts)
    write(directory/'frozen_tests.json',dict(returncode=tests.returncode,stdout=tests.stdout,stderr=tests.stderr,operations=frozen))
    if tests.returncode or sorted(k for k,_ in counts)!=sorted(TESTS):raise RuntimeError('passed one combined frozen suite')
    preparation=RESERVE+frozen+sum(r['operations'] for r in receipts().values())
    if preparation+MAIN_CAP+sum(CAPS.values())>TOTAL:raise ValueError('complete reserved aggregate work')
    m=Meter(MAIN_CAP,4*SECONDS);ctx.prec=192
    programs,shapes,witness=compile_grammar(directory,m)
    # Only now can an arithmetic response affect a bound or ranking.
    state=P.archived_state(PARENT,262143,m);tables=P.tables(state,DISCOVERY,m)
    selection=select(directory,programs,shapes,witness,state,tables,m)
    resources={}
    with ProcessPoolExecutor(max_workers=2,mp_context=mp.get_context('spawn'),initializer=limit) as pool:
        futures={pool.submit(worker,role,str(directory),selection['selected'],read(directory/'source_program.json')):role for role in CAPS}
        for future in as_completed(futures):
            role=futures[future];resources[role]=future.result();print(json.dumps(dict(stage=role+'_complete',**resources[role])),flush=True)
    compared,old_count=audit_vectors(directory,m)
    producer,checker=read(directory/'producer_cases.json'),read(directory/'checker_cases.json')
    compare(producer['R_u'],checker['R_u'],m);final=[]
    for r in selection['selected']:
        pid=str(r['program_id']);a=producer['cases'][pid];b=checker['cases'][pid]
        if set(a)!=set(b) or set(a)!=set(map(str,SCALES)):raise ValueError('all declared complete blocks')
        for X in SCALES:
            for k in MEASURES:
                compare(a[str(X)][k],b[str(X)][k],m)
                if X in DISCOVERY:compare(r['discovery_values'][str(X)][k],b[str(X)][k],m)
        rows={X:dict(majorant=arb(b[str(X)]['work'])) for X in SCALES}
        if rows[1024]['majorant'].upper()>arb(r['base_bound']):raise ArithmeticError('saved base upper bound')
        if any(arb(b[str(X)]['energy_filtered']).upper()>arb(r['head_bound']) for X in HEAD):raise ArithmeticError('complete saved finite energy head')
        C.verify_recurrence(r['conditional_certificate'],m)
        for scales,label in ((TRAIN,'training'),(VALIDATE,'validation')):
            score=FIT.score(rows,scales,r['rho'],'0',r['log_power'],r['constant'],m)
            if [d['status'] for d in score['decisions']]!=[d['status'] for d in r[label]['decisions']]:raise ArithmeticError('independent selection decision')
        score=FIT.score(rows,FINAL,r['rho'],'0',r['log_power'],r['constant'],m)
        for d in score['decisions']:
            d['inside_claimed_domain']=d['X']&(d['X']-1)==0
            if not d['inside_claimed_domain'] and d['status']=='counterexample':d['status']='irregular_probe_failure'
        score['all_probe_failures']=score['failed'];score['failed']=sum(d['inside_claimed_domain'] and d['status']!='passed' for d in score['decisions'])
        obligation=dict(r['next_obligation'])
        if any(d['status']=='counterexample' for d in score['decisions']):obligation['status']='counterexample_found'
        final.append(dict(program_id=r['program_id'],selection_lanes=r['selection_lanes'],program=r['program'],
                         rho=r['rho'],log_power=r['log_power'],constant=r['constant'],final_score=score,
                         conditional_certificate=r['conditional_certificate'],next_obligation=obligation,
                         whole_signed_bound_proved=False,RH_proved=False))
    write(directory/'final_bounds.json',final)
    total=preparation+m.operations+sum(r['operations'] for r in resources.values())
    if total>TOTAL:raise OverflowError('aggregate work cap')
    report=dict(status='SIGNED_PRIME_WORK_SEARCH_AND_INDEPENDENT_VERIFICATION_COMPLETE',programs=len(programs),
        raw_hypotheses=len(shapes),preadmitted_hypotheses=567,selection_status_counts=selection['status_counts'],
        selected_bounds=len(final),final_survivors=sum(r['final_score']['failed']==0 for r in final),
        final_counterexamples=sum(any(d['status']=='counterexample' for d in r['final_score']['decisions']) for r in final),
        checked_source_horizon=H,compared_vector_entries=compared,prior_prefix_comparisons=old_count,
        prime_bank=read(directory/'prime_bank_verification.json'),
        proved_recovery=dict(cutoff=1024,gap_lower='4/5',history_mass_upper='2/5',additional_block_log_loss=0),
        universal_reference='gamma1/logpower2 only',all_scale_signed_work_recurrences_proved=0,
        preparation_operations=preparation,main_operations=m.operations,worker_resources=resources,total_operations=total,
        elapsed_seconds=time.monotonic()-start,main_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        final_reselection=False,all_scale_signed_control_proved=False,whole_signed_bound_proved=False,RH_proved=False)
    verify(directory);write(directory/'report.json',report)
    next_input=dict(schema='signed-prime-work-obligations-v1',status='open',prior_input=INPUT,target=parents()['target'],
        generated_obligations=[dict(r['next_obligation'],fresh_final_score=r['final_score']) for r in final],
        exact_source_bank=read(directory/'prime_log_identity.json'),
        new_proved_rule='signed shell upper bound plus strict smaller-scale history controls complete target with no extra block log',
        remaining_proof='uniform actual-prime signed covariance step of a generated recurrence',
        prohibitions=['do not infer actual work bound from generic memory contraction','do not clip signed work','do not omit delayed log2 prefix','do not treat eta0 alias as a new arithmetic operator'],
        fresh_data_policy='all prefixes through524287 and these final scores are now observed',
        report=report,all_scale_signed_control_proved=False,whole_signed_bound_proved=False,RH_proved=False)
    write(directory/'next_search_input.json',next_input);print(json.dumps(report),flush=True)


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('action',choices=['freeze','run']);parser.add_argument('directory')
    args=parser.parse_args();globals()[args.action](args.directory)
