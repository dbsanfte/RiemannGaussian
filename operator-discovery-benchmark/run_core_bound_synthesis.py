"""End-to-end construction, inequality, proof attempt and fresh-test search."""
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
import core_bound_synthesis as D
import check_core_bound_synthesis as C
import prime_bank_candidates as S
import centered_product_fibers as SERIAL

ROOT=Path(__file__).resolve().parent
PARENT=ROOT/'joint-preconditioner-results/pilot-001'
INPUT='candidate10_joint_preconditioner_obligation.json'
TRAIN=[1,2,4,8,16,32,64,128,256,512,1024]
VALIDATE=[2048,4096,8192,16384]
FINAL=[32768,49152,65536]
DISCOVERY_SCALES=sorted(set(TRAIN+VALIDATE+[2*x for x in TRAIN+VALIDATE]))
ALL_SCALES=sorted(set(DISCOVERY_SCALES+FINAL+[2*x for x in FINAL]))
H=2*max(ALL_SCALES)-1
MAIN_CAP=750000000
CAPS={'producer':650000000,'checker':1700000000}
TOTAL=3200000000
SECONDS=3600
RESERVE=3000000
TESTS=['test_core_bound_synthesis','test_check_core_bound_synthesis']
RECEIPTS=['core_bound_producer_development.json','core_bound_checker_development.json']
REVIEWS=['JOINT_CORE_LOG_RECURRENCE_REVIEW_005.txt','JOINT_CORE_KERNEL_RECOVERY_REVIEW_005.txt',
         'JOINT_CORRELATION_PAIRING_REVIEW_004.txt']
SOURCES=['core_bound_synthesis.py','check_core_bound_synthesis.py','run_core_bound_synthesis.py',
         'core_bound_synthesis_protocol.txt','prime_bank_candidates.py','joint_preconditioned_source.py',
         'centered_product_fibers.py',INPUT]+[t+'.py' for t in TESTS]+RECEIPTS+REVIEWS
VECTORS=['core','F','log_prefix','log_abel']+['mode:'+n for n in D.NAMES]+['prefix:'+n for n in D.NAMES]


def read(path):return json.loads(Path(path).read_text())


def write(path,data):
    with Path(path).open('x') as stream:
        json.dump(data,stream,sort_keys=True,indent=2);stream.write('\n')


def receipts():
    rows={n:read(ROOT/n) for n in RECEIPTS}
    for row in rows.values():
        if not row['runs'] or row['runs'][-1]['returncode'] or row['operations']!=sum(r['operations'] for r in row['runs']):
            raise ValueError('passed cumulative owned development suites')
    return rows


def parent():
    p=read(ROOT/INPUT)
    if p['schema']!='joint-preconditioned-correlation-obligation-v1' or p['whole_signed_bound_proved'] or p['RH_proved']:
        raise ValueError('unchanged complete open core obligation')
    if (ROOT/INPUT).read_bytes()!=(PARENT/'next_search_input.json').read_bytes():raise ValueError('published target bytes')
    for name in read(PARENT/'source_files.json'):
        if (ROOT/name).read_bytes()!=(PARENT/'source_snapshot'/name).read_bytes():raise ValueError('changed parent source '+name)
    return p


def specification():
    return dict(schema='automatic-core-bound-synthesis-v1',parent=parent(),
        grammar=dict(target_filters=D.filters(),auxiliary_coefficients='all single coordinates and all signed two-coordinate sums in the full four-mode basis',
            auxiliary_delays=list(D.AUX_THETAS),fractional_weights=list(D.ALPHAS),storage_weights=list(D.WEIGHTS),
            program_count=10766,rhos=list(D.RHOS),forcing_powers=list(D.GAMMAS),forcing_log_powers=list(D.LOG_POWERS),
            numerical_hypothesis_count=86128),
        source_order=list(D.NAMES),full_source_scalars=['beta','-beta','-R_u','-beta'],
        auxiliary='A(X)=E_G(X)+w*E_H(X)>=E_G(X), full squares and signed cross terms',
        searched_inequality='A(2X)<=rho*A(X)+C*X^gamma*(1+log2X)^k, every dyadic X>=1',
        constant_fitting='integer ceiling of5/4 times the nonnegative maximum training ratio; never refit on later data',
        selection=['cofinal eligibility including analytic pole gate','validation failures','conditional core log degree','AST complexity','forcing power','program ordinal','rho','log power'],
        archive='all hypotheses, including analytic obstructions, counterexamples and unsupported survivors',
        training_parent_scales=TRAIN,validation_parent_scales=VALIDATE,final_parent_scales=FINAL,
        prior_overlap='training/validation reuse independently verified archived prefixes; final32768 is calibration; final49152 is irregular and partly fresh; final65536 has a wholly fresh child block',
        final_policy='best per declared structural lane, saved before generation of source through262143; no final reselection',
        proof_methods=['positive auxiliary domination','bounded/polylog causal recovery','Volterra recovery with finite head',
                       'conditional dyadic induction','retained-pole rejection','unconditional gamma1/logpower2 absolute-prefix reference'],
        unsupported_core_bounds_remain_open=True,generator_and_selector_model_calls=False,
        horizon=H,source_bits=160,checker_bits=192,all_vectors=VECTORS,
        arithmetic='streamed9x9 weighted Gram with all36 off-diagonal orientations; independent literal squared expressions',
        main_cap=MAIN_CAP,worker_caps=CAPS,total_work_limit=TOTAL,metadata_reserve=RESERVE,
        worker_seconds=SECONDS,main_seconds=4*SECONDS,workers=2,process_memory_bytes=4*1024**3,
        aggregate_memory_limit=16*1024**3,development=receipts(),hashes=False,
        whole_signed_bound_proved=False,RH_proved=False)


def freeze(directory):
    directory=Path(directory).resolve();protocol=specification()
    raw={n:(ROOT/n).read_bytes() for n in SOURCES}
    if directory.exists():raise FileExistsError('new immutable experiment')
    directory.mkdir(parents=True);(directory/'source_snapshot').mkdir()
    for n,data in raw.items():(directory/'source_snapshot'/n).write_bytes(data)
    write(directory/'source_files.json',SOURCES);write(directory/'protocol.json',protocol)


def verify(directory):
    if read(directory/'source_files.json')!=SOURCES:raise ValueError('complete source manifest')
    for n in SOURCES:
        if (ROOT/n).read_bytes()!=(directory/'source_snapshot'/n).read_bytes():raise ValueError('changed frozen source '+n)
    if read(directory/'protocol.json')!=specification():raise ValueError('changed specification')


def limit():
    _,hard=resource.getrlimit(resource.RLIMIT_AS);resource.setrlimit(resource.RLIMIT_AS,(4*1024**3,hard))


def compare(left,right,meter):
    a,b=arb(left),arb(right);meter.charge(16)
    if not SERIAL.tight(a) or not SERIAL.tight(b) or not a.overlaps(b):raise ArithmeticError('independent tight disagreement')


def publish_vectors(directory,role,state,meter):
    rows={n:state[n] for n in VECTORS[:4]}
    rows.update({'mode:'+n:state['modes'][n] for n in D.NAMES})
    rows.update({'prefix:'+n:state['prefixes'][n] for n in D.NAMES})
    if list(rows)!=VECTORS:raise ValueError('complete vectors')
    with gzip.open(directory/(role+'_vectors.jsonl.gz'),'xt',compresslevel=1) as stream:
        for name,values in rows.items():
            meter.charge(10*len(values))
            json.dump(dict(name=name,values=[SERIAL.encode(v) for v in values]),stream);stream.write('\n')


def fresh_worker(role,directory,selected,source_program):
    directory=Path(directory);ctx.prec=160 if role=='producer' else 192
    meter=S.Meter(CAPS[role],SECONDS);start=time.monotonic();status='FAILED'
    try:
        state=D.source(H,source_program,meter) if role=='producer' else C.source(H,meter)
        print(json.dumps(dict(stage=role+'_fresh_source',H=H,operations=meter.operations)),flush=True)
        if not 0<state['R_u']<=5:raise ArithmeticError('certified fixed residue ceiling')
        if role=='producer':tables=D.gram_tables(state,ALL_SCALES,meter);cache={}
        cases={}
        for record in selected:
            pid=str(record['program_id']);program=record['program']
            if role=='producer':values=D.energies(program,tables,state,meter,cache)
            else:values={X:C.measure(program,X,state,meter) for X in ALL_SCALES}
            cases[pid]={str(X):{k:row[k] for k in ('X','energy_target','energy_filtered','energy_auxiliary','majorant')} for X,row in values.items()}
            print(json.dumps(dict(stage=role+'_candidate',id=pid,operations=meter.operations)),flush=True)
        meter.charge(300000)
        write(directory/(role+'_cases.json'),SERIAL.serialize(dict(cases=cases,R_u=state['R_u'],precision=ctx.prec,H=H,
              whole_signed_bound_proved=False,RH_proved=False)))
        publish_vectors(directory,role,state,meter);status='COMPLETE'
    finally:
        resources=dict(status=status,operations=meter.operations,peak_cells=meter.peak_cells,
                       elapsed_seconds=time.monotonic()-start,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
        write(directory/(role+'_resources.json'),resources)
    return resources


def select(directory,programs,state,tables,meter):
    cache={};gates={};winners={};totals=Counter();reference_count=0
    with gzip.open(directory/'hypotheses.jsonl.gz','xt',compresslevel=1) as archive, gzip.open(directory/'proved_reference_bounds.jsonl.gz','xt',compresslevel=1) as references:
        for row in programs:
            program=row['program'];aux=program['auxiliary']
            gate_key=None if aux is None else (tuple(aux['coefficients']),aux['theta'],aux['alpha'])
            if gate_key not in gates:gates[gate_key]=D.pole_gate(program,meter)
            gate=gates[gate_key]
            values=D.energies(program,tables,state,meter,cache)
            base=str(max(0,int(values[1]['majorant'].upper().ceil().unique_fmpz())))
            certificate=D.coarse_certificate(program)
            C.verify_coarse(certificate,state['R_u'],meter)
            json.dump(dict(program_id=row['id'],certificate=certificate),references);references.write('\n')
            reference_count+=1
            for rho,gamma,k in product_hypotheses():
                constant=D.fit(values,TRAIN,rho,gamma,k,meter)
                training=D.score(values,TRAIN,rho,gamma,k,constant,meter)
                validation=D.score(values,VALIDATE,rho,gamma,k,constant,meter)
                record=D.hypothesis_record(row,rho,gamma,k,constant,base,training,validation,gate)
                json.dump(record,archive);archive.write('\n');meter.charge(1000)
                totals[record['status']]+=1
                lane=row['lane']
                if lane not in winners or D.rank(record)<D.rank(winners[lane]):winners[lane]=record
            if row['id']%1024==0:print(json.dumps(dict(stage='bound_search',program=row['id'],operations=meter.operations)),flush=True)
    selected=[]
    for lane,record in sorted(winners.items()):
        row=programs[record['program_id']]
        values=D.energies(row['program'],tables,state,meter,cache)
        selected.append(dict(record,program=row['program'],discovery_values=SERIAL.serialize(values),
                             next_obligation=D.obligation(record,row)))
    # Different lanes have disjoint baseline/auxiliary definitions; each selected program is unique.
    if len({r['program_id'] for r in selected})!=len(selected):raise ValueError('unique selected source programs')
    selection=dict(selected=selected,status_counts=dict(totals),candidate_hypotheses=sum(totals.values()),
                   automatically_verified_reference_instances=reference_count,independent_reference_rule_count=1,
                   reference_growth_power='1',selected_before_fresh_source_generation=True,
                   uniform_critical_bounds_proved=0,whole_signed_bound_proved=False,RH_proved=False)
    write(directory/'selection.json',selection)
    print(json.dumps(dict(stage='candidate_bounds_frozen',selected=len(selected),hypotheses=sum(totals.values()),counts=dict(totals))),flush=True)
    return selection


def product_hypotheses():
    return [(r,g,k) for r in D.RHOS for g in D.GAMMAS for k in D.LOG_POWERS]


def audit_vectors(directory,meter):
    count=0
    with gzip.open(directory/'producer_vectors.jsonl.gz','rt') as left,gzip.open(directory/'checker_vectors.jsonl.gz','rt') as right:
        for name in VECTORS:
            a,b=json.loads(next(left)),json.loads(next(right))
            if a['name']!=name or b['name']!=name or len(a['values'])!=H+1 or len(b['values'])!=H+1:raise ValueError('complete same vector')
            for n,(old,new) in enumerate(zip(a['values'],b['values'])):
                try:compare(old,new,meter)
                except ArithmeticError as error:raise ArithmeticError(name+' at '+str(n)) from error
                count+=1
            print(json.dumps(dict(stage='full_vector_verified',name=name,entries=H+1)),flush=True)
        if left.read() or right.read():raise ValueError('extra unverified vector')
    return count


def run(directory):
    directory=Path(directory).resolve();verify(directory);limit();start=time.monotonic()
    write(directory/'started.json',dict(attempt=1,monotonic=start))
    tests=subprocess.run([sys.executable,'-B','-m','unittest',*TESTS],cwd=ROOT,capture_output=True,text=True,timeout=60)
    counts=re.findall(r'^SYNTHETIC_WORK module=(\w+) operations=(\d+)$',tests.stdout,re.M)
    frozen=sum(int(n) for _,n in counts)
    write(directory/'frozen_tests.json',dict(returncode=tests.returncode,stdout=tests.stdout,stderr=tests.stderr,operations=frozen))
    if tests.returncode or sorted(k for k,_ in counts)!=sorted(TESTS):raise RuntimeError('one complete passed frozen suite')
    preparation=RESERVE+frozen+sum(r['operations'] for r in receipts().values())
    if preparation+MAIN_CAP+sum(CAPS.values())>TOTAL:raise ValueError('complete aggregate reserve')
    main=S.Meter(MAIN_CAP,4*SECONDS);ctx.prec=192
    programs=D.catalogue(main);write(directory/'programs.json',programs)
    # Source responses are read only after the full expression grammar is saved.
    state=D.archived_source(PARENT,'producer',2*max(DISCOVERY_SCALES)-1,main)
    if not 0<state['R_u']<=5:raise ArithmeticError('fixed residue ceiling')
    tables=D.gram_tables(state,DISCOVERY_SCALES,main)
    selection=select(directory,programs,state,tables,main)
    source_program=read(PARENT/'selection.json')['selected']
    resources={}
    with ProcessPoolExecutor(max_workers=2,mp_context=mp.get_context('spawn'),initializer=limit) as pool:
        futures={pool.submit(fresh_worker,role,str(directory),selection['selected'],source_program):role for role in CAPS}
        for future in as_completed(futures):
            role=futures[future];resources[role]=future.result()
            print(json.dumps(dict(stage=role+'_archived',**resources[role])),flush=True)
    compared=audit_vectors(directory,main)
    producer,checker=read(directory/'producer_cases.json'),read(directory/'checker_cases.json')
    compare(producer['R_u'],checker['R_u'],main)
    results=[]
    for selected in selection['selected']:
        pid=str(selected['program_id']);a=producer['cases'][pid];b=checker['cases'][pid]
        if set(a)!=set(b) or set(a)!=set(map(str,ALL_SCALES)):raise ValueError('all declared source blocks')
        for X in ALL_SCALES:
            for key in ('energy_target','energy_filtered','energy_auxiliary','majorant'):
                compare(a[str(X)][key],b[str(X)][key],main)
                if X in DISCOVERY_SCALES:compare(selected['discovery_values'][str(X)][key],b[str(X)][key],main)
        rows={X:{k:arb(v) if k!='X' else v for k,v in b[str(X)].items()} for X in ALL_SCALES}
        for scales,label in ((TRAIN,'training'),(VALIDATE,'validation')):
            scores=D.score(rows,scales,selected['rho'],selected['gamma'],selected['log_power'],selected['constant'],main)
            if [r['status'] for r in scores['decisions']]!=[r['status'] for r in selected[label]['decisions']]:raise ArithmeticError('independent fit/selection decision disagreement')
        final=D.score(rows,FINAL,selected['rho'],selected['gamma'],selected['log_power'],selected['constant'],main)
        for decision in final['decisions']:
            decision['inside_claimed_dyadic_domain']=(decision['X']&(decision['X']-1))==0
            if not decision['inside_claimed_dyadic_domain'] and decision['status']=='counterexample':
                decision['status']='irregular_probe_failure'
        final['all_probe_failures']=final['failed']
        final['failed']=sum(d['inside_claimed_dyadic_domain'] and d['status']!='passed' for d in final['decisions'])
        next_obligation=dict(selected['next_obligation'])
        if any(d['status']=='counterexample' for d in final['decisions']):next_obligation['status']='counterexample_found'
        results.append(dict(program_id=selected['program_id'],lane=selected['lane'],program=selected['program'],
                            rho=selected['rho'],gamma=selected['gamma'],log_power=selected['log_power'],constant=selected['constant'],
                            cofinal_candidate=selected['cofinal_candidate'],final_score=final,
                            next_obligation=next_obligation,whole_signed_bound_proved=False,RH_proved=False))
    write(directory/'final_bounds.json',results)
    total=preparation+main.operations+sum(r['operations'] for r in resources.values())
    if total>TOTAL:raise OverflowError('cumulative work cap')
    report=dict(status='AUTOMATIC_CORE_BOUND_SEARCH_AND_INDEPENDENT_EVALUATION_COMPLETE',
        programs=len(programs),hypotheses=selection['candidate_hypotheses'],selection_status_counts=selection['status_counts'],
        selected_bounds=len(results),final_survivors=sum(r['final_score']['failed']==0 for r in results),
        final_counterexample_bounds=sum(any(d['status']=='counterexample' for d in r['final_score']['decisions']) for r in results),
        universally_proved_reference_rule='absolute_prefix_majorants: gamma1,logpower2',
        reference_instantiations=selection['automatically_verified_reference_instances'],
        universally_proved_critical_bounds=0,checked_source_horizon=H,compared_vector_entries=compared,
        all_source_crosses_and_units=True,final_reselection=False,
        preparation_operations=preparation,main_operations=main.operations,worker_resources=resources,
        total_operations=total,elapsed_seconds=time.monotonic()-start,
        main_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        whole_signed_bound_proved=False,RH_proved=False)
    verify(directory);write(directory/'report.json',report)
    next_input=dict(schema='automatically-generated-core-bound-obligations-v1',status='open',prior_input=INPUT,
        target=parent()['missing_bound'],search_language='core_bound_synthesis.py',
        selected_generated_obligations=[dict(r['next_obligation'],fresh_final_score=r['final_score']) for r in results],
        next_priority='attempt a proof of a surviving complete signed increment; falsified constants remain archived and are not refit',
        proved_reference='gamma1/logpower2 cannot supply critical signed control',
        remaining_proof='uniform signed step of the generated recurrence, not its finite fit or conditional induction',
        report=report,whole_signed_bound_proved=False,RH_proved=False)
    write(directory/'next_search_input.json',next_input)
    print(json.dumps(report),flush=True)


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('action',choices=['freeze','run']);parser.add_argument('directory')
    args=parser.parse_args();globals()[args.action](args.directory)
