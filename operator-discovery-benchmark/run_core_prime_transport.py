"""One frozen joint search of arithmetic transports AND complete core bounds."""
from collections import Counter
from concurrent.futures import ProcessPoolExecutor,as_completed
from fractions import Fraction as Q
import gzip
import json
import math
import multiprocessing as mp
from pathlib import Path
import re
import resource
import subprocess
import sys
import time
import numpy as np
from flint import arb,ctx
import core_prime_transport as P
import check_core_prime_transport as C
import core_control_synthesis as B
import check_core_control_synthesis as K
import centered_product_fibers as SERIAL
from prime_bank_candidates import Meter
from run_core_arithmetic_grouping import verify as verify_parent

ROOT=Path(__file__).resolve().parent
PARENT=ROOT/'core-arithmetic-grouping-results/pilot-001'
FEEDBACK=PARENT/'proof-followup-001'
SOURCE=ROOT/'core-signed-work-results/pilot-001'
OUT=ROOT/'core-prime-transport-results/pilot-001'
INPUT='candidate10_arithmetic_grouping_obligation.json'
TRAIN=[2**k for k in range(10)]
VALIDATION=[1024,2048]
LARGER=[4096,8192]
DISCOVERY_SCALES=[2**k for k in range(13)]
SCALES=[2**k for k in range(15)]
DISCOVERY_H=8191
H=32767
TOTAL_CAP=2500000000
MAIN_CAP=600000000
WORKER_CAP=850000000
RESERVE=5000000
TESTS=['test_core_prime_transport','test_check_core_prime_transport','test_core_control_synthesis','test_check_core_control_synthesis']
RECEIPTS=['core_prime_transport_producer_development.json','core_prime_transport_checker_development.json',
          'core_control_producer_development.json','core_control_checker_development.json']
FILES=['core_prime_transport.py','check_core_prime_transport.py','core_control_synthesis.py','check_core_control_synthesis.py',
       'run_core_prime_transport.py','core_prime_transport_protocol.txt','CORE_PRIME_COMPOSITE_TRANSPORT_REVIEW_011.txt',
       'CORE_CONTROL_SYNTHESIS_REVIEW_012.txt','prime_bank_candidates.py','centered_product_fibers.py',INPUT]+RECEIPTS+[n+'.py' for n in TESTS]
VECTORS=['g','F','G','B','Bg','D','B_D']
CERT_KEYS=['domination_constant','full_target_storage_constant','error_constant','error_power',
           'conditional_log_degree','pole_excluded','cofinal_recovery','uniform_premise_established',
           'all_scale_storage_bound_proved','all_scale_target_bound_proved','RH_proved']


def read(path):return json.loads(Path(path).read_text())
def write(path,data):
    with Path(path).open('x') as f:json.dump(data,f,indent=2,sort_keys=True);f.write('\n')
def stat(m,start):
    return dict(operations=m.operations,peak_cells=m.peak_cells,elapsed_seconds=time.monotonic()-start,
                peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
def limits():
    _,hard=resource.getrlimit(resource.RLIMIT_AS);resource.setrlimit(resource.RLIMIT_AS,(4*1024**3,hard))


def parents():
    verify_parent()
    for name in read(FEEDBACK/'source_files.json'):
        if (ROOT/name).read_bytes()!=(FEEDBACK/'source_snapshot'/name).read_bytes():raise ValueError('changed parent feedback '+name)
    if (ROOT/INPUT).read_bytes()!=(FEEDBACK/'next_search_input.json').read_bytes():raise ValueError('current complete input')
    source=read(SOURCE/'source_program.json');witness=read(SOURCE/'pole_witness.json')
    if witness['source_terms']!=source['terms'] or witness['source_pole']['minimum_dyadic_energy_log_degree']!=2:
        raise ValueError('original full source pole binding')
    for w in witness['numerical_witnesses']:
        if not w['unique_simple_zero'] or w['critical_real_part']!='1/2' or not arb(w['core_laurent_leading_abs_lower'])>0:
            raise ValueError('certified original critical double pole')
    return source,witness


def verify():
    parents()
    for name in read(OUT/'source_files.json'):
        if (ROOT/name).read_bytes()!=(OUT/'source_snapshot'/name).read_bytes():raise ValueError('changed frozen study '+name)
    if (OUT/'source_program.json').read_bytes()!=(SOURCE/'source_program.json').read_bytes():raise ValueError('source AST')
    if (OUT/'pole_witness.json').read_bytes()!=(SOURCE/'pole_witness.json').read_bytes():raise ValueError('pole witness')


def archived(role,H,meter):
    with gzip.open(SOURCE/(role+'_vectors.jsonl.gz'),'rt') as f:
        for line in f:
            row=json.loads(line);meter.charge(5*len(row['values']))
            if row['name']=='core':
                if len(row['values'])<=H:raise ValueError('complete archive source horizon')
                return [arb(x) for x in row['values'][:H+1]]
    raise ValueError('complete archived core')


def recovery_check(row,source,Ru,meter):
    c=C.verify_recovery(row['program'],source,Ru,meter);p=row['certificate']
    for a,b in [('energy_error_power','error_energy_power'),('cofinal_recovery','cofinal_recovery'),
                ('cofactor_leading_capacity_positive','cofactor_positive_limit'),('eventual_prime_removal_proved','eventual_prime_deletion')]:
        if p[a]!=c[b]:raise ArithmeticError('independent all-scale recovery rule disagreement')
    return c


def finite_state(state,source,meter):
    f=np.array([float(v) for v in source]);g=np.array([float(v) for v in state['g']]);n=np.arange(1,len(f))
    F=f.cumsum();G=g.cumsum();logs=np.concatenate(([0.],np.log(n)))
    meter.charge(30*state['H'])
    return dict(H=state['H'],G=G,Bg=np.cumsum(g*logs),D=F-G)


def exact_worker(role,selected,transports):
    limits();ctx.prec=192;start=time.monotonic();m=Meter(WORKER_CAP,3600)
    f=archived(role,H,m);cases=[]
    for row in transports:
        related=[r for r in selected if r['transport_id']==row['id']]
        if not related:continue
        state=P.exact_scores(P.transform(f,row['program'],m),f,SCALES,m) if role=='producer' else C.transform(f,row['program'],m)
        controls=[]
        for record in related:
            values={X:(B.exact_measure(state,record['storage_program'],X,m) if role=='producer' else K.measure(state,record['storage_program'],X,m)) for X in SCALES}
            tests=(B.exact_test(values,TRAIN+VALIDATION+LARGER,record['shape'],record['constant'],m) if role=='producer' else
                   K.check_test(values,TRAIN+VALIDATION+LARGER,record['shape'],record['constant'],m))
            controls.append(dict(id=record['id'],values=values,tests=tests))
        path=OUT/(role+'-transport-'+str(row['id'])+'.json.gz')
        payload=dict(transport_id=row['id'],H=H,program=row['program'],vectors={k:state[k] for k in VECTORS},
                     windows=state['windows'],assignments=state['assignments'],blocks=state['blocks'],controls=controls)
        with gzip.open(path,'xt',compresslevel=1) as stream:json.dump(SERIAL.serialize(payload),stream)
        m.charge(15*(len(VECTORS)*(H+1)+len(state['assignments'])))
        cases.append(path.name)
        print(json.dumps(dict(stage=role+'_verified_candidate_arithmetic',transport_id=row['id'],controls=len(related),operations=m.operations)),flush=True)
    result=dict(paths=cases,resources=stat(m,start));write(OUT/(role+'_resources.json'),result)
    return result


def compare(left,right,meter):
    x,y=arb(left),arb(right);meter.charge(20)
    if not SERIAL.tight(x) or not SERIAL.tight(y) or not x.overlaps(y):raise ArithmeticError('tight independent scalar disagreement')


def main():
    limits();ctx.prec=192;start=time.monotonic();source,witness=parents()
    if OUT.exists():raise FileExistsError('one immutable terminal attempt; no restart')
    dev={name:read(ROOT/name) for name in RECEIPTS}
    for r in dev.values():
        if not r['runs'] or r['runs'][-1]['returncode'] or r['operations']!=sum(x['operations'] for x in r['runs']):
            raise ValueError('passed owned checks with complete development cost')
    OUT.mkdir(parents=True);(OUT/'source_snapshot').mkdir()
    for name in FILES:(OUT/'source_snapshot'/name).write_bytes((ROOT/name).read_bytes())
    write(OUT/'source_files.json',FILES)
    for name in ('source_program.json','pole_witness.json'):(OUT/name).write_bytes((SOURCE/name).read_bytes())
    spec=dict(schema='joint-arithmetic-operator-and-bound-search-v1',parent_input=INPUT,
        grammar=dict(transports=90,cofactors=list(range(2,17)),window_powers=list(P.THETAS),storages=55,
            auxiliary_kinds=list(B.KINDS),fractional_auxiliary_weights=list(B.ALPHAS),mixes=list(B.MIXES),reserves=list(B.RESERVES),bound_shapes=B.shapes()),
        searched='A(X)=E_(G+aQ)(X)+wE_Q(X); A(2X)<=rho*A(X)+C(1+log2X)^k',
        proof_composition='sum-square domination -> dyadic recurrence -> paid transport recovery -> original f pole minimum degree',
        training_parents=TRAIN,validation_parents=VALIDATION,larger_parents=LARGER,discovery_horizon=DISCOVERY_H,verification_horizon=H,
        fit='max(1,ceil(5/4*max(0,training normalized drift))); fixed before validation, never refitted',
        ranking=['validation failure count','conditional original-core log degree','worst observed storage doubling power on1024,2048,4096','AST complexity','negative training-final-annulus prime coverage',
                 'transport ordinal','storage ordinal','rho','forcing log degree'],
        selection='one best per auxiliary mechanism and each admitted window exponent; all choices frozen before larger transformed observables',
        data_status='underlying source already observed through524287; all new transformed observations are exploratory, NOT fresh holdout',
        full_units_crosses_prime_powers_and_corrections=True,models_in_generator_or_selector=False,
        analyst_supplied=['arithmetic/auxiliary grammar','elementary recovery/proof rules','reviewed short-prime-interval theorem'],
        detector_generated=['every joint construction','every bound shape and training constant','selection','proof-rule compositions and open dependency graphs'],
        workers=2,main_cap=MAIN_CAP,worker_cap=WORKER_CAP,total_operations_cap=TOTAL_CAP,main_seconds=14400,worker_seconds=3600,
        process_memory_bytes=4*1024**3,aggregate_memory_limit=16*1024**3,metadata_reserve=RESERVE,development=dev,hashes=False,
        uniform_premise_proved=False,whole_signed_bound_proved=False,RH_proved=False)
    write(OUT/'protocol.json',spec)
    meter=Meter(MAIN_CAP,14400);meter.charge(RESERVE)
    z=(arb(2)/3).zeta();Ru=arb(9)/2*((arb(4)/3).zeta()/(z*z)-1/z);meter.charge(1000)
    if not Ru.overlaps(arb(read(SOURCE/'producer_cases.json')['R_u'])):raise ArithmeticError('actual complete Ru')
    rows=P.catalogue(meter);storages=B.catalogue(meter);shapes=B.shapes()
    proof_rows=[]
    for row in rows:proof_rows.append(dict(id=row['id'],recovery=recovery_check(row,source,Ru,meter)))
    write(OUT/'transports.json',rows);write(OUT/'storage_programs.json',storages);write(OUT/'independent_recovery.json',proof_rows)
    # Check every compiled proof combination before any source responses.
    proof_comparisons=0;pole_rejections=0
    for row in rows:
        if not row['admitted']:continue
        for storage in storages:
            for shape in shapes:
                p=B.certificate(storage['program'],shape,row['program'],True)
                c=K.certificate(storage['program'],shape,row['program'],True,meter=meter)
                if any(p[k]!=c[k] for k in CERT_KEYS):raise ArithmeticError('independent compiled proof mismatch')
                proof_comparisons+=1;pole_rejections+=p['pole_excluded'];meter.charge(100)
    write(OUT/'proof_compilation.json',dict(checked_compositions=proof_comparisons,pole_rejections=pole_rejections,
        original_source_pole_bound_via_paid_recovery=True,uniform_target_bounds_proved=0))
    test_start=time.monotonic();test=subprocess.run([sys.executable,'-B','-m','unittest']+TESTS,cwd=ROOT,capture_output=True,text=True)
    test_ops=sum(map(int,re.findall(r'operations=(\d+)',test.stdout)))
    write(OUT/'frozen_tests.json',dict(returncode=test.returncode,stdout=test.stdout,stderr=test.stderr,operations=test_ops,elapsed_seconds=time.monotonic()-test_start))
    if test.returncode:raise RuntimeError('combined frozen suite failed')
    print(json.dumps(dict(stage='joint_grammar_and_proofs_frozen',transports=len(rows),admitted=sum(r['admitted'] for r in rows),
                         storages=len(storages),bound_shapes=len(shapes),proof_comparisons=proof_comparisons,pole_rejections=pole_rejections)),flush=True)
    # The first actual response access is below this point.
    f=archived('producer',DISCOVERY_H,meter);selected={};discovery=[];hypothesis_count=0;status_counts=Counter()
    with gzip.open(OUT/'hypotheses.jsonl.gz','xt',compresslevel=1) as archive:
        for transport in rows:
            if not transport['admitted']:continue
            state=P.transform(f,transport['program'],meter);numeric=finite_state(state,f,meter)
            tables=B.float_tables(numeric,DISCOVERY_SCALES,meter)
            cases=P.float_scores(state,f,[1024,2048,4096],meter)
            discovery.append(dict(id=transport['id'],status_counts=state['status_counts'],cases=cases))
            coverage=cases[-1]['coverage']
            for storage in storages:
                values=B.float_storage(storage['program'],tables)
                if any(not math.isfinite(v) or v<=0 for v in values.values()):raise ArithmeticError('finite positive full storage')
                growth=max(math.log2(values[2*X]/values[X]) for X in VALIDATION)
                for shape in shapes:
                    cert=B.certificate(storage['program'],shape,transport['program'],True)
                    record=dict(id=hypothesis_count,transport_id=transport['id'],storage_id=storage['id'],shape=shape)
                    hypothesis_count+=1
                    if cert['pole_excluded']:
                        record.update(status='all_scale_shape_disproved',reason='original core double pole after paid recovery')
                    else:
                        constant=B.fit(values,TRAIN,shape,meter);v=B.float_test(values,VALIDATION,shape,constant,meter)
                        failures=sum(x['status']!='pass' for x in v)
                        record.update(status='finite_validation_failure' if failures else 'finite_survivor_open_uniform_premise',constant=constant,validation=v,observed_tail_growth=growth,
                                      conditional_log_degree=cert['conditional_log_degree'])
                        lane=(transport['program']['theta'],storage['lane'])
                        rank=(failures,Q(cert['conditional_log_degree']),growth,storage['complexity'],-coverage,transport['id'],storage['id'],Q(shape['rho']),Q(shape['log_power']))
                        if lane not in selected or rank<selected[lane][0]:
                            candidate=dict(record,transport_program=transport['program'],storage_program=storage['program'],lane=list(lane),
                                           auxiliary_role='paid-perturbation calibration' if storage['lane']=='transport_error' else 'energy baseline' if storage['lane']=='baseline' else 'unpaid auxiliary construction',
                                           certificate=cert,training_prime_coverage=coverage)
                            selected[lane]=(rank,candidate)
                    json.dump(record,archive);archive.write('\n');status_counts[record['status']]+=1;meter.charge(150)
            print(json.dumps(dict(stage='joint_transport_and_bounds_searched',transport_id=transport['id'],coverage=coverage,
                                 hypotheses=hypothesis_count,operations=meter.operations)),flush=True)
    selections=[v[1] for lane,v in sorted(selected.items(),key=lambda x:(Q(x[0][0]),x[0][1]))]
    write(OUT/'discovery.json',discovery);write(OUT/'selection.json',selections)
    print(json.dumps(dict(stage='all_constructions_and_constants_selected',selected=len(selections),unique_transports=len({r['transport_id'] for r in selections}))),flush=True)
    resources=[]
    with ProcessPoolExecutor(max_workers=2,mp_context=mp.get_context('spawn')) as pool:
        futures=[pool.submit(exact_worker,role,selections,rows) for role in ('producer','checker')]
        for future in as_completed(futures):resources.append(future.result())
    comparisons=0;verified=[];transport_summaries=[]
    by_id={r['id']:r for r in selections}
    for tid in sorted({r['transport_id'] for r in selections}):
        with gzip.open(OUT/('producer-transport-'+str(tid)+'.json.gz'),'rt') as f:p=json.load(f)
        with gzip.open(OUT/('checker-transport-'+str(tid)+'.json.gz'),'rt') as f:c=json.load(f)
        if p['program']!=c['program'] or p['H']!=c['H']:raise ArithmeticError('matching full transport domain')
        for key in VECTORS:
            if len(p['vectors'][key])!=H+1 or len(c['vectors'][key])!=H+1:raise ValueError('complete vector length')
            for a,b in zip(p['vectors'][key],c['vectors'][key]):compare(a,b,meter);comparisons+=1
        if len(p['windows'])!=len(c['windows']) or len(p['assignments'])!=len(c['assignments']):raise ArithmeticError('complete windows and assignments')
        for a,b in zip(p['windows'],c['windows']):
            for key in ('annulus','start','stop','length','sources','destinations'):
                if a[key]!=b[key]:raise ArithmeticError('actual prime/composite window geometry')
            if (a['status']=='accepted')!=(b['status']=='accepted') or (a['status']=='empty')!=(b['status']=='empty'):
                raise ArithmeticError('guard decisions')
            compare(b['mass_residual'],'0',meter);comparisons+=1
        for a,b in zip(p['assignments'],c['assignments']):
            if a[:2]!=b[:2]:raise ArithmeticError('same complete sorted pair assignment')
            compare(a[2],b[2],meter);comparisons+=1
        if len(p['blocks'])!=len(SCALES) or len(c['blocks'])!=len(SCALES):raise ValueError('full block range')
        exponent=Q(rows[tid]['certificate']['energy_error_power'])
        for a,b in zip(p['blocks'],c['blocks']):
            if a['X']!=b['X']:raise ArithmeticError('same dyadic block')
            for key in ('energy_transformed','energy_error','prime_log_work'):compare(a[key],b[key],meter);comparisons+=1
            X=a['X'];cap=25*arb(X).root(exponent.denominator)**exponent.numerator
            if not arb(a['energy_error'])<=cap:raise ArithmeticError('finite recovery envelope check')
        if len(p['controls'])!=len(c['controls']):raise ArithmeticError('all selected storage programs')
        for a,b in zip(p['controls'],c['controls']):
            if a['id']!=b['id'] or set(a['values'])!=set(b['values']):raise ArithmeticError('same complete storage program')
            for X in a['values']:compare(a['values'][X],b['values'][X],meter);comparisons+=1
            if len(a['tests'])!=len(b['tests']):raise ArithmeticError('all recurrence probes')
            for x,y in zip(a['tests'],b['tests']):
                if (x['X'],x['status'])!=(y['X'],y['status']):raise ArithmeticError('independent recurrence decision')
                for key in ('drift','upper_bound'):compare(x[key],y[key],meter);comparisons+=1
            record=by_id[a['id']]
            row=dict(id=a['id'],transport_id=tid,storage_id=record['storage_id'],shape=record['shape'],constant=record['constant'],
                     finite_tests=a['tests'],larger_scale_pass=all(x['status']=='pass' for x in a['tests'] if x['X'] in LARGER),
                     uniform_premise_established=False,whole_signed_bound_proved=False,RH_proved=False)
            verified.append(row)
        transport_summaries.append(dict(transport_id=tid,program=p['program'],assignments=len(p['assignments']),
            window_statuses=dict(Counter(w['reason'] or 'accepted' for w in p['windows'])),
            largest_block=p['blocks'][-1],complete_vectors_independently_verified=True))
    write(OUT/'verified_bounds.json',verified);write(OUT/'verified_transports.json',transport_summaries)
    obligations=[]
    results={r['id']:r for r in verified}
    for record in selections:
        ob=B.proof_obligation(record);ob['finite_verification']=results[record['id']]
        # A failed fixed-C conjecture is closed, not sent back as an open lemma.
        if any(t['status']=='fail' for t in results[record['id']]['finite_tests']):
            ob['status']='finite_counterexample_found';ob['next_search_target']=None
        else:ob['status']='open_uniform_increment'
        obligations.append(ob)
    next_input=dict(schema='joint-transport-control-search-input-v1',status='open',parent_obligation=read(ROOT/INPUT),
        generated_bound_obligations=obligations,generated_transport_obligations=[P.obligation(rows[i]) for i in sorted({r['transport_id'] for r in selections})],
        proof_compilation=read(OUT/'proof_compilation.json'),original_target_and_corrections_retained=True,
        source_horizon_already_observed=524287,new_source_observations=0,
        next_priority='Search for constructions/identities controlling each explicit uniform_increment; do not treat recurrence fitting as its proof',
        unresolved='complete original or transformed signed core control over ALL scales',
        detector_generates_bound_candidates=True,grammar_and_proof_rules_supplied_by_analysts=True,
        all_scale_signed_control_proved=False,whole_signed_bound_proved=False,RH_proved=False)
    write(OUT/'next_search_input.json',next_input)
    total=meter.operations+test_ops+sum(r['operations'] for r in dev.values())+sum(r['resources']['operations'] for r in resources)
    if total>TOTAL_CAP:raise OverflowError('inclusive work cap')
    verify()
    report=dict(status='JOINT_TRANSPORT_AND_CORE_CONTROL_SEARCH_VERIFIED',transport_programs=len(rows),admitted_transports=sum(r['admitted'] for r in rows),
        storage_programs=len(storages),bound_shapes=len(shapes),joint_hypotheses=hypothesis_count,hypothesis_statuses=dict(status_counts),
        selected=len(selections),independent_scalar_comparisons=comparisons,proof_comparisons=proof_comparisons,
        selected_larger_scale_passes=sum(r['larger_scale_pass'] for r in verified),verified_transports=transport_summaries,
        main=stat(meter,start),workers=resources,total_operations=total,source_horizon=H,new_source_observations=0,
        hashes=False,whole_signed_bound_proved=False,RH_proved=False)
    write(OUT/'report.json',report)
    print(json.dumps(report),flush=True)


if __name__=='__main__':main()
