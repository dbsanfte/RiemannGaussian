"""Single immutable obstruction-driven grouping study on already observed data."""
from collections import Counter
from concurrent.futures import ProcessPoolExecutor,as_completed
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
from flint import arb,ctx
import core_arithmetic_grouping as P
import check_core_arithmetic_grouping as C
import centered_product_fibers as SERIAL
from prime_bank_candidates import Meter
from run_core_signed_work import verify as verify_parent

ROOT=Path(__file__).resolve().parent
PARENT=ROOT/'core-signed-work-results/pilot-001'
FEEDBACK=PARENT/'proof-followup-001'
OUT=ROOT/'core-arithmetic-grouping-results/pilot-001'
SCALES=[256,512,1024]
H=4*max(SCALES)-1
TOTAL_CAP=6000000000
RESERVE=4000000
TESTS=['test_core_arithmetic_grouping','test_check_core_arithmetic_grouping']
RECEIPTS=['core_arithmetic_grouping_producer_development.json','core_arithmetic_grouping_checker_development.json']
FILES=['core_arithmetic_grouping.py','check_core_arithmetic_grouping.py','run_core_arithmetic_grouping.py',
    'core_arithmetic_grouping_protocol.txt','CORE_ARITHMETIC_GROUPING_REVIEW_009.txt','CORE_ARITHMETIC_GROUPING_GATES_009.txt',
    'prime_bank_candidates.py','centered_product_fibers.py','candidate10_signed_work_obligation.json']+RECEIPTS+[t+'.py' for t in TESTS]


def read(p):return json.loads(Path(p).read_text())
def write(p,data):
    with Path(p).open('x') as f:json.dump(data,f,indent=2,sort_keys=True);f.write('\n')


def verify():
    verify_parent(PARENT)
    for name in read(FEEDBACK/'source_files.json'):
        if (ROOT/name).read_bytes()!=(FEEDBACK/'source_snapshot'/name).read_bytes():raise ValueError('changed proof parent '+name)
    if (ROOT/'candidate10_signed_work_obligation.json').read_bytes()!=(FEEDBACK/'next_search_input.json').read_bytes():
        raise ValueError('published complete current target')
    if OUT.exists():
        for name in read(OUT/'source_files.json'):
            if (ROOT/name).read_bytes()!=(OUT/'source_snapshot'/name).read_bytes():raise ValueError('changed study source '+name)


def limits():
    _,hard=resource.getrlimit(resource.RLIMIT_AS)
    resource.setrlimit(resource.RLIMIT_AS,(4*1024**3,hard))


def statistics(m,start):
    return dict(operations=m.operations,peak_cells=m.peak_cells,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
                elapsed_seconds=time.monotonic()-start)


def float_job(rows,coeff):
    limits();start=time.monotonic();m=Meter(1500000000,3600);out=[]
    for row in rows:
        cases=[]
        for X in SCALES:
            label=P.labels(row['program'],X,m)
            result=P.grouped_float(coeff[:4*X],label,X,m)
            result.pop('matrix');result['X']=X;cases.append(result)
        if any(not math.isfinite(c['sum_abs']) or c['sum_abs']<=0 for c in cases):raise ArithmeticError('finite positive discovery majorant')
        slopes=[math.log(b['sum_abs']/a['sum_abs'],2) for a,b in zip(cases,cases[1:])]
        out.append(dict(program_id=row['id'],cases=cases,observed_growth_slopes=slopes,worst_observed_growth=max(slopes),
            finite_data_only=True,uniform_bound_proved=False))
    return dict(results=out,resources=statistics(m,start))


def exact_job(kind,row,coeff):
    limits();ctx.prec=192;start=time.monotonic();m=Meter(1500000000,3600);X=max(SCALES)
    label=(P.labels(row['program'],X,m) if kind=='producer' else C.evaluate_labels(row['program'],X,m))
    values=[arb(v) for v in coeff]
    result=(P.grouped_arb(values,label,X,m) if kind=='producer' else C.grouped_literal(values,label,X,meter=m))
    encoded={}
    for key,value in result.items():
        if key=='group_matrix':encoded[key]=[[SERIAL.encode(v) for v in r] for r in value]
        elif isinstance(value,arb):encoded[key]=SERIAL.encode(value)
        else:encoded[key]=value
    encoded.update(program_id=row['id'],X=X,backend=kind,resources=statistics(m,start))
    path=OUT/(kind+'-program-'+str(row['id'])+'.json');write(path,encoded)
    return dict(path=path.name,resources=encoded['resources'])


def main():
    start=time.monotonic();ctx.prec=192;verify()
    if OUT.exists():raise FileExistsError('a study directory is one terminal attempt; do not restart')
    dev={name:read(ROOT/name) for name in RECEIPTS}
    for receipt in dev.values():
        if not receipt['runs'] or receipt['runs'][-1]['returncode'] or receipt['operations']!=sum(r['operations'] for r in receipt['runs']):
            raise ValueError('passed owned checks with cumulative cost')
    OUT.mkdir(parents=True);(OUT/'source_snapshot').mkdir()
    for name in FILES:(OUT/'source_snapshot'/name).write_bytes((ROOT/name).read_bytes())
    write(OUT/'source_files.json',FILES)
    spec=dict(schema='obstruction-driven-arithmetic-grouping-v1',scales=SCALES,coefficient_horizon=H,
        source_horizon_already_observed=524287,new_source_observations=0,
        numerical_scope='exploratory observables on previously verified coefficients; no fresh holdout, no fitted bound constant',
        target=dict(eta='1',rho='1/2',filter='identity',parent_program_id=6),
        grammar='17 valuation-stripping bases; failed prime-frontier proof routes activate11 generic post-maps each',
        post_maps=['remove_largest_once','remove_smallest_once','remove_largest_all','roots2,3,6','quotientsX^(1/3),X^(1/2)','residues2,3,6'],
        adaptive_rule='proved baseline obstruction -> enumerate every fixed post-map; no model calls or score-driven mutations',
        proof_gates=['complete prime exponent singleton frontier','eventual one-bucket restatement','prime-only sublinear-width coarsening'],
        ranking=['nontrivial complete partition on every observed scale','worst observed doubling growth of grouped absolute sum','complexity','ordinal'],
        selection='one per prime-cofactor/fractional-interval/residue lane; no ties selected by constants',
        numerical_methods=['float streaming symmetric row updates for discovery','Arb streaming row updates','independent literal all ordered Arb pairs and scalar prefix work'],
        exact_scope='selected complete matrices atX1024, after exploratory selection; this is verification on known data',
        partition_reuse='only identical canonical partitions at these finite scales share evaluation; no uniform alias claim',
        work_limit=TOTAL_CAP,metadata_reserve=RESERVE,main_limit=1200000000,worker_limit=1500000000,
        workers=2,worker_seconds=3600,main_seconds=14400,aggregate_memory_limit=16*1024**3,
        per_worker_memory_limit=4*1024**3,hashes=False,development=dev,
        all_scale_signed_control_proved=False,whole_signed_bound_proved=False,RH_proved=False)
    write(OUT/'protocol.json',spec)
    m=Meter(1200000000,14400);m.charge(RESERVE)
    source=read(PARENT/'source_program.json');z=(arb(2)/3).zeta()
    Ru=arb(9)/2*((arb(4)/3).zeta()/(z*z)-1/z);m.charge(1000)
    if not Ru>0 or not Ru.overlaps(arb(read(PARENT/'producer_cases.json')['R_u'])):raise ArithmeticError('complete certified residue')
    frontier=P.prime_frontier_certificate(source,Ru);rows=P.generate(frontier,m)
    write(OUT/'prime_frontier_certificate.json',frontier);write(OUT/'programs.json',rows)
    print(json.dumps(dict(stage='grammar_saved',programs=len(rows),proof_gates=dict(Counter(r['proof_gate'] for r in rows)))),flush=True)
    # One combined frozen suite; its work is included in the study total.
    ts=time.monotonic();test=subprocess.run([sys.executable,'-B','-m','unittest']+TESTS,cwd=ROOT,capture_output=True,text=True)
    test_ops=sum(map(int,re.findall(r'operations=(\d+)',test.stdout)))
    write(OUT/'frozen_tests.json',dict(returncode=test.returncode,stdout=test.stdout,stderr=test.stderr,operations=test_ops,elapsed_seconds=time.monotonic()-ts))
    if test.returncode:raise RuntimeError('frozen combined suite failed')
    # Check every admitted label at every scale independently before source responses.
    signatures=[];representatives=[];mapping={};structure=[]
    for row in rows:
        if row['proof_gate']!='open_grouped_arithmetic_premise':continue
        signature=[];counts=[]
        for X in SCALES:
            first=P.labels(row['program'],X,m);second=C.evaluate_labels(row['program'],X,m)
            if first!=second:raise ArithmeticError('independent complete partition interpretation')
            values,ids=P.compact_labels(first);signature.append(ids.tobytes());counts.append(len(values));m.charge(4*X)
        signature=tuple(signature)
        duplicate=next((i for i,s in enumerate(signatures) if s==signature),None)
        if duplicate is None:
            signatures.append(signature);representatives.append(row);representative=row['id']
        else:representative=representatives[duplicate]['id']
        mapping[row['id']]=representative
        structure.append(dict(program_id=row['id'],group_counts=counts,finite_evaluation_representative=representative,
            all_observed_partitions_nontrivial=min(counts)>1,uniform_equivalence_claimed=False))
    write(OUT/'partition_verification.json',structure)
    print(json.dumps(dict(stage='all_partitions_checked',admitted=len(structure),finite_distinct=len(representatives),operations=m.operations)),flush=True)
    coeff=None
    with gzip.open(PARENT/'producer_vectors.jsonl.gz','rt') as stream:
        for line in stream:
            row=json.loads(line);m.charge(5*len(row['values']))
            if row['name']=='core':coeff=row['values'][:H+1];break
    if coeff is None or len(coeff)!=H+1 or not arb(coeff[0]).is_zero():raise ValueError('complete verified core prefix')
    write(OUT/'source_prefix.json',dict(parent=str(PARENT.relative_to(ROOT)),H=H,values=coeff))
    float_coeff=[float(arb(v)) for v in coeff];m.charge(10*len(coeff));worker_resources=[];numerics={}
    with ProcessPoolExecutor(max_workers=2,mp_context=mp.get_context('spawn')) as pool:
        futures=[pool.submit(float_job,representatives[j::2],float_coeff) for j in range(2)]
        for future in as_completed(futures):
            result=future.result();worker_resources.append(result['resources'])
            for row in result['results']:numerics[row['program_id']]=row
            print(json.dumps(dict(stage='discovery_worker_complete',count=len(result['results']),resources=result['resources'])),flush=True)
    structures={r['program_id']:r for r in structure};records=[]
    for row in rows:
        if row['id'] not in mapping:continue
        result=dict(numerics[mapping[row['id']]],program_id=row['id'],finite_evaluation_representative=mapping[row['id']],
                    lane=row['lane'],complexity=row['complexity'],partition=structures[row['id']])
        records.append(result)
    write(OUT/'discovery.json',records)
    selections=[]
    for lane in ('prime_cofactor','fractional_interval','residue'):
        eligible=[r for r in records if r['lane']==lane and r['partition']['all_observed_partitions_nontrivial']]
        if not eligible:continue
        best=min(eligible,key=lambda r:(r['worst_observed_growth'],r['complexity'],r['program_id']))
        selections.append(dict(rows[best['program_id']],discovery=best))
    write(OUT/'selection.json',selections)
    print(json.dumps(dict(stage='selection_saved',selected=[dict(id=r['id'],program=r['program'],growth=r['discovery']['worst_observed_growth']) for r in selections])),flush=True)
    # Exact methods now verify the new selected GROUPINGS; source data is unchanged.
    jobs=[]
    with ProcessPoolExecutor(max_workers=2,mp_context=mp.get_context('spawn')) as pool:
        futures=[pool.submit(exact_job,kind,row,coeff) for row in selections for kind in ('producer','checker')]
        for future in as_completed(futures):
            result=future.result();worker_resources.append(result['resources']);jobs.append(result)
            print(json.dumps(dict(stage='exact_worker_complete',**result)),flush=True)
    verified=[];comparisons=0
    for row in selections:
        producer=read(OUT/('producer-program-'+str(row['id'])+'.json'));checker=read(OUT/('checker-program-'+str(row['id'])+'.json'))
        if producer['group_labels']!=checker['group_labels'] or not checker['identity_verified']:raise ArithmeticError('verified complete group domain')
        def compare(a,b):
            nonlocal comparisons
            x,y=arb(a),arb(b);m.charge(20);comparisons+=1
            if not SERIAL.tight(x) or not SERIAL.tight(y) or not x.overlaps(y):raise ArithmeticError('independent complete group mismatch')
        for ra,rb in zip(producer['group_matrix'],checker['group_matrix']):
            if len(ra)!=len(rb):raise ValueError('matrix width')
            for a,b in zip(ra,rb):compare(a,b)
        for key in ('signed_total','sum_abs','positive_sum','negative_sum','diagonal_coefficient_sum'):compare(producer[key],checker[key])
        compare(producer['signed_total'],checker['scalar_total'])
        if not abs(arb(checker['identity_residual']))<=arb(2)**-65:raise ArithmeticError('tight scalar identity residual')
        finite=row['discovery']['cases'][-1]
        if abs(float(arb(producer['sum_abs']))-finite['sum_abs'])>1e-8*(1+abs(finite['sum_abs'])):
            raise ArithmeticError('exploratory rounding inconsistent with exact evaluation')
        verified.append(dict(program_id=row['id'],group_count=len(producer['group_labels']),
            signed_total=producer['signed_total'],sum_abs=producer['sum_abs'],positive_sum=producer['positive_sum'],
            negative_sum=producer['negative_sum'],diagonal_coefficient_sum=producer['diagonal_coefficient_sum'],
            exact_finite_grouping_verified=True,uniform_group_bound_proved=False))
    write(OUT/'verified_groupings.json',verified)
    prior=read(ROOT/'candidate10_signed_work_obligation.json')
    obligations=[P.obligation(row) for row in selections]
    next_input=dict(schema='obstruction-driven-grouped-work-input-v1',status='open',target=prior['target'],
        prior_input='candidate10_signed_work_obligation.json',source_mass_profile=prior['source_mass_profile'],
        generated_grouped_obligations=obligations,prior_generated_pair_obligations=prior['generated_pair_obligations'],
        generated_prime_frontier_guard=frontier,selection=selections,verified_finite_groupings=verified,
        original_corrections_and_recovery_retained=True,source_horizon_now_observed=524287,
        discovery_data_status='known coefficients; newly computed grouped observables; no final extrapolation claim',
        unresolved='uniform signed estimates for generated groups, or a better exact transport with separately paid leftovers',
        next_priority='synthesize cross-cofactor transports and full complement bounds; any fixed polylog degree suffices for cofinal recovery',
        all_scale_signed_control_proved=False,whole_signed_bound_proved=False,RH_proved=False)
    write(OUT/'next_search_input.json',next_input)
    total=m.operations+sum(r['operations'] for r in worker_resources)+test_ops+sum(r['operations'] for r in dev.values())
    if total>TOTAL_CAP:raise OverflowError('inclusive complete work cap')
    verify()
    report=dict(status='ARITHMETIC_GROUPING_SEARCH_AND_COMPLETE_VERIFICATION_FINISHED',programs=len(rows),
        proof_gates=dict(Counter(r['proof_gate'] for r in rows)),admitted=len(records),finite_distinct_evaluations=len(representatives),
        selected=len(selections),exact_scalar_comparisons=comparisons,verified=verified,
        numerical_source_horizon=H,new_source_observations=0,all_scale_bounds_proved=0,
        main=statistics(m,start),workers=worker_resources,total_operations=total,
        tests_passed=11,whole_signed_bound_proved=False,RH_proved=False)
    write(OUT/'report.json',report)
    print(json.dumps(report),flush=True)


if __name__=='__main__':main()
