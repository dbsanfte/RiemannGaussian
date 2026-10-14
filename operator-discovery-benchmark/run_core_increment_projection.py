"""Proof-selected reductions of the current detector-generated open increments."""
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
import core_increment_projection as P
import check_core_increment_projection as C
import check_core_prime_transport as TRANSPORT_CHECK
import centered_product_fibers as SERIAL
from prime_bank_candidates import Meter
from run_core_prime_transport import verify as verify_parent

ROOT=Path(__file__).resolve().parent
PARENT=ROOT/'core-prime-transport-results/pilot-001'
INPUT='candidate10_transport_control_obligation.json'
OUT=ROOT/'core-increment-projection-results/pilot-001'
SCALES=[2**k for k in range(15)]
H=32767
TESTS=['test_core_increment_projection','test_check_core_increment_projection']
RECEIPTS=['core_increment_projection_producer_development.json','core_increment_projection_checker_development.json']
FILES=['core_increment_projection.py','check_core_increment_projection.py','run_core_increment_projection.py',
       'core_increment_projection_protocol.txt','CORE_INCREMENT_PROJECTION_REVIEW_013.txt',
       'CORE_SELECTED_GROUPING_REVIEW_010.txt','CORE_PRIME_COMPOSITE_TRANSPORT_REVIEW_011.txt',
       'check_core_control_synthesis.py','check_core_prime_transport.py','centered_product_fibers.py','prime_bank_candidates.py',INPUT]+RECEIPTS+[s+'.py' for s in TESTS]
PROOF_KEYS=('detail_constant','detail_power','raw_log_degree','cofinal_recovery','bounded_detail','bounded_detail_constant','effective_detail_log_degree')
MAIN_CAP=150000000
WORKER_CAP=500000000
TOTAL_CAP=1200000000
RESERVE=3000000


def read(path):return json.loads(Path(path).read_text())
def write(path,value):
    with Path(path).open('x') as f:json.dump(value,f,indent=2,sort_keys=True);f.write('\n')
def limits():
    _,hard=resource.getrlimit(resource.RLIMIT_AS);resource.setrlimit(resource.RLIMIT_AS,(4*1024**3,hard))
def stat(m,start):
    return dict(operations=m.operations,peak_cells=m.peak_cells,elapsed_seconds=time.monotonic()-start,
                peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)


def parents():
    verify_parent()
    if (ROOT/INPUT).read_bytes()!=(PARENT/'publication-001/next_search_input.json').read_bytes():raise ValueError('published complete open input')
    prior=read(ROOT/INPUT)
    if prior['whole_signed_bound_proved'] or prior['RH_proved']:raise ValueError('unresolved actual target')
    selection=read(PARENT/'selection.json')
    mapping={'control_'+str(r['transport_id'])+'_'+str(r['storage_id'])+'_'+r['shape']['rho']+'_'+r['shape']['log_power']:r for r in selection}
    for ob in prior['generated_bound_obligations']:
        r=mapping[ob['id']]
        if r['transport_program']!=ob['transport_program'] or r['storage_program']!=ob['storage_program'] or r['shape']!=ob['shape']:
            raise ValueError('complete selected AST binding')
    return prior,mapping


def verify():
    parents()
    for name in read(OUT/'source_files.json'):
        if (ROOT/name).read_bytes()!=(OUT/'source_snapshot'/name).read_bytes():raise ValueError('changed frozen source '+name)


def source_binding(prior,meter):
    source=read(PARENT/'source_program.json');witness=read(PARENT/'pole_witness.json')
    if witness['source_terms']!=source['terms'] or witness['source_pole']['minimum_dyadic_energy_log_degree']!=2:
        raise ValueError('actual original critical pole binding')
    z=(arb(2)/3).zeta();Ru=arb(9)/2*((arb(4)/3).zeta()/(z*z)-1/z);meter.charge(1000)
    checked=[]
    for ob in prior['generated_bound_obligations']:
        certificate=TRANSPORT_CHECK.verify_recovery(ob['transport_program'],source,Ru,meter)
        if not certificate['verified'] or not certificate['cofinal_recovery']:raise ValueError('actual full source and paid transform')
        checked.append(dict(parent_obligation=ob['id'],actual_four_mode_source_verified=True,transport_scope_verified=True))
    bridge=P.source_holomorphy_bridge(source,{'beta':arb(9)/2,'-beta':-arb(9)/2,'-R_u':-Ru},meter)
    if not bridge['verified']:raise ValueError('complete source RH bridge')
    return dict(verified=True,source_program=source,residue=str(Ru),coefficient_constant='37/2',source_holomorphy_RH_bridge=bridge,
        local_majorants='nu0 first valuation |t-2|<=2; later (1-t)^2*t^(e-2)<=1; every other complete local mode has modulus<=1, 0<t<1',
        complete_source_majorant='|f(n)|<=(3beta+5)d2(n)=(37/2)d2(n)',
        transported_majorants='capacity checked transport has |g(n)|<=|f(n)| and |f(n)-g(n)|<=|f(n)| pointwise',
        proofs=['CORE_SELECTED_GROUPING_REVIEW_010.txt','CORE_PRIME_COMPOSITE_TRANSPORT_REVIEW_011.txt','CORE_INCREMENT_PROJECTION_REVIEW_013.txt'],
        checked_actual_inputs=checked,original_core_pole_verified=True,whole_signed_bound_proved=False,RH_proved=False)


def worker(role,selected,mapping):
    limits();ctx.prec=192;start=time.monotonic();meter=Meter(WORKER_CAP,3600);files=[];loaded_tid=None;source=None
    parent_names=list(dict.fromkeys(row['parent_obligation'] for row in selected))
    for index,parent in enumerate(parent_names):
        record=mapping[parent];tid=record['transport_id']
        if loaded_tid!=tid:
            path=PARENT/(role+'-transport-'+str(tid)+'.json.gz')
            with gzip.open(path,'rt') as f:old=json.load(f)
            source=dict(H=H,**{k:[arb(v) for v in old['vectors'][k]] for k in ('g','G','Bg','D')})
            meter.charge(20*(H+1));loaded_tid=tid
        program=record['storage_program']
        prepared=P.prepare(source,program,meter) if role=='producer' else C.prepare(source,program,meter)
        cases=[]
        for row in selected:
            if row['parent_obligation']!=parent:continue
            blocks=[]
            for X in SCALES:
                blocks.append(P.project(prepared,X,row['mesh_power'],meter) if role=='producer' else C.project(prepared,X,row['mesh_power'],meter))
            cases.append(dict(program_id=row['id'],mesh_power=row['mesh_power'],lane=row['lane'],blocks=blocks))
        name=role+'-parent-'+str(index)+'.json.gz'
        payload=dict(parent_obligation=parent,transport_id=tid,storage_program=program,H=H,U=prepared['U'],Q=prepared['Q'],weight=prepared['weight'],cases=cases)
        with gzip.open(OUT/name,'xt',compresslevel=1) as f:json.dump(SERIAL.serialize(payload),f)
        files.append(name);meter.charge(30*(H+1))
        print(json.dumps(dict(stage=role+'_projection_checked',parent_index=index,cases=len(cases),operations=meter.operations)),flush=True)
    result=dict(files=files,resources=stat(meter,start));write(OUT/(role+'_resources.json'),result)
    return result


def compare(a,b,meter):
    x,y=arb(a),arb(b);meter.charge(20)
    if not SERIAL.tight(x) or not SERIAL.tight(y) or not x.overlaps(y):raise ArithmeticError('independent tight scalar disagreement')


def main():
    limits();ctx.prec=192;start=time.monotonic();prior,mapping=parents()
    if OUT.exists():raise FileExistsError('one terminal attempt, no retry')
    dev={name:read(ROOT/name) for name in RECEIPTS}
    for r in dev.values():
        if not r['runs'] or r['runs'][-1]['returncode'] or r['operations']!=sum(x['operations'] for x in r['runs']):raise ValueError('passed cumulative owned development')
    OUT.mkdir(parents=True);(OUT/'source_snapshot').mkdir()
    for name in FILES:(OUT/'source_snapshot'/name).write_bytes((ROOT/name).read_bytes())
    write(OUT/'source_files.json',FILES)
    write(OUT/'protocol.json',dict(schema='proof-guided-increment-projection-v1',parent_input=INPUT,
        grammar=dict(mesh_powers=list(P.MESH_POWERS),storage_inputs='every selected open storage AST from published parent',coarse_operator='orthogonal complete-cell mean of each full storage channel'),
        source_scope='verified complete source/transport supplies coefficient majorants; generic projection identity alone is conditional',
        selection='largest nested cell exponent paid within logdegree2; largest with any fixed polylog energy cost; largest with separately verified source-specific analytic RH bridge',
        numerical_selection=False,fitting=False,source_generation=False,source_horizon_already_observed=524287,H=H,scales=SCALES,
        data_scope='new exact projection observables on previously verified source and transports; no fresh source holdout',
        independent_methods=['prefix moments including derivative moments0,1,2','literal cell means, centered squares and local edge sums'],
        proofs=['orthogonal energy split','complete source derivative majorants','fractional mesh power accounting','nested-projection dominance','zero-mean Mellin pole preservation','weak-fact composite countermodels'],
        workers=2,main_cap=MAIN_CAP,worker_cap=WORKER_CAP,total_cap=TOTAL_CAP,metadata_reserve=RESERVE,
        process_memory_bytes=4*1024**3,aggregate_memory_limit=16*1024**3,main_seconds=14400,worker_seconds=3600,
        development=dev,hashes=False,whole_signed_bound_proved=False,RH_proved=False))
    meter=Meter(MAIN_CAP,14400);meter.charge(RESERVE)
    binding=source_binding(prior,meter);write(OUT/'source_majorant_binding.json',binding)
    rows=P.generate(prior['generated_bound_obligations'],meter)
    for row in rows:
        independent=C.certificate(row['storage_program'],row['mesh_power'],meter)
        if any(row['certificate'][key]!=independent[key] for key in PROOF_KEYS):raise ArithmeticError('independent all-scale detail certificate')
        row['certificate']['coefficient_majorant_premise_verified']=True
        row['certificate']['source_binding_file']='source_majorant_binding.json'
        row['coarse_pole_guard']=P.coarse_pole_guard(row,binding['original_core_pole_verified'],meter)
        row['analytic_recovery']=P.analytic_recovery(row,binding['source_holomorphy_RH_bridge'],meter)
        if not row['certificate']['cofinal_recovery'] and row['analytic_recovery']['admitted']:
            row['status']='analytic_recovery_open_coarse'
    chosen=P.proof_select(rows);write(OUT/'programs.json',rows);write(OUT/'selection.json',chosen)
    weak={ob['id']:P.weak_fact_countermodels(ob['storage_program'],meter) for ob in prior['generated_bound_obligations']}
    write(OUT/'weak_fact_countermodels.json',weak)
    test_start=time.monotonic();test=subprocess.run([sys.executable,'-B','-m','unittest']+TESTS,cwd=ROOT,capture_output=True,text=True)
    test_ops=sum(map(int,re.findall(r'operations=(\d+)',test.stdout)))
    write(OUT/'frozen_tests.json',dict(returncode=test.returncode,stdout=test.stdout,stderr=test.stderr,operations=test_ops,elapsed_seconds=time.monotonic()-test_start))
    if test.returncode:raise RuntimeError('combined frozen suite failed')
    print(json.dumps(dict(stage='proof_grammar_frozen',programs=len(rows),selected=len(chosen),statuses=dict(Counter(r['status'] for r in rows)))),flush=True)
    workers=[]
    with ProcessPoolExecutor(max_workers=2,mp_context=mp.get_context('spawn')) as pool:
        futures=[pool.submit(worker,role,chosen,mapping) for role in ('producer','checker')]
        for future in as_completed(futures):workers.append(future.result())
    count=0;verified=[];path_status=Counter();guarded={row['id']:row for row in chosen};old_tid=None;old_controls=None
    for index,parent in enumerate(dict.fromkeys(r['parent_obligation'] for r in chosen)):
        with gzip.open(OUT/('producer-parent-'+str(index)+'.json.gz'),'rt') as f:p=json.load(f)
        with gzip.open(OUT/('checker-parent-'+str(index)+'.json.gz'),'rt') as f:c=json.load(f)
        for key in ('parent_obligation','storage_program','H','transport_id'):
            if p[key]!=c[key]:raise ArithmeticError('matching complete projection input')
        if old_tid!=p['transport_id']:
            with gzip.open(PARENT/('producer-transport-'+str(p['transport_id'])+'.json.gz'),'rt') as f:old=json.load(f)
            old_controls={r['id']:r['values'] for r in old['controls']};old_tid=p['transport_id']
        old_values=old_controls[mapping[parent]['id']]
        compare(p['weight'],c['weight'],meter);count+=1
        for key in ('U','Q'):
            if len(p[key])!=H+1 or len(c[key])!=H+1:raise ValueError('complete transformed channel')
            for a,b in zip(p[key],c[key]):compare(a,b,meter);count+=1
        if len(p['cases'])!=len(c['cases']):raise ArithmeticError('all selected mesh cases')
        for a,b in zip(p['cases'],c['cases']):
            if a['program_id']!=b['program_id'] or a['mesh_power']!=b['mesh_power'] or len(a['blocks'])!=len(SCALES) or len(b['blocks'])!=len(SCALES):
                raise ArithmeticError('identical full projection support')
            row=guarded[a['program_id']];cert=row['certificate'];power=Q(cert['detail_power']);C0=P.real(cert['detail_constant'])
            for x,y in zip(a['blocks'],b['blocks']):
                if x['X']!=y['X'] or x['L']!=y['L'] or len(x['cell_means'])!=len(y['cell_means']):raise ArithmeticError('same complete cells')
                for key in ('full_storage','coarse_storage','detail_storage','path_bound','identity_residual'):
                    compare(x[key],y[key],meter);count+=1
                compare(x['full_storage'],old_values[str(x['X'])],meter);count+=1
                for side in (x,y):
                    compare(side['identity_residual'],'0',meter);count+=1;path_status[side['path_comparison']]+=1
                    if side['path_comparison']=='fail':raise ArithmeticError('variance exceeds proved path bound')
                for u,v in zip(x['cell_means'],y['cell_means']):
                    if (u['start'],u['stop'])!=(v['start'],v['stop']):raise ArithmeticError('complete cell endpoints')
                    for key in ('U_mean','Q_mean'):compare(u[key],v[key],meter);count+=1
                X=x['X'];cap=C0*arb(X).root(power.denominator)**power.numerator*X.bit_length()**3
                if not arb(x['detail_storage'])<=cap or not arb(y['detail_storage'])<=cap:raise ArithmeticError('complete finite detail envelope')
            last=a['blocks'][-1]
            verified.append(dict(program_id=row['id'],parent_obligation=parent,mesh_power=row['mesh_power'],lane=row['lane'],
                largest_X=last['X'],largest_L=last['L'],largest_coarse_storage=last['coarse_storage'],largest_detail_storage=last['detail_storage'],
                largest_full_storage=last['full_storage'],exact_full_split_verified=True,uniform_detail_bound_proved=True,
                detail_cofinally_paid=cert['cofinal_recovery'],analytic_recovery_admitted=row['analytic_recovery']['admitted'],full_coarse_bound_proved=False))
    write(OUT/'verified_projections.json',verified)
    obligations=[]
    for row in chosen:
        ob=P.obligation(row);ob['coarse_pole_guard']=row['coarse_pole_guard'];ob['actual_source_majorant_verified']=True
        ob['weak_fact_scope_guard']='all weak_fact_countermodels satisfy prime removal and coefficient bounds but have coarse energy at least cX; additional actual-source cancellation is required'
        obligations.append(ob)
    next_input=dict(schema='proof-guided-projected-increment-input-v1',status='open',parent_obligation=prior,
        source_majorant_binding=binding,generated_projected_obligations=obligations,
        selection_uses_proof_cost_and_nested_projection=True,numerical_fit_or_ranking=False,
        new_unconditional_scope='complete local variation uniformly paid for every dyadic scale; full signed means remain open',
        next_priority='Search genuine complete-source identities controlling the explicit coarse mean correlations; weak majorants plus prime removal are insufficient',
        analytic_recovery_branch='r2/3 has unpaid energy detail but detail Mellin holomorphyRe>1/3; cofinal full coarseS implies source holomorphy and then RH by the checked source-specific bridge; no unproved coarse bound or original critical moment is supplied',
        original_target_and_corrections_retained=True,source_horizon_already_observed=524287,new_source_observations=0,
        all_scale_signed_control_proved=False,whole_signed_bound_proved=False,RH_proved=False)
    write(OUT/'next_search_input.json',next_input)
    total=meter.operations+test_ops+sum(r['operations'] for r in dev.values())+sum(r['resources']['operations'] for r in workers)
    if total>TOTAL_CAP:raise OverflowError('inclusive work cap')
    verify()
    report=dict(status='PROOF_GUIDED_INCREMENT_PROJECTION_VERIFIED',generated_programs=len(rows),selected=len(chosen),
        certificate_statuses=dict(Counter(r['status'] for r in rows)),independent_scalar_comparisons=count,
        path_comparisons=dict(path_status),uniform_detail_certificates=len(chosen),uniform_coarse_bounds_proved=0,
        weak_countermodel_instances=sum(map(len,weak.values())),actual_core_conjectures_disproved=0,
        main=stat(meter,start),workers=workers,total_operations=total,source_horizon=H,new_source_observations=0,
        whole_signed_bound_proved=False,RH_proved=False)
    write(OUT/'report.json',report);print(json.dumps(report),flush=True)


if __name__=='__main__':main()
