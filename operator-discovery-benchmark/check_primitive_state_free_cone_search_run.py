"""Independent audit of bounded proposal records and an exact affine endpoint.

The published chart/source license is hash-bound without new elimination. Trace
checks establish record consistency, not numerical search or gradient correctness.
"""
import argparse
import contextvars
import ast
import json
import math
from pathlib import Path
import re
import time
import check_primitive_state_free_cone_search as CORE
import check_primitive_state_solver_trace_run as ORIGINAL

ROOT=Path(__file__).resolve().parent
path_under=ORIGINAL.path_under
_IO_BUDGET=contextvars.ContextVar('free_cone_search_archive_io_budget',default=None)


def read(path,cap=8388608):
    size=Path(path).stat().st_size;require(size<=cap,'bounded controlled artifact read')
    meter=_IO_BUDGET.get()
    if meter is not None:meter.charge(2*(size//64+1),cells=size//64+1)
    return ORIGINAL.read(path,cap)


def sha(path):
    size=Path(path).stat().st_size;meter=_IO_BUDGET.get()
    if meter is not None:meter.charge(size//64+1)
    return ORIGINAL.sha(path)
require=CORE.require
FLAGS=dict(CORE.FLAGS)
PARENT=CORE.PARENT
TAPE='cancellation-arithmetic-results/primitive-state-exact-row-basis-probe-002/jobs'
CACHE=CORE.CACHE;BASIS=CORE.BASIS;PROJECTION=CORE.PROJECTION
LIMITS=dict(cooperative_seconds=900,max_work=450000000,materialization_operations=50000000,proposal_operations=100000000,endpoint_operations=20000000,max_cache_bytes=134217728,max_tape_bytes=33554432,max_receipt_bytes=8388608,max_metadata_bytes=65536,max_protocol_bytes=65536,max_live_cells=4000000,max_fill_cells=20000000,max_audit_cells=60000000,max_coefficient_bits=4096,binding_byte_multiplier=4,source_byte_multiplier=12,metadata_work_reserve=1048576)
PARALLEL=dict(workers=1,worker_memory_bytes=3*1024**3,memory_budget_bytes=3*1024**3,timeout_seconds=1800,max_jobs=1,max_result_bytes=65536)
TESTS=['test_primitive_state_free_cone_search','test_check_primitive_state_free_cone_search','test_run_primitive_state_free_cone_search','test_check_primitive_state_free_cone_search_run']
INPUTS=['cancellation-arithmetic-results/publication-015/manifest.json','cancellation-arithmetic-results/publication-016/manifest.json','cancellation-arithmetic-results/publication-016/report.json','cancellation-arithmetic-results/publication-017/manifest.json','cancellation-arithmetic-results/publication-017/report.json','primitive_state_free_cone_search_resource_scope.txt','primitive_state_free_coordinate_search_analysis_v1.txt',PARENT+'/independent_verification.json',PARENT+'/receipt.json',PARENT+'/jobs/restoration.json',PARENT+'/jobs/check.json',PARENT+'/jobs/restoration-job.json',CACHE,BASIS,PROJECTION]



def scope(value):
    require(type(value)is dict,'explicit scoped object')
    for k in FLAGS:
        if k in value:require(value[k]is False,'no free_cone_search theorem admission '+k)


def source_names():
    pending=['run_primitive_state_free_cone_search','check_primitive_state_free_cone_search_run',*TESTS];seen=set()
    while pending:
        n=pending.pop();p=ROOT/(n+'.py')
        if n in seen or not p.is_file():continue
        seen.add(n)
        for node in ast.walk(ast.parse(p.read_text())):
            if isinstance(node,ast.Import):pending.extend(a.name.split('.')[0] for a in node.names)
            elif isinstance(node,ast.ImportFrom) and node.module:pending.append(node.module.split('.')[0])
    return sorted(n+'.py' for n in seen)


def parent_protocol_license(license):
    bindings=license.bindings;summary=license.summary
    names=[CACHE,BASIS,PROJECTION,PARENT+'/jobs/restoration.json',PARENT+'/jobs/check.json',PARENT+'/jobs/restoration-job.json',PARENT+'/independent_verification.json',PARENT+'/receipt.json']
    return dict(publication='publication-017',publication_report_hash=bindings[CORE.REPORT],parent_review_hash=bindings[PARENT+'/independent_verification.json'],normalized_basis_hash=summary['normalized_basis_hash'],rank=summary['rank'],free_count=summary['free_count'],original_variables=summary['original_variables'],original_rows=summary['original_rows'],projected_variables=summary['projected_variables'],parent_projected_hash=summary['parent_projected_hash'],initial_free_hash=summary['parent_free_hash'],input_file_hashes={name:bindings[name] for name in names})


def verify_protocol(value,license):
    import importlib.metadata
    expected=dict(schema='primitive-state-free-cone-search-run-v1',parent_license=license,limits=LIMITS,parallel=PARALLEL,tests=TESTS,precision=CORE.PRECISION,search=CORE.SEARCH,seed_rule=CORE.SEED,phases=['materialization','proposal','exact_endpoint'],versions={name:importlib.metadata.version(name) for name in ('mpmath','numpy')},one_fixed_seed=True,no_source_rebuild_or_new_elimination=True,no_precision_retry=True,original_objective_preserved=False,optimization_result=False,all_original_equalities_signs_and_PSD_required=True,endpoint_checker_full_elimination_replay=False,**FLAGS)
    require(value==expected,'exact fixed mixed-precision search protocol')


def verify_inventory(directory,receipt):
    require(type(receipt.get('files_sha256'))is dict,'complete free_cone_search terminal inventory');scope(receipt)
    actual={str(p.relative_to(directory)) for p in directory.rglob('*') if p.is_file() and p.relative_to(directory).parts[0]!='frozen_source' and str(p.relative_to(directory)) not in ('receipt.json','independent_verification.json')}
    require(actual==set(receipt['files_sha256']),'complete terminal file inventory')
    rootfiles={'protocol.json','source_seal.json','input.json','seal.json','run_started.json','tests.json','execution.json'}
    jobfiles={'search-job.json','progress.json','map.json','proposal.json','endpoint.json','check.json'}
    for n,h in receipt['files_sha256'].items():
        p=path_under(directory,n);require(sha(p)==h,'terminal free_cone_search file binding '+n)
        if n in rootfiles:cap=65536
        else:
            require(n.startswith('jobs/') and len(Path(n).parts)==2,'declared bounded free_cone_search artifact')
            name=Path(n).name;base=name[:-4] if name.endswith('.tmp') else name
            require(base in jobfiles,'known free_cone_search artifact or retained tmp')
            cap=8388608 if base in ('map.json','proposal.json','endpoint.json','check.json') else 65536
        require(p.stat().st_size<=cap,'bounded free_cone_search archive file '+n)
    return dict(bound_files=len(actual),temporary_files=[n for n in sorted(actual) if n.endswith('.tmp')],temporary_files_are_evidence=False)


def verify_runtime(execution):
    rows=execution.get('results');cost=execution.get('cost',{})
    require(type(rows)is list and len(rows)==1 and rows[0].get('index')==0 and type(rows[0]['index'])is int and rows[0].get('status')in ('available','missing_resource','error'),'one fixed ordered free_cone_search transport')
    for k,v in dict(requested_workers=1,workers=1,max_in_flight=1,worker_memory_bytes=3*1024**3,memory_budget_bytes=3*1024**3,worker_memory_limit_enforced=True,numerical_threads_per_worker=1,serial_fallback=False,start_method='spawn').items():require(type(cost.get(k))is type(v) and cost[k]==v,'fixed free_cone_search runtime '+k)
    for k in ('elapsed_seconds','result_bytes','payload_bytes'):require(type(cost.get(k))in (int,float) and math.isfinite(cost[k]) and cost[k]>=0,'finite free_cone_search runtime '+k)
    require(cost['result_bytes']<=65536+4096,'bounded free_cone_search transport')
    for k,s in [('available','available'),('missing','missing_resource'),('errors','error')]:require(cost.get(k)==int(rows[0]['status']==s),'complete free_cone_search transport count '+k)
    if rows[0]['status']!='available':require('value' not in rows[0],'failed transport has no fabricated result')
    return rows[0]


def verify_ledger(ledger,input_reserve,check,source_cells):
    require(type(ledger)is dict and ledger.get('max_work')==450000000,'fixed whole job work ceiling')
    entries=ledger.get('entries');require(type(entries)is list and 1<=len(entries)<=5,'bounded free_cone_search stage ledger')
    stages=[('compilation',input_reserve),('map_materialization',50000000),('proposal_generator',100000000),('exact_endpoint',20000000),('search_checker',None)];total=0;pending=[]
    for i,(entry,(stage,allocation)) in enumerate(zip(entries,stages)):
        expected=450000000-total if allocation is None else allocation
        require(entry.get('stage')==stage and type(entry.get('allocation'))is int and entry['allocation']==expected,'exact ordered free_cone_search allocation')
        if i==0:
            require(entry.get('precision')=='declared_compilation_reserve' and entry.get('reserve')==expected and entry.get('charged_operations')==expected,'declared actual file/source binding reserve')
        elif entry.get('precision')=='independently_verified':
            require(i==4 and check is not None and entry.get('reserve')==check['independent_audit_work_reserve'] and entry.get('charged_operations')==check['audit_operations'],'only independently bounded checker refinement')
        else:
            require(entry.get('precision')=='allocated_unverified' and entry.get('reserve')==expected and entry.get('charged_operations')is None,'full pending producer/checker allocation')
            if i==4:pending.append(stage)
        require(type(entry['reserve'])is int and 0<entry['reserve']<=expected,'bounded stage work reserve');total+=entry['reserve']
    require(total<=450000000 and ledger.get('total_work_reserve')==total and ledger.get('remaining_work')==450000000-total,'exact conservative free_cone_search ledger sum')
    if check is not None:
        require(len(entries)==5 and check['audit_operations']<=entries[4]['allocation']-4*8388608-source_cells-1 and check['independent_audit_work_reserve']<=entries[4]['allocation'],'persisted check fits allocated audit allowance')
    return dict(total_work_reserve=total,pending_stages=pending,all_stages_committed=len(entries)==5 and not pending)


def verify_artifacts(directory,record):
    artifacts=(record or {}).get('artifacts',{})
    require(type(artifacts)is dict,'explicit free_cone_search artifact map')
    for name,value in artifacts.items():require(name in ('map','proposal','endpoint','check') and value==dict(file=name+'.json',sha256=sha(directory/(name+'.json'))),'bound free_cone_search artifact '+name)


def verify_job(directory,row,input_reserve,source_cells,check,license):
    folder=directory/'jobs';path=folder/'search-job.json';record=read(path,65536) if path.exists() else None
    progress=read(folder/'progress.json',65536) if (folder/'progress.json').exists() else None
    stored=read(folder/'check.json') if (folder/'check.json').exists() else None
    require(stored is None or check is not None and stored==check,'same deterministic independent endpoint check')
    if row['status']=='available':
        value=row.get('value');require(type(value)is dict and record is not None,'available endpoint metadata');scope(value)
        require(value.get('file')=='jobs/search-job.json' and value.get('sha256')==sha(path) and value.get('status')==record.get('status') and value.get('cost')==record.get('cost'),'transport metadata/hash/status/cost binding')
    ledger=None;pl=None;outer=False
    if record is not None:
        scope(record);ORIGINAL.verify_worker_cost(record['cost'])
        require(record.get('phase')=='search' and type(record.get('index'))is int and record['index']==0 and record.get('status')in ('endpoint_verified','unknown','missing_resource','rejected'),'one declared endpoint job')
        require(type(record.get('deadline_exceeded'))is bool,'explicit cooperative deadline status')
        if 'parent_license' in record:require(record['parent_license']==license,'same completed parent license')
        if 'input_work_reserve' in record:require(record['input_work_reserve']==input_reserve,'actual bounded source/file reserve')
        verify_artifacts(folder,record)
        if record.get('ledger')is not None:ledger=verify_ledger(record['ledger'],input_reserve,stored,source_cells)
    if progress is not None:
        scope(progress);verify_artifacts(folder,progress)
        require(progress.get('phase')in ('map_materialization_started','map_materialization_complete','proposal_started','power_estimate','gradient_iteration','proposal_complete','proposal_returned','exact_endpoint_returned','search_check_started','endpoint_verified','unknown','missing_resource','rejected'),'known endpoint lifecycle')
        require(progress.get('status')in ('missing_resource','endpoint_verified','unknown','rejected'),'known endpoint checkpoint status')
        pl=verify_ledger(progress['ledger'],input_reserve,stored if len(progress['ledger'].get('entries',[]))==5 else None,source_cells)
        if record is not None and record.get('ledger')is not None:
            outer=record.get('status')in ('missing_resource','rejected')
            if outer:
                old=progress['ledger']['entries'];new=record['ledger']['entries'];require(len(old)<=len(new),'failure preserves prior ledger prefix')
                for a,b in zip(old,new):
                    require(a['stage']==b['stage'] and a['allocation']==b['allocation'],'failure preserves allocation')
                    if a['precision']=='independently_verified':require(a==b,'failure preserves committed checker')
            else:
                for k in ('ledger','status','artifacts','endpoint_verified','finite_candidate_feasible'):require(progress.get(k)==record.get(k),'terminal progress metadata binding '+k)
        elif record is not None:require(record['status']in ('missing_resource','rejected'),'outer metadata without ledger is failure');outer=True
    available=row['status']=='available' and record is not None and record['status']=='endpoint_verified' and record.get('deadline_exceeded')is False
    if record is not None and record['status']=='endpoint_verified':
        require(check is not None and stored is not None and check.get('complete')is True and check.get('endpoint_verified')is True,'complete independent endpoint')
        require(ledger is not None and ledger['all_stages_committed'] and progress is not None and progress['phase']=='endpoint_verified' and set(record.get('artifacts',{}))=={'map','proposal','endpoint','check'},'committed complete endpoint ledger/artifacts')
        require(record.get('endpoint_verified')is True and record.get('finite_candidate_feasible')is check['finite_candidate_feasible'],'endpoint outcome binding')
    elif record is not None:
        require(record.get('endpoint_verified')is False and record.get('finite_candidate_feasible')is None,'failed/UNKNOWN metadata admits no candidate')
    return dict(transport_status=row['status'],worker_status=record.get('status') if record else None,
                endpoint_verified=available,finite_candidate_feasible=check['finite_candidate_feasible'] if available else None,
                independent_replay_retained=check is not None,deadline_exceeded=record.get('deadline_exceeded') if record else None,lifecycle=dict(ledger=ledger,progress_ledger=pl,progress_retained=progress is not None,outer_partial_failure=outer),**FLAGS)




def _audit(directory,*,write=False,time_limit=900,max_audit_operations=450000000,max_audit_cells=60000000):
    require(type(time_limit)in (int,float) and math.isfinite(time_limit) and 0<time_limit<=900,'finite bounded audit deadline')
    require(type(max_audit_operations)is int and 0<max_audit_operations<=450000000 and type(max_audit_cells)is int and 0<max_audit_cells<=60000000,'strict bounded independent audit caps')
    started=time.monotonic();deadline=started+time_limit;d=Path(directory).resolve()
    if write and (d/'independent_verification.json').exists():raise FileExistsError('independent verification already exists')
    io=CORE.EXACT.EXACT._Budget(deadline,max_audit_operations,max_audit_cells,4096);_IO_BUDGET.set(io)
    protocol=read(d/'protocol.json',65536);source=read(d/'source_seal.json',65536);inputs=read(d/'input.json',65536);seal=read(d/'seal.json',65536)
    for name in ('protocol','source_seal','input'):require(seal.get(name+'_sha256')==sha(d/(name+'.json')),'frozen search seal '+name)
    io.charge(sum(2*(path_under(ROOT,n).stat().st_size//64+1) for n in source))
    require(set(source)==set(source_names()),'complete transitive search source closure')
    frozen={str(p.relative_to(d/'frozen_source')) for p in (d/'frozen_source').rglob('*') if p.is_file()}
    require(frozen==set(source),'complete frozen search source tree')
    for n,h in source.items():require(sha(path_under(ROOT,n))==h==sha(path_under(d/'frozen_source',n)),'immutable search source '+n)
    require(set(inputs.get('input_sha256',{}))==set(INPUTS),'complete fixed search input closure')
    for n,h in inputs['input_sha256'].items():require(sha(path_under(ROOT,n))==h,'immutable search input '+n)
    reserve=4*sum(path_under(ROOT,n).stat().st_size for n in INPUTS)+12*sum(path_under(ROOT,n).stat().st_size for n in source)+1048576+1
    require(inputs.get('binding_work_reserve')==reserve and reserve+170000000+4*8388608<450000000,'bounded actual input/source/producer/checker work')
    license=CORE.load_verified_license(ROOT,inputs['input_sha256'],deadline=deadline,max_operations=min(50000000,max_audit_operations-io.operations),max_cells=max_audit_cells-io.cells,max_coefficient_bits=4096)
    io.charge(license.summary['audit_operations'],cells=license.summary['audit_cells'])
    parent=parent_protocol_license(license);verify_protocol(protocol,parent)
    require((license.summary['original_variables'],license.summary['original_rows'],license.summary['rank'],license.summary['free_count'])==(1957,5641,779,445),'unchanged licensed source/free chart')
    tests=read(d/'tests.json',65536);match=re.search(r'Ran (\d+) tests?',tests.get('stderr',''))
    require(tests.get('returncode')==0 and match and tests['stderr'].rstrip().endswith('OK'),'prescore fixed search tests passed');test_count=int(match.group(1))
    require(read(d/'run_started.json',65536)==dict(protocol_sha256=sha(d/'protocol.json')),'sealed fixed search startup')
    receipt=read(d/'receipt.json',65536);inventory=verify_inventory(d,receipt);require(receipt.get('source_count')==len(source),'terminal search source count')
    row=verify_runtime(read(d/'execution.json',65536));folder=d/'jobs'
    artifacts={name:read(folder/(name+'.json')) if (folder/(name+'.json')).exists() else None for name in ('map','proposal','endpoint')}
    require(artifacts['proposal']is None or artifacts['map']is not None,'proposal requires retained licensed map artifact')
    require(artifacts['endpoint']is None or artifacts['proposal']is not None,'endpoint requires retained fixed proposal')
    check=None;partial_map_check=None;ops=0;cells=0
    source_cells=license.source['source_cells'];cap=450000000-reserve-170000000-4*8388608-source_cells-1
    require(cap>0,'positive worker independent search allocation')
    if artifacts['proposal']is not None:
        check=CORE.verify_search(license,artifacts['map'],artifacts['proposal'],artifacts['endpoint'],deadline=deadline,max_operations=min(cap,max_audit_operations-io.operations),max_cells=max_audit_cells-io.cells,max_coefficient_bits=4096,max_trace_bytes=8388608,max_endpoint_bytes=8388608)
        ops=check['audit_operations'];cells=check['audit_cells'];io.charge(ops,cells=cells)
    elif artifacts['map']is not None:
        partial_map_check=CORE.verify_map_receipt(license,artifacts['map'],deadline=deadline,max_operations=min(cap,max_audit_operations-io.operations),max_cells=max_audit_cells-io.cells)
        ops=partial_map_check['audit_operations'];cells=partial_map_check['audit_cells'];io.charge(ops,cells=cells)
    job=verify_job(d,row,reserve,source_cells,check,parent)
    record=read(folder/'search-job.json',65536) if (folder/'search-job.json').exists() else None
    if record is not None and 'license_loader_cost' in record:require(record['license_loader_cost']==dict(audit_operations=license.summary['audit_operations'],audit_cells=license.summary['audit_cells']),'same bounded published license parsing')
    if record is not None and 'proposal_stop_reason' in record:require(record['proposal_stop_reason']==(artifacts['proposal'] or {}).get('stop_reason') and record.get('proposal_reason')==(artifacts['proposal'] or {}).get('reason'),'actual proposal termination metadata')
    for n,h in source.items():require(sha(path_under(ROOT,n))==h==sha(path_under(d/'frozen_source',n)),'post-replay source binding')
    for n,h in inputs['input_sha256'].items():require(sha(path_under(ROOT,n))==h,'post-replay input binding')
    verify_inventory(d,receipt)
    final_bindings={n:sha(d/(n+'.json')) for n in ('protocol','source_seal','input','seal','tests','execution','receipt')}
    require(time.monotonic()<=deadline,'whole search archive audit deadline')
    parent_manifest=read(ROOT/CORE.MANIFEST)
    result=dict(schema='primitive-state-free-cone-search-independent-review-v1',all_passed=True,source_count=len(source),tests_passed=test_count,parent_bound_files=len(parent_manifest['files']),parent_license_summary=license.summary,parent_source_rebuilds=0,full_elimination_replayed=False,independent_endpoint_checks=int(check is not None and check['endpoint_verified']),original_finite_equations=5641,original_variables=1957,rank=779,free_coordinates=445,search_check=check,partial_map_check=partial_map_check,job=job,inventory=inventory,gradient_or_merit_certified=False,intermediate_iterates_exact=False,affine_map_precision_decimal_digits=80,native_PSD_projection_precision='binary64',independent_replay_operations=ops,independent_replay_cells=cells,total_independent_audit_operations=io.operations,total_independent_audit_cells=io.cells,artifact_io_accounting='SHA file pass bytes//64+1; JSON read 2*(bytes//64+1) plus bytes//64+1 cells; source AST read proxy2*(bytes//64+1); issued license counters and endpoint/search checks charged separately',independent_audit_limits=dict(seconds=time_limit,max_operations=max_audit_operations,max_cells=max_audit_cells),elapsed_seconds=time.monotonic()-started,input_sha256=final_bindings,uniform_or_RH_admission=False,objective_preserved=False,**FLAGS)
    require(time.monotonic()<=deadline,'whole search final artifact/summary deadline')
    if write:
        with (d/'independent_verification.json').open('x') as f:json.dump(result,f,sort_keys=True,indent=2,allow_nan=False)
    return result


def audit(directory,**kwargs):
    token=_IO_BUDGET.set(None)
    try:return _audit(directory,**kwargs)
    finally:_IO_BUDGET.reset(token)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('directory');p.add_argument('--write',action='store_true');a=p.parse_args();print(json.dumps(audit(a.directory,write=a.write),sort_keys=True))
