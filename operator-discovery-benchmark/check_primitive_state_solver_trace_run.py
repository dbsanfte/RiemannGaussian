"""Independent archive audit of primitive/state numerical diagnostics only.

Rebuilds the complete arithmetic once and reuses its geometry for both jobs.
No numerical solver or numerical trace producer is imported. Partial worker
artifacts can establish retained diagnostics only, never arithmetic admission.
"""
import argparse
import ast
import hashlib
import json
import math
from pathlib import Path
import time
import check_cancellation_primitive_state_localizers as B
import check_cancellation_shared_gram as G
import check_primitive_state_scaled_search_v2 as GEOM
import check_primitive_state_solver_trace as TRACE

ROOT=Path(__file__).resolve().parent
FLAGS=dict(certified=False,exact_admission=False,infeasibility_proved=False,
           global_bound_proved=False,RH_proved=False)
PROGRAM=dict(target='mu',q=6,C=32,claim='critical',constraint='zero_cubic',
             dictionary_mode='extended',allow_constant_slack=True)
PHASES=['dual','primal']
LIMITS=dict(max_columns=2048,max_monomials=100000,max_operations=200000000,
            max_coefficient_bits=4096,max_horizon=80,max_degree=12,
            max_denominator=1000000,time_limit=900)
PARALLEL=dict(workers=2,worker_memory_bytes=3*1024**3,memory_budget_bytes=6*1024**3,
              timeout_seconds=1800,max_jobs=2,max_result_bytes=65536)
CAPS=dict(trace=8388608,log=1048576,metadata=65536)


def sha(path):
    h=hashlib.sha256()
    with Path(path).open('rb') as stream:
        for chunk in iter(lambda:stream.read(65536),b''):h.update(chunk)
    return h.hexdigest()


def read(path,cap=8388608):
    with Path(path).open('rb') as stream:raw=stream.read(cap+1)
    if len(raw)>cap:raise OverflowError('bounded audit artifact '+str(path))
    def pairs(items):
        result={}
        for key,value in items:
            if key in result:raise ValueError('duplicate JSON key')
            result[key]=value
        return result
    return json.loads(raw,object_pairs_hook=pairs,parse_constant=lambda _:(_ for _ in ()).throw(ValueError('finite JSON required')))


def path_under(directory,name):
    if type(name)is not str or not name or Path(name).is_absolute() or '..' in Path(name).parts:
        raise ValueError('relative archive path required')
    p=directory/name
    if p.is_symlink() or not p.resolve().is_relative_to(directory.resolve()):
        raise ValueError('contained regular artifact required')
    return p


def source_names(tests):
    if type(tests)is not list or not tests or any(type(n)is not str or not n.isidentifier() for n in tests) or len(set(tests))!=len(tests):
        raise ValueError('complete distinct test modules required')
    pending=['run_primitive_state_solver_trace','check_primitive_state_solver_trace_run',*tests];seen=set()
    while pending:
        name=pending.pop();path=ROOT/(name+'.py')
        if name in seen or not path.is_file():continue
        seen.add(name)
        for node in ast.walk(ast.parse(path.read_text())):
            if isinstance(node,ast.Import):pending.extend(a.name.split('.')[0] for a in node.names)
            elif isinstance(node,ast.ImportFrom) and node.module:pending.append(node.module.split('.')[0])
    return sorted(n+'.py' for n in seen)


def scope(record, *, required=False):
    if type(record)is not dict:raise ValueError('scope dictionary required')
    for key in FLAGS:
        mandatory=required and key in ('certified','infeasibility_proved','global_bound_proved','RH_proved')
        if (mandatory or key in record) and record.get(key)is not False:
            raise ValueError('numerical artifact cannot claim '+key)
    for key in ('admitted','feasibility_proved','cone_feasibility_proved','uniform_bound_proved','optimality_claim'):
        if key in record and record[key]is not False:raise ValueError('diagnostic only '+key)


def verify_inventory(directory,receipt):
    actual={str(p.relative_to(directory)) for p in directory.rglob('*') if p.is_file() and 'frozen_source' not in p.relative_to(directory).parts}
    actual-= {'receipt.json','independent_verification.json'}
    permitted={'protocol.json','source_seal.json','input.json','seal.json','run_started.json','tests.json','execution.json'}
    for phase in PHASES:
        jobnames=[f'jobs/{phase}.json',f'jobs/{phase}-trace.json',f'jobs/{phase}-progress.json']
        if phase=='primal':jobnames.append('jobs/primal-progress.json.source.json')
        permitted.update(jobnames);permitted.update(n+'.tmp' for n in jobnames)
        permitted.add(f'jobs/{phase}-native.log')
    if actual-permitted:raise ValueError('undeclared diagnostic artifact '+str(sorted(actual-permitted)))
    entries=receipt.get('files_sha256')
    if type(entries)is not dict or set(entries)!=actual:
        raise ValueError('complete terminal artifact inventory')
    byte_count=0
    for name,expected in entries.items():
        p=path_under(directory,name)
        if not p.is_file() or sha(p)!=expected:raise ValueError('terminal artifact hash '+name)
        artifact_name=name[:-4] if name.endswith('.tmp') else name
        cap=CAPS['trace'] if artifact_name.endswith(('-trace.json','-progress.json','.source.json')) else CAPS['log'] if artifact_name.endswith('.log') else CAPS['metadata']
        if p.stat().st_size>cap:raise OverflowError('artifact byte cap '+name)
        byte_count+=p.stat().st_size
    return dict(files=len(entries),bytes=byte_count)


def verify_runtime(execution):
    if type(execution)is not dict or type(execution.get('results'))is not list or len(execution['results'])!=2:
        raise ValueError('both predeclared diagnostic jobs required')
    cost=execution.get('cost',{})
    for key,value in dict(requested_workers=2,worker_memory_bytes=3*1024**3,
                          memory_budget_bytes=6*1024**3,worker_memory_limit_enforced=True,
                          numerical_threads_per_worker=1,serial_fallback=False,start_method='spawn').items():
        if type(cost.get(key))is not type(value) or cost[key]!=value:raise ValueError('executed resource contract '+key)
    if type(cost.get('workers'))is not int or not 1<=cost['workers']<=2:
        raise ValueError('available bounded process count')
    if type(cost.get('max_in_flight'))is not int or not 1<=cost['max_in_flight']<=2*cost['workers']:
        raise ValueError('bounded in-flight jobs')
    for i,row in enumerate(execution['results']):
        if type(row)is not dict or type(row.get('index'))is not int or row['index']!=i or row.get('status')not in ('available','missing_resource','error'):
            raise ValueError('ordered process transport status')
        if row['status']!='available' and 'value' in row:raise ValueError('process failure cannot invent returned metadata')
    for key in ('elapsed_seconds','result_bytes','payload_bytes'):
        value=cost.get(key)
        if type(value)not in (int,float) or not math.isfinite(value) or value<0:raise ValueError('finite runtime '+key)
    if cost['result_bytes']>2*(65536+4096):raise ValueError('bounded transport result bytes')
    for key,status in [('available','available'),('missing','missing_resource'),('errors','error')]:
        if cost.get(key)!=sum(r['status']==status for r in execution['results']):raise ValueError('complete transport count '+key)
    return True


def rebuild():
    built=[B.build(PROGRAM,X) for X in [1,2,3,5]];aux=B.auxiliary()
    ordinary=[b['instance'] for b in built]
    instances=ordinary+[aux['instance']]
    blocks=[b['gram_blocks'] for b in built]+[aux['gram_blocks']]
    storage=[b['storage_blocks'] for b in built]+[aux['storage_blocks']]
    specs=B.gram_specs()
    expected=dict(ordinary_case_hashes=list(map(G.digest,ordinary)),case_hashes=list(map(G.digest,instances)),
        gram_block_hashes=list(map(G.digest,blocks)),storage_block_hashes=list(map(G.digest,storage)),
        gram_archive_hashes=[G.digest(b['gram_archive']) for b in built],
        factor_archive_hashes=[G.digest(b['factor_archive']) for b in built],
        divisor_archive_hashes=[G.digest(b['divisor_archive']) for b in built],
        cell_archive_hashes=[G.digest(b['cell_archive']) for b in built],dictionary_sha256=built[0]['dictionary_sha256'],gram_specs=specs,
        primitive_state_archive_hashes=[G.digest([{k:v for k,v in row.items() if k!='polynomial_sha256'} for row in b['primitive_state_archive']]) for b in built],
        primitive_source_hashes=[G.digest(b['primitive_sources']) for b in built],multiplier_source_hashes=[G.digest(b['multiplier_sources']) for b in built])
    geometry=GEOM.prepared(instances,blocks,storage,specs)
    return expected,geometry


def verify_metadata(record,phase,index,expected):
    if record.get('phase')!=phase or record.get('index')!=index or record.get('program')!=PROGRAM or record.get('refitted',False)is not False:
        raise ValueError('same historical diagnostic case')
    if record.get('scales')!=[1,2,3,5]:raise ValueError('historical development scales')
    scope(record,required=True)
    if record.get('status')not in ('trace_available','missing_resource','rejected'):raise ValueError('nonadmitted diagnostic status')
    complete='case_hashes' in record
    if complete:
        for key,value in expected.items():
            if record.get(key)!=value:raise ValueError('complete original arithmetic archive '+key)
    elif record['status']=='trace_available':raise ValueError('completed trace complete arithmetic metadata required')
    return complete


def verify_solver(trace,phase,protocol):
    solver=trace.get('solver')
    if type(solver)is not dict:raise ValueError('explicit solver metadata')
    scope(trace)
    if trace.get('vector_role')=='accepted_proposal':raise ValueError('diagnostic protocol accepts no proposal')
    options=dict(solver.get('options',{}));limit=options.pop('time_limit',None)
    if type(limit)not in (int,float) or not math.isfinite(limit) or not 0<=limit<=900:
        raise ValueError('bounded remaining cooperative solver seconds')
    # Freeze records the complete settings, except the clock-dependent time_limit.
    contract=protocol.get('solver_contract')
    if type(contract)is not dict or type(contract.get('versions'))is not dict:
        raise ValueError('frozen solver settings and versions')
    version_keys=['scipy'] if phase=='dual' else ['clarabel','cvxpy']
    versions={name:contract['versions'][name] for name in version_keys}
    template=contract['support_options' if phase=='dual' else 'primal_options']
    if solver.get('versions')!=versions or options!=template:
        raise ValueError('frozen solver version/settings binding')
    if solver.get('name')!=('scipy-highs' if phase=='dual' else 'clarabel-native'):raise ValueError('declared solver attempt')
    return True


def verify_trace(directory,phase,trace,geometry,protocol,source):
    verify_solver(trace,phase,protocol)
    expected_source={name:source[name] for name in ('primitive_state_solver_trace.py','primitive_state_numerical_proposals.py')}
    log=trace.get('retained_log',{})
    if log.get('path') is not None:
        expected=directory/f'jobs/{phase}-native.log'
        if Path(log['path']).resolve()!=expected.resolve():raise ValueError('bound native log path')
    if phase=='dual':
        return TRACE.verify_system_trace('support',geometry['restricted'],geometry['lhs'],geometry['domain'],trace,
            nonnegative=geometry['rn'],relations=geometry['rrr'],expected_source_hashes=expected_source)
    return TRACE.verify_system_trace('primal',geometry['columns'],geometry['lhs'],geometry['domain'],trace,
        shape=geometry['shape'],offset=geometry['offset'],specs=B.gram_specs(),expected_source_hashes=expected_source)


def system_metadata(phase,geometry):
    if phase=='dual':
        width=2*len(geometry['domain'])+len(geometry['rn'])
        return dict(variables=width,rows_count=len(geometry['restricted'])+1,
            objective=[1.0]*width,nonnegative_indices=list(range(width)),psd_blocks=[])
    columns=geometry['columns'];offset=geometry['offset'];shape=geometry['shape']
    objective=[0.0]*len(columns);objective[:shape[0]+2*shape[1]]=[1.0]*(shape[0]+2*shape[1]);blocks=[];j=offset
    for name,size in B.gram_specs().items():
        indices=[]
        for a in range(size):
            for b in range(a,size):
                indices.append(j);objective[j]=float(a==b);j+=1
        blocks.append(dict(name=name,size=size,indices=indices))
    return dict(variables=len(columns),rows_count=len(geometry['domain']),objective=objective,
                nonnegative_indices=list(range(offset)),psd_blocks=blocks)


def coordinate_map(phase,geometry):
    if phase=='dual':
        width=len(geometry['domain'])
        return dict(moment_monomials=[repr(m) for m in geometry['domain']],positive_moment_offset=0,
            negative_moment_offset=width,slack_offset=2*width,slack_source_column_indices=geometry['rn'],relation_source_column_indices=geometry['rrr'])
    return dict(scalar_offset=0,scalar_count=geometry['offset'],psd_blocks=system_metadata(phase,geometry)['psd_blocks'],
        upper_triangle_order='row-major-a-then-b-a-through-n-minus-1',source_column_order='identity')


def complete_trace_check(directory,phase,trace,geometry,protocol,source):
    metadata=trace.get('original_system_metadata')
    if metadata is None and type(trace.get('original_system'))is dict:
        metadata={k:v for k,v in trace['original_system'].items() if k not in ('rows','rhs')}
        metadata['rows_count']=len(trace['original_system']['rows'])
    if metadata!=system_metadata(phase,geometry):raise ValueError('trusted complete numerical objective/domain')
    if trace.get('original_coordinate_map')!=coordinate_map(phase,geometry):raise ValueError('complete original coordinate map')
    if 'raw_partial_original_vector' in trace:
        raw=trace['raw_partial_original_vector'];width=metadata['variables']
        if trace.get('original_vector') is not None or type(raw)is not list or len(raw)!=width or not any(v is None for v in raw):
            raise ValueError('partial original vector explicit unknown coordinates')
        if any(v is not None and (type(v)not in (int,float) or not math.isfinite(v)) for v in raw):
            raise ValueError('finite-or-unknown partial raw coordinates')
    return verify_trace(directory,phase,trace,geometry,protocol,source)


def verify_progress(directory,phase,trace,geometry,protocol,source):
    path=directory/f'jobs/{phase}-progress.json';startup_path=Path(str(path)+'.source.json')
    if not path.exists() and not startup_path.exists():
        return dict(retained=False,exact_admission=False)
    origin='progress' if path.exists() else 'startup-before-first-progress'
    progress=read(path if path.exists() else startup_path)
    if progress.get('schema')!='primitive-state-solver-trace-v1':raise ValueError('known progress schema')
    scope(progress);checkpoint_trace_check=None
    if progress.get('kind')in ('support','primal'):
        if trace is not None:
            if progress!=trace:raise ValueError('durable final progress equals returned trace')
        else:
            checkpoint_trace_check=complete_trace_check(directory,phase,progress,geometry,protocol,source)
            trace=progress;origin='terminal-checkpoint-before-trace-transport'
        progress=read(startup_path) if startup_path.exists() else None
        final=True
    else:final=False
    if progress is not None:
        key='support' if phase=='dual' else 'primal'
        if progress.get('kind')!=key+'-progress' or progress.get('numerical_evidence_only')is not True or progress.get('original_vector')is not None or progress.get('vector_role')!='unavailable':
            raise ValueError('partial progress never implies a complete vector')
        if 'source_checkpoint_hash' in progress:
            if phase!='primal' or not startup_path.exists():raise ValueError('iteration progress requires source checkpoint')
            startup=read(startup_path)
            if progress['source_checkpoint_hash']!=TRACE.digest(startup):raise ValueError('iteration/source checkpoint hash')
            if type(progress.get('raw_info'))is not dict:raise ValueError('explicit native iteration information')
            progress=startup
        if trace is not None:
            for name in ('original_system_hash','scaled_original_system_hash','solver_system_hash','transformation_receipt','source_hashes'):
                if progress.get(name)!=trace.get(name):raise ValueError('startup/final source binding '+name)
            if progress.get('solver')!=trace.get('solver'):
                raise ValueError('same startup and terminal solver settings')
        else:
            # Adapt recorded unavailable-vector startup into a diagnostic core
            # check. Exact compression is replayed once for this failed job.
            partial=dict(progress,kind=key,original_system_metadata=system_metadata(phase,geometry),
                original_vector=None,vector_role='unavailable',termination_status='external-worker-unavailable',
                retained_log=dict(text='',encoding='utf-8',retained_bytes=0,total_bytes=0,truncated=False,sha256=hashlib.sha256(b'').hexdigest()))
            checkpoint_trace_check=verify_trace(directory,phase,partial,geometry,protocol,source)
    return dict(retained=True,origin=origin,terminal_trace_equal=final and origin=='progress',
        startup_retained=startup_path.exists(),partial_only=not final,checkpoint_trace_check=checkpoint_trace_check,exact_admission=False)


TESTS=['test_primitive_state_solver_trace','test_check_primitive_state_solver_trace',
       'test_run_primitive_state_solver_trace','test_check_primitive_state_solver_trace_run']
INPUTS=['cancellation-arithmetic-results/publication-011/manifest.json',
        'cancellation-arithmetic-results/publication-011/report.json',
        'primitive_state_localizers_uniform_scope.txt','primitive_state_trace_resource_scope.txt']
COMPILER_LIMITS={k:v for k,v in LIMITS.items() if k not in ('max_denominator','time_limit')}
TRACE_LIMITS=dict(cooperative_seconds=900,max_rows=2500,max_variables=60000,max_work=450000000,
    max_cells=4000000,max_coefficient_bits=4096,max_trace_bytes=8388608,max_log_bytes=1048576,max_metadata_bytes=65536)


def verify_protocol(protocol):
    expected=dict(schema='primitive-state-solver-trace-run-v1',program=PROGRAM,scales=[1,2,3,5],phases=PHASES,
        language=B.SPEC,gram_specs=B.gram_specs(),compiler_limits=COMPILER_LIMITS,trace_limits=TRACE_LIMITS,
        parallel=PARALLEL,tests=TESTS,
        strategy='two independent numerical traces on unchanged complete source equations; no exact admission',
        no_refit_or_source_selection=True,historical_development_scales=True,
        canonical_primal_matrix_independently_rebuilt=False)
    for key,value in expected.items():
        if protocol.get(key)!=value:raise ValueError('known diagnostic protocol '+key)
    for key in ('certified','global_bound_proved','RH_proved','infeasibility_proved'):
        if protocol.get(key)is not False:raise ValueError('diagnostic protocol scope '+key)
    scope(protocol)
    contract=protocol.get('solver_contract')
    if type(contract)is not dict or set(contract)!= {'versions','support_options','primal_options'}:
        raise ValueError('complete frozen solver contract')
    versions=contract['versions']
    if type(versions)is not dict or set(versions)!={'scipy','cvxpy','clarabel','numpy'} or any(type(v)is not str or not v for v in versions.values()):
        raise ValueError('complete frozen runtime versions')
    if contract['support_options']!=dict(threads=1,parallel=False,disp=True):raise ValueError('known HiGHS settings')
    primal=contract['primal_options']
    if type(primal)is not dict or 'time_limit' in primal or primal.get('max_threads')!=1 or primal.get('verbose')is not True:
        raise ValueError('complete frozen single-thread Clarabel settings')
    return True


def verify_worker_cost(cost):
    if type(cost)is not dict:raise ValueError('returned worker cost required')
    for key in ('elapsed_seconds','cpu_seconds','peak_rss_kib'):
        value=cost.get(key)
        if type(value)not in (int,float) or not math.isfinite(value) or value<0:raise ValueError('finite worker cost '+key)
    if cost['peak_rss_kib']>3*1024**2:raise ValueError('worker RSS within per-worker memory')
    if type(cost.get('pid'))is not int or cost['pid']<=0:raise ValueError('explicit worker process')
    if type(cost.get('observed_threads_at_completion'))is not int or cost['observed_threads_at_completion']!=1:
        raise ValueError('completed worker observed thread count')
    return True


def verify_compilation(record,geometry):
    expected=dict(complete_monomials=len(geometry['domain']),complete_columns=len(geometry['columns']),
        compilation_work_reserve=geometry['compilation'],
        exact_columns_hash=G.digest([[[list(m),str(q)] for m,q in sorted(p.items())] for p in geometry['columns']]),
        exact_target_hash=G.digest([[list(m),str(q)] for m,q in sorted(geometry['lhs'].items())]))
    if 'complete_columns' in record:
        for key,value in expected.items():
            if record.get(key)!=value:raise ValueError('complete compiled original system '+key)
    elif record['status']=='trace_available':raise ValueError('completed trace compilation metadata')
    return expected


def verify_job(directory,phase,index,row,expected,geometry,protocol,source):
    path=directory/f'jobs/{phase}.json';trace_path=directory/f'jobs/{phase}-trace.json'
    record=read(path,CAPS['metadata']) if path.exists() else None
    if row['status']=='available':
        value=row.get('value')
        if type(value)is not dict or value.get('file')!=str(path.relative_to(directory)) or not path.exists() or value.get('sha256')!=sha(path):
            raise ValueError('returned isolated metadata file/hash')
        scope(value,required=True)
        if value.get('status')!=record.get('status') or value.get('cost')!=record.get('cost'):
            raise ValueError('returned status and cost binding')
    elif record is not None:
        # A process may write metadata then die before transporting it. It is
        # retained evidence, but remains an unavailable outer process result.
        scope(record)
    if record is not None:
        verify_metadata(record,phase,index,expected)
        verify_worker_cost(record.get('cost'))
        verify_compilation(record,geometry)
    elif row['status']=='available':raise ValueError('available worker metadata required')
    trace=read(trace_path,CAPS['trace']) if trace_path.exists() else None
    trace_check=None
    if trace is not None:
        if record is not None and record.get('status')=='trace_available':
            if record.get('trace_file')!=str(trace_path.relative_to(directory)) or record.get('trace_sha256')!=sha(trace_path):
                raise ValueError('complete retained trace file/hash binding')
        trace_check=complete_trace_check(directory,phase,trace,geometry,protocol,source)
    elif record is not None and record.get('status')=='trace_available':raise ValueError('completed worker trace required')
    if record is not None and record.get('status')!='trace_available' and any(k in record for k in ('trace_file','trace_sha256')):
        raise ValueError('failed worker cannot claim completed trace metadata')
    progress=verify_progress(directory,phase,trace,geometry,protocol,source)
    return dict(phase=phase,transport_status=row['status'],worker_status=record.get('status') if record else None,
        arithmetic_metadata_complete=record is not None and 'case_hashes' in record,trace_retained=trace is not None,
        trace_check=trace_check,progress=progress,unknown_mathematical_feasibility=True,**FLAGS)


def audit(directory, *, write=False):
    start=time.monotonic();d=Path(directory).resolve();target=d/'independent_verification.json'
    if write and target.exists():raise FileExistsError('exclusive independent diagnostic review')
    protocol=read(d/'protocol.json',CAPS['metadata']);verify_protocol(protocol)
    source=read(d/'source_seal.json',CAPS['metadata']);seal=read(d/'seal.json',CAPS['metadata'])
    if set(source)!=set(source_names(TESTS)):raise ValueError('complete executed source closure')
    actual_frozen={str(p.relative_to(d/'frozen_source')) for p in (d/'frozen_source').rglob('*') if p.is_file()}
    if actual_frozen!=set(source):raise ValueError('complete frozen source inventory')
    for name,h in source.items():
        if sha(path_under(ROOT,name))!=h or sha(path_under(d/'frozen_source',name))!=h:raise ValueError('frozen source '+name)
    for name in ['protocol','source_seal','input']:
        if seal.get(name+'_sha256')!=sha(d/(name+'.json')):raise ValueError('sealed preregistration '+name)
    inputs=read(d/'input.json',CAPS['metadata']).get('input_sha256')
    if type(inputs)is not dict or set(inputs)!=set(INPUTS):raise ValueError('complete immutable prior input binding')
    for name,h in inputs.items():
        if sha(path_under(ROOT,name))!=h:raise ValueError('bound prior input '+name)
    manifest=read(ROOT/'cancellation-arithmetic-results/publication-011/manifest.json')
    for name,h in manifest['files'].items():
        if sha(path_under(ROOT,name))!=h:raise ValueError('immutable publication011 '+name)
    tests=read(d/'tests.json',CAPS['metadata'])
    if type(tests.get('returncode'))is not int or tests['returncode']!=0:raise ValueError('prescore tests passed')
    if read(d/'run_started.json',CAPS['metadata'])!=dict(protocol_sha256=sha(d/'protocol.json')):
        raise ValueError('exclusive preregistered execution')
    receipt=read(d/'receipt.json',CAPS['metadata']);scope(receipt,required=True)
    if receipt.get('source_count')!=len(source):raise ValueError('complete source count')
    inventory=verify_inventory(d,receipt)
    execution=read(d/'execution.json',CAPS['metadata']);verify_runtime(execution)
    expected,geometry=rebuild()
    checks=[verify_job(d,phase,i,execution['results'][i],expected,geometry,protocol,source) for i,phase in enumerate(PHASES)]
    # Freeze is checked after replay too: no audit-time source or evidence edits.
    for name,h in source.items():
        if sha(ROOT/name)!=h or sha(d/'frozen_source'/name)!=h:raise ValueError('source changed during independent replay '+name)
    for name,h in receipt['files_sha256'].items():
        if sha(path_under(d,name))!=h:raise ValueError('artifact changed during replay '+name)
    review=dict(schema='primitive-state-solver-trace-independent-review-v1',all_passed=True,
        source_count=len(source),inventory=inventory,checks=checks,
        complete_original_columns=len(geometry['columns']),complete_original_monomials=len(geometry['domain']),
        redundant_storage_cross_columns=len(geometry['redundancy']),arithmetic_rebuilds=1,geometry_rebuilds=1,
        canonical_primal_matrix_independently_rebuilt=False,numerical_diagnostics_only=True,
        mathematical_feasibility='UNKNOWN',elapsed_seconds=time.monotonic()-start,
        input_sha256={n:sha(d/n) for n in ['protocol.json','source_seal.json','input.json','seal.json','tests.json','execution.json','receipt.json']},**FLAGS)
    if write:
        with target.open('x') as stream:json.dump(review,stream,sort_keys=True,indent=2,allow_nan=False);stream.write('\n')
    return review


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('directory');parser.add_argument('--write',action='store_true')
    args=parser.parse_args();result=audit(args.directory,write=args.write)
    print(json.dumps(dict(all_passed=result['all_passed'],mathematical_feasibility=result['mathematical_feasibility']),sort_keys=True))
