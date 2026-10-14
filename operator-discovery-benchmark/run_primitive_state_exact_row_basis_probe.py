"""One bounded exact PRIMAL preprocessing probe; no numerical solve or admission."""
import argparse
import ast
import json
import math
import os
from pathlib import Path
import resource
import subprocess
import sys
import time
import run_detector as R
from detector_parallel import run_jobs
from detector_workflow_guard import require_verified_runtime
import cancellation_primitive_state_localizers as P
import cancellation_primitive_state_scaled_synthesis as S
import run_primitive_state_solver_trace as TRACE
import primitive_state_equation_projection as PROJECT
import check_primitive_state_equation_projection as PROJECT_CHECK
import primitive_state_exact_row_basis as BASIS
import check_primitive_state_exact_row_basis as BASIS_CHECK

ROOT=Path(__file__).resolve().parent
BASE=ROOT/'cancellation-arithmetic-results'
PROGRAM=dict(TRACE.PROGRAM);SCALES=list(TRACE.SCALES);COMPILER_LIMITS=dict(TRACE.COMPILER_LIMITS)
FLAGS=dict(certified=False,exact_admission=False,infeasibility_proved=False,global_bound_proved=False,RH_proved=False)
LIMITS=dict(cooperative_seconds=900,max_work=450000000,projection_operations=50000000,
    basis_operations=175000000,max_source_cells=4000000,max_live_cells=4000000,
    max_fill_cells=20000000,max_coefficient_bits=4096,max_receipt_bytes=8388608,
    max_metadata_bytes=65536,max_audit_cells=60000000)
PARALLEL=dict(workers=1,worker_memory_bytes=3*1024**3,memory_budget_bytes=3*1024**3,
    timeout_seconds=1800,max_jobs=1,max_result_bytes=65536)
TESTS=['test_primitive_state_equation_projection','test_check_primitive_state_equation_projection',
    'test_primitive_state_exact_row_basis','test_check_primitive_state_exact_row_basis',
    'test_run_primitive_state_exact_row_basis_probe','test_check_primitive_state_exact_row_basis_probe']
INPUTS=['cancellation-arithmetic-results/publication-012/manifest.json',
    'cancellation-arithmetic-results/publication-012/report.json','primitive_state_exact_basis_resource_scope.txt']


def validate_limits(limits):
    if type(limits)is not dict or set(limits)!=set(LIMITS):raise ValueError('complete preprocessing limits')
    if any(type(v)is not int or v<1 for v in limits.values()):raise ValueError('strict positive preprocessing caps')
    if limits['max_receipt_bytes']<256 or limits['max_work']>450000000 or limits['cooperative_seconds']>900:
        raise ValueError('authorized byte/work/time ceilings')
    if limits['projection_operations']+limits['basis_operations']>=limits['max_work']:
        raise ValueError('producer reserves must leave independent audit allowance')


class WorkLedger:
    """Reservations stay conservative until independent precision is available."""
    def __init__(self,total,compilation):
        if any(type(v)is not int or v<1 for v in (total,compilation)) or compilation>=total:
            raise OverflowError('positive compilation within total work allowance')
        self.total=total;self.entries=[dict(stage='compilation',allocation=compilation,reserve=compilation,
            charged_operations=compilation,precision='declared_compilation_reserve')]
    def remaining(self):return self.total-sum(e['reserve'] for e in self.entries)
    def allocate(self,stage,allocation):
        if type(allocation)is not int or allocation<1 or allocation>self.remaining():raise OverflowError('insufficient work allocation '+stage)
        if any(e['stage']==stage for e in self.entries):raise ValueError('unique work stage')
        entry=dict(stage=stage,allocation=allocation,reserve=allocation,charged_operations=None,precision='allocated_unverified')
        self.entries.append(entry);return entry
    def precise(self,entry,reserve,operations):
        if type(reserve)is not int or not 0<=reserve<=entry['allocation'] or type(operations)is not int or not 0<=operations<=reserve:
            raise ValueError('independent exact charge within allocation')
        entry.update(reserve=reserve,charged_operations=operations,precision='independently_verified')
    def snapshot(self):
        return dict(max_work=self.total,total_work_reserve=self.total-self.remaining(),remaining_work=self.remaining(),entries=[dict(e) for e in self.entries])


def bounded_write(path,value,cap):
    payload=json.dumps(value,sort_keys=True,separators=(',',':'),allow_nan=False).encode()
    if len(payload)>cap:raise OverflowError('bounded preprocessing artifact bytes')
    temporary=Path(str(path)+'.tmp')
    with temporary.open('wb') as f:f.write(payload);f.flush();os.fsync(f.fileno())
    os.replace(temporary,path)


def process_equations(columns,lhs,monomials,retained_indices,recipes,*,directory,deadline,
                      compilation_work_reserve,limits=None):
    """Run only algebraic preprocessing. Tiny synthetic domains support calibration."""
    limits=dict(LIMITS if limits is None else limits);validate_limits(limits)
    if type(deadline)not in (int,float) or not math.isfinite(deadline):raise ValueError('finite shared preprocessing deadline')
    directory=Path(directory);directory.mkdir(exist_ok=True)
    ledger=WorkLedger(limits['max_work'],compilation_work_reserve)
    out=dict(status='unknown',equation_reduction_verified=False,selected_original_row_indices=None,artifacts={},**FLAGS)
    def checkpoint(phase):
        record=dict(phase=phase,ledger=ledger.snapshot(),status=out['status'],equation_reduction_verified=out['equation_reduction_verified'],
            selected_original_row_indices=out['selected_original_row_indices'],artifacts=dict(out['artifacts']),**FLAGS)
        bounded_write(directory/'progress.json',record,limits['max_metadata_bytes'])
    def artifact(name,value):
        path=directory/(name+'.json');bounded_write(path,value,limits['max_receipt_bytes'])
        out['artifacts'][name]=dict(file=path.name,sha256=R.sha(path))
    def check_allocation(stage,future,source_cells):
        allocation=ledger.remaining()-future
        overhead=limits['max_receipt_bytes']+source_cells+1
        operations=allocation-overhead
        if operations<1:raise OverflowError('independent audit work reserve unavailable '+stage)
        return ledger.allocate(stage,allocation),operations
    common=dict(deadline=deadline,max_source_cells=limits['max_source_cells'],max_live_cells=limits['max_live_cells'],
        max_coefficient_bits=limits['max_coefficient_bits'],max_receipt_bytes=limits['max_receipt_bytes'])
    try:
        checkpoint('prepared_source')
        producer=ledger.allocate('projection_producer',limits['projection_operations']);checkpoint('projection_started')
        projection_limits={k:common[k] for k in common if k!='deadline'};projection_limits['max_operations']=producer['allocation']
        rows,rhs,projection=PROJECT.project_equations(columns,lhs,monomials,retained_indices,recipes,
            max_operations=producer['allocation'],**common)
        artifact('projection',projection);checkpoint('projection_returned')
        source_cells=sum(map(len,columns))+len(lhs)
        check_entry,audit_ops=check_allocation('projection_checker',limits['basis_operations'],source_cells+(sum(map(len,rows)) if rows is not None else 0))
        checkpoint('projection_check_started')
        project_check=PROJECT_CHECK.verify_projection(columns,lhs,monomials,retained_indices,recipes,rows,rhs,projection,
            deadline=deadline,max_audit_operations=audit_ops,max_audit_cells=limits['max_audit_cells'],
            max_coefficient_bits=limits['max_coefficient_bits'],max_receipt_bytes=limits['max_receipt_bytes'],authorized_limits=projection_limits)
        artifact('projection-check',project_check)
        if project_check.get('verified')is not True:raise ValueError('projection independently verified gate')
        ledger.precise(check_entry,project_check['independent_audit_work_reserve'],project_check['audit_operations'])
        if projection.get('complete')is not True or project_check.get('complete')is not True:
            out.update(status='unknown',reason='incomplete projection; no row basis attempted');checkpoint('projection_unknown');return dict(out,ledger=ledger.snapshot())
        if project_check.get('projection_authorized')is not True:raise ValueError('projection preprocessing authorization gate')
        ledger.precise(producer,projection['counts']['operations'],projection['counts']['operations']);checkpoint('projection_verified')
        producer=ledger.allocate('basis_producer',limits['basis_operations']);checkpoint('basis_started')
        basis_limits={k:common[k] for k in common if k!='deadline'};basis_limits.update(max_operations=producer['allocation'],max_fill_cells=limits['max_fill_cells'])
        selected,selected_rhs,basis=BASIS.reduce_rows(rows,rhs,len(retained_indices),max_operations=producer['allocation'],
            max_fill_cells=limits['max_fill_cells'],**common)
        artifact('basis',basis);checkpoint('basis_returned')
        source_cells=sum(map(len,rows))+len(rhs)
        check_entry,audit_ops=check_allocation('basis_checker',0,source_cells);checkpoint('basis_check_started')
        basis_check=BASIS_CHECK.verify_rows(rows,rhs,len(retained_indices),selected,selected_rhs,basis,
            deadline=deadline,max_audit_operations=audit_ops,max_audit_cells=limits['max_audit_cells'],
            max_coefficient_bits=limits['max_coefficient_bits'],max_receipt_bytes=limits['max_receipt_bytes'],authorized_limits=basis_limits)
        artifact('basis-check',basis_check)
        if basis_check.get('verified')is not True:raise ValueError('basis independently verified gate')
        ledger.precise(check_entry,basis_check['independent_audit_work_reserve'],basis_check['audit_operations'])
        if basis.get('complete')is not True or basis_check.get('complete')is not True:
            out.update(status='unknown',reason='incomplete basis; original equations remain required');checkpoint('basis_unknown');return dict(out,ledger=ledger.snapshot())
        if basis_check.get('reduction_authorized')is not True:raise ValueError('basis equivalence authorization gate')
        if basis.get('source_hash')!=projection.get('projected_rows_hash'):raise ValueError('projection/basis complete source binding')
        ledger.precise(producer,basis['counts']['operations'],basis['counts']['operations'])
        indices=basis['retained_indices']
        if any(type(i)is not int or not 0<=i<len(monomials) for i in indices):raise ValueError('original equality row indices')
        out.update(status='basis_verified',equation_reduction_verified=True,selected_original_row_indices=indices,
            original_rows=len(monomials),original_columns=len(columns),projection_columns=len(retained_indices),
            retained_rows=len(indices),augmented_rank=basis['augmented_rank'],
            inconsistent_augmented_pivots=basis['inconsistent_augmented_pivots'])
        checkpoint('basis_verified')
    except (OverflowError,TimeoutError,MemoryError,ImportError) as e:
        out.update(status='missing_resource',reason=str(e) or type(e).__name__,equation_reduction_verified=False,selected_original_row_indices=None);checkpoint('missing_resource')
    except (ValueError,TypeError,KeyError,RuntimeError,ZeroDivisionError) as e:
        out.update(status='rejected',reason=str(e) or type(e).__name__,equation_reduction_verified=False,selected_original_row_indices=None);checkpoint('rejected')
    return dict(out,ledger=ledger.snapshot())


def sources():
    pending=['run_primitive_state_exact_row_basis_probe','check_primitive_state_exact_row_basis_probe',*TESTS];seen=set()
    while pending:
        name=pending.pop();path=ROOT/(name+'.py')
        if name in seen or not path.is_file():continue
        seen.add(name)
        for node in ast.walk(ast.parse(path.read_text())):
            if isinstance(node,ast.Import):pending.extend(a.name.split('.')[0] for a in node.names)
            elif isinstance(node,ast.ImportFrom) and node.module:pending.append(node.module.split('.')[0])
    return sorted(n+'.py' for n in seen)


def validate_prior():
    manifest=R.read(BASE/'publication-012/manifest.json')
    for name,h in manifest['files'].items():
        if R.sha(ROOT/name)!=h:raise ValueError('immutable publication012 '+name)


def freeze(directory):
    require_verified_runtime();validate_limits(LIMITS);validate_prior();d=Path(directory).resolve();d.mkdir(exist_ok=False)
    (d/'jobs').mkdir();(d/'frozen_source').mkdir();source={}
    for name in sources():
        (d/'frozen_source'/name).write_bytes((ROOT/name).read_bytes());source[name]=R.sha(ROOT/name)
    protocol=dict(schema='primitive-state-exact-row-basis-probe-v1',program=PROGRAM,scales=SCALES,
        phases=['primal_preprocessing'],language=P.SPEC,gram_specs=P.gram_specs(),compiler_limits=COMPILER_LIMITS,
        limits=LIMITS,parallel=PARALLEL,tests=TESTS,parent_publication='publication-012',
        expected_shape=dict(original_rows=5641,original_columns=1957,projected_columns=1224,omitted_columns=733),
        strategy='verify full15 column identities, exact augmented row basis, independent replay; no solver',
        solver_called=False,no_refit_or_source_selection=True,historical_development_scales=True,**FLAGS)
    R.write(d/'protocol.json',protocol);R.write(d/'source_seal.json',source)
    R.write(d/'input.json',dict(input_sha256={n:R.sha(ROOT/n) for n in INPUTS}))
    R.write(d/'seal.json',{n+'_sha256':R.sha(d/(n+'.json')) for n in ['protocol','source_seal','input']})


def validate(directory):
    d=Path(directory);seal=R.read(d/'seal.json')
    for n in ['protocol','source_seal','input']:
        if seal[n+'_sha256']!=R.sha(d/(n+'.json')):raise ValueError('frozen seal '+n)
    source=R.read(d/'source_seal.json')
    if set(source)!=set(sources()):raise ValueError('complete source closure')
    for n,h in source.items():
        if R.sha(ROOT/n)!=h or R.sha(d/'frozen_source'/n)!=h:raise ValueError('frozen source '+n)
    inputs=R.read(d/'input.json')['input_sha256']
    if set(inputs)!=set(INPUTS):raise ValueError('complete immutable input set')
    for n,h in inputs.items():
        if R.sha(ROOT/n)!=h:raise ValueError('immutable input '+n)
    validate_prior()


def worker(job):
    require_verified_runtime();d=Path(job['directory']);validate(d)
    if job.get('phase')!='primal_preprocessing' or job.get('index')!=0 or (d/'receipt.json').exists():raise ValueError('one known unsealed preprocessing job')
    start=time.monotonic();cpu=time.process_time();deadline=start+LIMITS['cooperative_seconds']
    out=dict(phase=job['phase'],index=0,program=PROGRAM,scales=SCALES,solver_called=False,equation_reduction_verified=False,**FLAGS)
    try:
        built=[P.build(PROGRAM,X) for X in SCALES];aux=P.auxiliary()
        instances=[b['instance'] for b in built]+[aux['instance']]
        blocks=[b['gram_blocks'] for b in built]+[aux['gram_blocks']]
        storage=[b['storage_blocks'] for b in built]+[aux['storage_blocks']]
        out.update(TRACE.metadata(built,instances,blocks,storage))
        columns,lhs,monomials,shape,offset,_,specs=S.prepare(instances,blocks,storage,gram_specs=P.gram_specs(),deadline=deadline,**COMPILER_LIMITS)
        retained,recipes=PROJECT.full15_recipes(shape,offset,specs,len(columns))
        if (len(columns),len(monomials),len(retained),len(recipes))!=(1957,5641,1224,733):raise ValueError('complete published primal geometry')
        compilation=S.compilation_charge(instances,blocks,columns)
        out.update(complete_columns=len(columns),complete_monomials=len(monomials),projected_columns=len(retained),
            compilation_work_reserve=compilation,exact_columns_hash=R.digest([[[list(m),str(q)] for m,q in sorted(p.items())] for p in columns]),
            exact_target_hash=R.digest([[list(m),str(q)] for m,q in sorted(lhs.items())]))
        out.update(process_equations(columns,lhs,monomials,retained,recipes,directory=d/'jobs',deadline=deadline,compilation_work_reserve=compilation))
    except (OverflowError,TimeoutError,MemoryError,ImportError) as e:out.update(status='missing_resource',reason=str(e) or type(e).__name__)
    except (ValueError,TypeError,KeyError,RuntimeError,ZeroDivisionError) as e:out.update(status='rejected',reason=str(e) or type(e).__name__)
    out['cost']=dict(elapsed_seconds=time.monotonic()-start,cpu_seconds=time.process_time()-cpu,
        peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        observed_threads_at_completion=len(list(Path('/proc/self/task').iterdir())),pid=os.getpid())
    out['deadline_exceeded']=time.monotonic()>deadline
    validate(d);path=d/'jobs/primal.json';bounded_write(path,out,LIMITS['max_metadata_bytes'])
    return dict(file=str(path.relative_to(d)),sha256=R.sha(path),status=out['status'],cost=out['cost'],**FLAGS)


def run(directory):
    require_verified_runtime();d=Path(directory).resolve();validate(d)
    with (d/'run_started.json').open('x') as f:json.dump(dict(protocol_sha256=R.sha(d/'protocol.json')),f)
    tests=subprocess.run([sys.executable,'-B','-m','unittest',*TESTS],cwd=ROOT,capture_output=True,text=True,timeout=180)
    R.write(d/'tests.json',dict(returncode=tests.returncode,stdout=tests.stdout,stderr=tests.stderr))
    if tests.returncode:raise ValueError('prescore preprocessing calibration failed')
    jobs=[dict(directory=str(d),phase='primal_preprocessing',index=0)]
    execution=run_jobs(jobs,worker='run_primitive_state_exact_row_basis_probe:worker',**PARALLEL)
    R.write(d/'execution.json',execution);validate(d)
    files={str(p.relative_to(d)):R.sha(p) for p in sorted(d.rglob('*')) if p.is_file() and 'frozen_source' not in p.parts}
    R.write(d/'receipt.json',dict(files_sha256=files,source_count=len(R.read(d/'source_seal.json')),solver_called=False,**FLAGS))
    print(dict(jobs=[r['status'] for r in execution['results']],**FLAGS))


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('command',choices=['freeze','run']);parser.add_argument('directory')
    args=parser.parse_args();(freeze if args.command=='freeze' else run)(args.directory)
