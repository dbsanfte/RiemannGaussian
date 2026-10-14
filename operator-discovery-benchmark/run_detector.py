#!/usr/bin/env python3
"""Resource-bounded multicore entrypoint for future factor scalar-cone searches.

search freezes a JSON configuration, searches candidate programs in parallel,
seals accepted weights, then checks those unchanged weights at the final scales.
transfer audits an existing attempt at new scales without fitting. The historical
full-Gram and other stage workflows remain available through legacy.
"""
import argparse
import ast
import hashlib
import importlib.metadata
import json
import os
from pathlib import Path
import resource
import sys
import time
from detector_workflow_guard import require_verified_runtime

BASE = Path(__file__).resolve().parent
FLAGS = dict(global_bound_proved=False, RH_proved=False)
_COLUMN_CACHE = None
DEFAULT_LIMITS = dict(max_columns=1024,max_monomials=30000,max_operations=200000000,
                      max_coefficient_bits=4096,max_horizon=80,max_degree=12,
                      max_denominator=1000000,time_limit=180)


def read(path): return json.loads(Path(path).read_text())
def digest(value): return hashlib.sha256(json.dumps(value,sort_keys=True,separators=(',',':'),allow_nan=False).encode()).hexdigest()
def sha(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def write(path,value):
    path=Path(path)
    with path.open('x') as f: json.dump(value,f,sort_keys=True,indent=2,allow_nan=False)


def source_closure():
    # Statically include local imports, including function-local imports used only
    # in spawned workers. Every file actually imported is checked again at runtime.
    pending=['run_detector','detector_parallel','cancellation_sparse_synthesis',
             'check_cancellation_factor_search','check_grouped_arithmetic_sparse']
    seen=set()
    while pending:
        name=pending.pop(); path=BASE/(name+'.py')
        if name in seen or not path.is_file(): continue
        seen.add(name)
        for node in ast.walk(ast.parse(path.read_text())):
            if isinstance(node,ast.Import): pending.extend(a.name.split('.')[0] for a in node.names)
            elif isinstance(node,ast.ImportFrom) and node.module: pending.append(node.module.split('.')[0])
    return sorted(n+'.py' for n in seen)


def validate_sources(directory):
    directory=Path(directory); seal=read(directory/'source_seal.json')
    if read(directory/'seal.json') != dict(protocol_sha256=sha(directory/'protocol.json'),
                                          source_seal_sha256=sha(directory/'source_seal.json'),
                                          input_sha256=sha(directory/'input.json')):
        raise ValueError('run seal changed')
    for name,value in seal.items():
        if sha(BASE/name)!=value or sha(directory/'frozen_source'/name)!=value:
            raise ValueError('source changed: '+name)
    for module in list(sys.modules.values()):
        filename=getattr(module,'__file__',None)
        if filename:
            p=Path(filename).resolve()
            if p.parent==BASE and p.suffix=='.py' and p.name not in seal:
                raise ValueError('import outside frozen source closure: '+p.name)


def freeze(directory,protocol,input_value):
    require_verified_runtime(); directory=Path(directory).resolve()
    directory.mkdir(parents=True,exist_ok=False); (directory/'frozen_source').mkdir()
    sources={}
    for name in source_closure():
        data=(BASE/name).read_bytes(); (directory/'frozen_source'/name).write_bytes(data)
        sources[name]=hashlib.sha256(data).hexdigest()
    write(directory/'input.json',input_value); write(directory/'protocol.json',protocol)
    write(directory/'source_seal.json',sources)
    write(directory/'seal.json',dict(protocol_sha256=sha(directory/'protocol.json'),
        source_seal_sha256=sha(directory/'source_seal.json'),input_sha256=sha(directory/'input.json')))
    (directory/'jobs').mkdir(); return directory


def execute_job(job):
    global _COLUMN_CACHE
    require_verified_runtime()
    directory=Path(job['directory']); validate_sources(directory)
    protocol=read(directory/'protocol.json'); inputs=read(directory/'input.json')
    import check_cancellation_factor_search as B
    import check_grouped_arithmetic_sparse as CHECK
    from grouped_arithmetic_sparse import instantiate_details
    from cancellation_sparse_synthesis import synthesize
    from exact_polynomial_column_cache import ColumnCache
    start=time.monotonic(); cpu=time.process_time()
    limits=protocol['limits']; phase=job['phase']; index=job['index']
    record=dict(phase=phase,index=index,refitted=False,grams_fixed_zero=True,**FLAGS)
    try:
        if phase=='train':
            program=inputs['programs'][index]; scales=protocol['training_scales']
            allow_slack=program['allow_constant_slack']
            instances=[]; case_hashes=[]; archives=[]
            for X in scales:
                b=B.build(program,X); instances.append(b['instance'])
                case_hashes.append(CHECK.digest(b['instance']));archives.append(CHECK.digest(b['factor_archive']))
            if program['constraint']=='zero_cubic': instances.append(B.auxiliary()['instance'])
            hashes=[CHECK.digest(i) for i in instances]
            if _COLUMN_CACHE is None:
                _COLUMN_CACHE=ColumnCache(max_entries=2,max_cached_coefficients=250000)
            result=synthesize(instances,allow_constant_slack=allow_slack,column_cache=_COLUMN_CACHE,**limits)
            checked=CHECK.verify_joint_result(instances,result,allow_constant_slack=allow_slack,
                       expected_instance_sha256=hashes,time_limit=protocol['audit_seconds'],max_operations=limits['max_operations'])
            record.update(program=program,scales=scales,case_sha256=case_hashes,
                instance_sha256=hashes,factor_archive_sha256=archives,synthesis=result,independent_check=checked)
        else:
            if protocol['mode']=='transfer':
                attempt=inputs['attempt']; X=protocol['final_scales'][index]
            else:
                if sha(directory/'candidate_seal.json')!=job['candidate_seal_sha256']:
                    raise ValueError('candidate seal changed')
                plan=read(directory/'candidate_seal.json')
                if plan['training_receipts_sha256']!=sha(directory/'training_receipts.json'):
                    raise ValueError('training receipts changed')
                spec=plan['final_jobs'][index]; path=directory/spec['attempt_file']
                if sha(path)!=spec['attempt_sha256']: raise ValueError('candidate changed after sealing')
                attempt=read(path); X=spec['X']
            if attempt['synthesis']['status']!='finite_certificate': raise ValueError('accepted finite candidate required')
            program=attempt['program']; weights=attempt['synthesis']['weights']
            allow_slack=program['allow_constant_slack']
            b=B.build(program,X); inst=b['instance']; h=CHECK.digest(inst)
            details=instantiate_details(inst,weights,allow_constant_slack=allow_slack,**limits)
            result=dict(status='finite_certificate',weights=weights,certificates=[details['certificate']],
                        constant_slacks=[details['constant_slack']] if allow_slack else [],allow_constant_slack=allow_slack,**FLAGS)
            checked=CHECK.verify_joint_result([inst],result,allow_constant_slack=allow_slack,
                        expected_instance_sha256=[h],time_limit=protocol['audit_seconds'],max_operations=limits['max_operations'])
            record.update(program=program,X=X,case_sha256=h,factor_archive_sha256=CHECK.digest(b['factor_archive']),
                          weights_sha256=CHECK.digest(weights),synthesis=result,independent_check=checked,
                          instantiation=details['diagnostics'])
            if protocol['mode']=='search' and sha(directory/'candidate_seal.json')!=job['candidate_seal_sha256']:
                raise ValueError('candidate seal changed during transfer')
        record['dictionary_sha256']=CHECK.digest(B.descriptors())
        record['status']=record['synthesis']['status']
    except (OverflowError,TimeoutError,MemoryError,ImportError) as e:
        record.update(status='missing_resource',reason=str(e) or type(e).__name__)
    except (ValueError,TypeError,KeyError,ZeroDivisionError,RuntimeError) as e:
        record.update(status='rejected',reason=str(e) or type(e).__name__)
    record['cost']=dict(elapsed_seconds=time.monotonic()-start,cpu_seconds=time.process_time()-cpu,
        peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,pid=os.getpid(),
        observed_threads_at_completion=len(list(Path('/proc/self/task').iterdir())) if Path('/proc/self/task').is_dir() else None)
    validate_sources(directory)
    filename=f'jobs/{phase}-{index:04d}.json'; write(directory/filename,record)
    return dict(status=record['status'],file=filename,sha256=sha(directory/filename),cost=record['cost'],**FLAGS)


def dispatch(directory,phase,count,protocol):
    from detector_parallel import run_jobs
    jobs=[dict(directory=str(directory),phase=phase,index=i) for i in range(count)]
    candidate_sha=None
    if phase=='final' and protocol['mode']=='search':
        candidate_sha=sha(directory/'candidate_seal.json')
        for job in jobs: job['candidate_seal_sha256']=candidate_sha
    result=run_jobs(jobs,worker='run_detector:execute_job',**protocol['parallel'])
    if candidate_sha and sha(directory/'candidate_seal.json')!=candidate_sha:
        raise ValueError('candidate seal changed during final dispatch')
    return result


def execute(directory):
    directory=Path(directory); validate_sources(directory)
    protocol=read(directory/'protocol.json'); inputs=read(directory/'input.json')
    if (directory/'started.json').exists(): raise FileExistsError('run already started; use a fresh destination')
    write(directory/'started.json',dict(protocol_sha256=sha(directory/'protocol.json')))
    if protocol['mode']=='search':
        training=dispatch(directory,'train',len(inputs['programs']),protocol)
        write(directory/'training_receipts.json',training); final_jobs=[]
        for receipt in training['results']:
            if receipt['status']!='available' or receipt['value']['status']!='finite_certificate': continue
            value=receipt['value']; attempt=read(directory/value['file'])
            if sha(directory/value['file'])!=value['sha256'] or not attempt['independent_check']['verified']:
                raise ValueError('accepted training receipt mismatch')
            for X in protocol['final_scales']:
                final_jobs.append(dict(attempt_file=value['file'],attempt_sha256=value['sha256'],X=X))
        write(directory/'candidate_seal.json',dict(training_receipts_sha256=sha(directory/'training_receipts.json'),final_jobs=final_jobs))
        count=len(final_jobs)
    else: count=len(protocol['final_scales'])
    final=dispatch(directory,'final',count,protocol); write(directory/'final_receipts.json',final)
    validate_sources(directory)
    files={str(p.relative_to(directory)):sha(p) for p in sorted(directory.rglob('*.json')) if p.is_file()}
    summary=dict(mode=protocol['mode'],files_sha256=files,final_jobs=count,
        accepted_finite_checks=sum(r['status']=='available' and r['value']['status']=='finite_certificate' for r in final['results']),
        final_cost=final['cost'],original_results_preserved=True,refitted=False,grams_fixed_zero=True,
        scope='finite scalar-cone search/evaluation only; no full-Gram exclusion or all-scale estimate',**FLAGS)
    write(directory/'receipt.json',summary)
    print(json.dumps(dict(directory=str(directory),final_jobs=count,accepted_finite_checks=summary['accepted_finite_checks'],cost=final['cost'],**FLAGS),indent=2))
    return summary


def scales(value):
    if type(value)is not list or not value or any(type(x)is not int or x<1 for x in value) or len(set(value))!=len(value):
        raise ValueError('positive unique scale list')
    return value


def main():
    require_verified_runtime()
    p=argparse.ArgumentParser(description=__doc__); sub=p.add_subparsers(dest='command',required=True)
    for mode in ('search','transfer'):
        a=sub.add_parser(mode);a.add_argument('--input',type=Path,required=True);a.add_argument('--out',type=Path,required=True)
        a.add_argument('--workers',type=int,default=4);a.add_argument('--worker-memory-mib',type=int,default=1024)
        a.add_argument('--memory-budget-mib',type=int,default=4096);a.add_argument('--timeout',type=float,default=600)
        a.add_argument('--scales',type=int,nargs='+',default=[7,11]);a.add_argument('--time-limit',type=float,default=180)
    legacy=sub.add_parser('legacy');legacy.add_argument('args',nargs=argparse.REMAINDER)
    args=p.parse_args()
    if args.command=='legacy':
        import subprocess
        forwarded=args.args[1:] if args.args[:1]==['--'] else args.args
        raise SystemExit(subprocess.call([sys.executable,str(BASE/'run_expanded_probe.py'),*forwarded],cwd=BASE))
    value=read(args.input)
    if args.command=='transfer':
        if value.get('synthesis',{}).get('status')!='finite_certificate': raise ValueError('finite attempt input required')
        if type(value.get('program',{}).get('allow_constant_slack'))is not bool: raise ValueError('explicit boolean slack policy required')
        inputs=dict(attempt=value); training_scales=[]; final_scales=scales(args.scales); limits=dict(DEFAULT_LIMITS,time_limit=args.time_limit)
    else:
        if type(value.get('programs'))is not list or not value['programs']: raise ValueError('nonempty programs required')
        for program in value['programs']:
            if program.get('dictionary_mode')!='extended' or program.get('constraint') not in ('none','zero_cubic'):
                raise ValueError('extended factor dictionary and explicit constraint required')
            if type(program.get('allow_constant_slack'))is not bool: raise ValueError('explicit boolean slack policy required')
        inputs=dict(programs=value['programs']);training_scales=scales(value['training_scales'])
        final_scales=scales(value['final_scales']);limits=dict(DEFAULT_LIMITS,**value.get('limits',{}))
        if set(limits)!=set(DEFAULT_LIMITS): raise ValueError('known solver limits required')
    for v in (args.workers,args.worker_memory_mib,args.memory_budget_mib):
        if v<1: raise ValueError('positive process resources')
    if args.memory_budget_mib<args.worker_memory_mib: raise ValueError('budget must fit a worker')
    protocol=dict(schema=1,mode=args.command,training_scales=training_scales,final_scales=final_scales,limits=limits,
        audit_seconds=args.time_limit,input_source=str(args.input.resolve()),input_source_sha256=sha(args.input),
        parallel=dict(workers=args.workers,worker_memory_bytes=args.worker_memory_mib*1048576,
                      memory_budget_bytes=args.memory_budget_mib*1048576,timeout_seconds=args.timeout,
                      max_result_bytes=65536,max_jobs=256),
        source_builder='calibrated checker factor builder used for construction; separate independent certificate algebra audit',
        runtime=dict(python=sys.version,packages={name:importlib.metadata.version(name) for name in ('scipy','numpy','python-flint')}),
        grams_fixed_zero=True,final_refit=False,**FLAGS)
    execute(freeze(args.out,protocol,inputs))

if __name__=='__main__': main()
