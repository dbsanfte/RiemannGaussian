"""Generic immutable review planning; dispatch and mathematical adjudication external.

Requested model metadata is not authenticated runtime model identity. Collection
checks provenance/completeness only and never promotes mathematical conclusions.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import sys
import tempfile

STATUSES = frozenset({'unresolved', 'conditional', 'stored_refutation',
                      'global_refutation', 'new_proposal'})
REQUESTED_MODEL = 'gpt-6.1-sol'


def optimization_guard():
    if sys.flags.optimize or os.environ.get('PYTHONOPTIMIZE', '') not in ('', '0'):
        raise RuntimeError('review orchestration requires nonoptimized Python and PYTHONOPTIMIZE unset, empty or zero')


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def read(path):
    return json.loads(Path(path).read_text())


def write_new(path, value):
    with Path(path).open('x') as stream:
        stream.write(json.dumps(value, indent=2)+'\n')


def safe_child(root, relative):
    if not isinstance(relative, str) or not relative or Path(relative).is_absolute():
        raise ValueError('relative artifact path required')
    child = (Path(root)/relative).resolve()
    if not child.is_relative_to(Path(root).resolve()):
        raise ValueError('artifact path escapes source directory')
    return child


def refuse_sealed_worker_destination(directory):
    """Guard for wrappers before invoking any worker; no producer is called here."""
    optimization_guard()
    directory = Path(directory)
    markers = ('seal.json', 'verification.json', 'analytical_verification.json',
               'integration_verification.json', 'review_protocol.json', 'collection.json')
    if any((directory/name).exists() for name in markers):
        raise FileExistsError('refusing a sealed or completed worker destination')
    return directory


def source_record(source, queue_name='proof_queue.json'):
    source = Path(source).resolve()
    protocol_path, seal_path = source/'protocol.json', source/'seal.json'
    queue_path = safe_child(source, queue_name)
    protocol, seal, queue = read(protocol_path), read(seal_path), read(queue_path)
    if seal.get('protocol_sha256') != digest(protocol):
        raise ValueError('source seal protocol digest mismatch')
    if queue.get('protocol_sha256', digest(protocol)) != digest(protocol):
        raise ValueError('source queue protocol digest mismatch')
    files = seal.get('files')
    if not isinstance(files, dict) or files.get(queue_name) != sha(queue_path):
        raise ValueError('source queue is not bound by the seal')
    for name, expected in files.items():
        if sha(safe_child(source,name)) != expected:
            raise ValueError('source sealed file changed: '+name)
    keys = [key for key in ('queue','potential_queue') if key in queue]
    if len(keys) != 1 or not isinstance(queue[keys[0]],list) or not queue[keys[0]]:
        raise ValueError('exactly one nonempty supported queue required')
    candidates = []
    for row in queue[keys[0]]:
        pid = row.get('program_id')
        program = row.get('exact_program',row.get('program'))
        claim = row.get('global_claim',row.get('precise_claim'))
        if not isinstance(pid,str) or not pid or program is None or not isinstance(claim,str) or not claim:
            raise ValueError('candidate requires program_id, exact program and exact claim')
        candidates.append({'program_id':pid,'exact_program':program,
                           'exact_program_sha256':digest(program),
                           'precise_claim':claim,'precise_claim_sha256':digest(claim)})
    if len({row['program_id'] for row in candidates}) != len(candidates):
        raise ValueError('duplicate source candidate IDs')
    return {'source_directory':str(source),'queue_name':queue_name,
            'source_protocol_sha256':sha(protocol_path),'source_protocol_digest':digest(protocol),
            'source_seal_sha256':sha(seal_path),'source_queue_sha256':sha(queue_path),
            'source_sealed_files':files,'candidates':sorted(candidates,key=lambda row:row['program_id'])}


def plan(source, destination, workers=3, queue_name='proof_queue.json'):
    optimization_guard()
    if type(workers) is not int or workers < 1:
        raise ValueError('positive integer worker count required')
    source_info = source_record(source,queue_name)
    destination = Path(destination).resolve()
    refuse_sealed_worker_destination(destination)
    if destination.exists():
        raise FileExistsError('review plan requires a fresh destination')
    count = min(workers,len(source_info['candidates']))
    manifest = {'schema':1,**source_info,'requested_reviewer_model':REQUESTED_MODEL,
                'batch_count':count,'allocation':'sorted IDs, round-robin; no numerical selection',
                'dispatch_required_external':True,'runtime_model_independently_verified':False,
                'mathematical_adjudication':'external domain checker required',
                'actual_all_scale_signed_bound_proved':False,'RH_proved':False}
    # Every source check completes before directory reservation.
    destination.mkdir(parents=True,exist_ok=False)
    write_new(destination/'manifest.json',manifest)
    for i in range(count):
        write_new(destination/f'batch-{i+1:02d}.json',{
            'schema':1,'batch':i+1,'manifest_sha256':sha(destination/'manifest.json'),
            'requested_reviewer_model':REQUESTED_MODEL,
            'candidates':source_info['candidates'][i::count],
            'requested_output':f'batch-{i+1:02d}-review.json',
            'allowed_statuses':sorted(STATUSES),'runtime_model_independently_verified':False,
            'global_claims_require_domain_checker':True})
    return manifest


def validate_plan(directory):
    directory = Path(directory).resolve();manifest=read(directory/'manifest.json')
    current=source_record(manifest['source_directory'],manifest['queue_name'])
    for key,value in current.items():
        if manifest.get(key)!=value:
            raise ValueError('planned source changed: '+key)
    if manifest.get('requested_reviewer_model')!=REQUESTED_MODEL or manifest.get('runtime_model_independently_verified') is not False:
        raise ValueError('model request/provenance overclaim')
    count=manifest['batch_count']
    if type(count) is not int or not 1<=count<=len(current['candidates']):
        raise ValueError('invalid batch count')
    for i in range(1,count+1):
        batch=read(directory/f'batch-{i:02d}.json')
        if (batch.get('batch')!=i or batch.get('manifest_sha256')!=sha(directory/'manifest.json') or
            batch.get('candidates')!=current['candidates'][i-1::count] or
            batch.get('requested_output')!=f'batch-{i:02d}-review.json' or
            batch.get('requested_reviewer_model')!=REQUESTED_MODEL or
            batch.get('runtime_model_independently_verified') is not False or
            batch.get('global_claims_require_domain_checker') is not True or
            batch.get('allowed_statuses')!=sorted(STATUSES)):
            raise ValueError('batch differs from frozen deterministic assignment')
    return manifest


def record_receipt(directory, batch, tool_agent_task_name, input_sha256,
                   tool_reported_model=None):
    """Bind an externally observed collaboration dispatch, without authenticating it.

    Caller supplies the actual task name returned by the tool. This API cannot
    independently prove the caller's statement or the runtime model identity.
    """
    optimization_guard();directory=Path(directory).resolve();manifest=validate_plan(directory)
    if type(batch) is not int or not 1<=batch<=manifest['batch_count']:
        raise ValueError('unknown batch')
    if not isinstance(tool_agent_task_name,str) or not tool_agent_task_name.strip():
        raise ValueError('collaboration tool agent task name required')
    batch_path=directory/f'batch-{batch:02d}.json'
    if input_sha256!=sha(batch_path):
        raise ValueError('dispatch input hash mismatch')
    receipt={'schema':1,'batch':batch,'tool_agent_task_name':tool_agent_task_name,
             'input':batch_path.name,'input_sha256':input_sha256,
             'manifest_sha256':sha(directory/'manifest.json'),
             'requested_reviewer_model':REQUESTED_MODEL,
             'tool_reported_model':tool_reported_model,
             'receipt_origin':'external collaboration-tool observation supplied by caller',
             'runtime_model_independently_verified':False}
    write_new(directory/f'batch-{batch:02d}-receipt.json',receipt)
    return receipt


def preflight(directory):
    """Require complete hash-bound reviews/receipts, but do not adjudicate them."""
    optimization_guard();directory=Path(directory).resolve();manifest=validate_plan(directory)
    inputs={'manifest.json':sha(directory/'manifest.json')};seen=set();agents=set()
    for i in range(1,manifest['batch_count']+1):
        bn=f'batch-{i:02d}.json';rn=f'batch-{i:02d}-receipt.json';on=f'batch-{i:02d}-review.json'
        batch,receipt,output=read(directory/bn),read(directory/rn),read(directory/on)
        if (receipt.get('batch')!=i or receipt.get('input')!=bn or receipt.get('input_sha256')!=sha(directory/bn) or
            receipt.get('manifest_sha256')!=sha(directory/'manifest.json') or
            receipt.get('requested_reviewer_model')!=REQUESTED_MODEL or
            receipt.get('runtime_model_independently_verified') is not False):
            raise ValueError('receipt binding mismatch')
        agent=receipt.get('tool_agent_task_name')
        if not isinstance(agent,str) or not agent.strip() or agent in agents:
            raise ValueError('missing or duplicate dispatched task name')
        agents.add(agent)
        if (output.get('batch')!=i or output.get('input_sha256')!=sha(directory/bn) or
            output.get('tool_agent_task_name')!=agent or output.get('runtime_model_independently_verified') is not False):
            raise ValueError('review dispatch/input binding mismatch')
        rows=output.get('reviews');expected={row['program_id']:row for row in batch['candidates']}
        if not isinstance(rows,list) or len(rows)!=len(expected):
            raise ValueError('missing or excess reviews')
        local=set()
        for row in rows:
            pid=row.get('program_id');original=expected.get(pid)
            if original is None or pid in local or pid in seen:
                raise ValueError('duplicate or unassigned review ID')
            local.add(pid);seen.add(pid)
            if (row.get('exact_program_sha256')!=original['exact_program_sha256'] or
                row.get('precise_claim_sha256')!=original['precise_claim_sha256'] or
                row.get('status') not in STATUSES or row.get('original_formula_changed') is not False):
                raise ValueError('review formula/claim/status mismatch')
            if any(row.get(key,False) is not False for key in
                   ('actual_all_scale_signed_bound_proved','RH_proved','independently_verified',
                    'global_bound_proved','global_actual_signed_innovation_bound_proved',
                    'actual_signed_upper_bound_proved','global_proof_verified')):
                raise ValueError('planner reviews cannot promote a mathematical conclusion')
        for name in (bn,rn,on):inputs[name]=sha(directory/name)
    if seen!={row['program_id'] for row in manifest['candidates']}:
        raise ValueError('incomplete queue coverage')
    return {'schema':1,'all_passed':True,'input_sha256':inputs,
            'reviewed_candidates':len(seen),'requested_reviewer_model':REQUESTED_MODEL,
            'runtime_model_independently_verified':False,'domain_adjudication_required':True,
            'mathematical_conclusions_promoted':False,'actual_all_scale_signed_bound_proved':False,'RH_proved':False}


def collect(directory, destination):
    """Freeze completed leads only AFTER full preflight; no mathematical promotion."""
    directory=Path(directory).resolve();destination=Path(destination).resolve()
    result=preflight(directory)
    if destination.exists():raise FileExistsError('collection requires a fresh destination')
    destination.parent.mkdir(parents=True,exist_ok=True)
    stage=Path(tempfile.mkdtemp(prefix='.review-collection-',dir=destination.parent))
    reserved=False
    try:
        for name,expected in result['input_sha256'].items():
            data=(directory/name).read_bytes()
            if hashlib.sha256(data).hexdigest()!=expected:
                raise ValueError('review changed during collection')
            with (stage/name).open('xb') as stream:stream.write(data)
        write_new(stage/'collection.json',result)
        # Atomic reservation prevents replacement of another successful directory.
        destination.mkdir(exist_ok=False);reserved=True
        os.replace(stage,destination)
    except Exception:
        if reserved and destination.is_dir() and not any(destination.iterdir()):
            destination.rmdir()
        raise
    finally:
        if stage.exists():shutil.rmtree(stage)
    return result


def main():
    optimization_guard();parser=argparse.ArgumentParser(description=__doc__)
    sub=parser.add_subparsers(dest='command',required=True)
    p=sub.add_parser('plan');p.add_argument('--source',required=True);p.add_argument('--destination',required=True);p.add_argument('--workers',type=int,default=3);p.add_argument('--queue-name',default='proof_queue.json')
    p=sub.add_parser('preflight');p.add_argument('--plan-dir',required=True)
    p=sub.add_parser('receipt');p.add_argument('--plan-dir',required=True);p.add_argument('--batch',required=True,type=int);p.add_argument('--task-name',required=True);p.add_argument('--input-sha256',required=True);p.add_argument('--tool-reported-model')
    p=sub.add_parser('collect');p.add_argument('--plan-dir',required=True);p.add_argument('--destination',required=True)
    args=parser.parse_args()
    if args.command=='plan':result=plan(args.source,args.destination,args.workers,args.queue_name)
    elif args.command=='preflight':result=preflight(args.plan_dir)
    elif args.command=='receipt':result=record_receipt(args.plan_dir,args.batch,args.task_name,args.input_sha256,args.tool_reported_model)
    else:result=collect(args.plan_dir,args.destination)
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
