"""One scalar-first exact recovery under the original unspent final-audit reserve.

The numerical proposal is unchanged. A negative nonnegative coordinate rejects
only this explicit exact point; PSD is then deliberately not evaluated. All
result rationals remain capped at4096 bits. No hashes or tape replay are used.
"""
from fractions import Fraction as F
import argparse
import contextvars
import json
import math
import os
from pathlib import Path
import re
import resource
import time
import check_primitive_state_backtracking_cone_search as CORE
import check_primitive_state_backtracking_cone_search_run as ORIGINAL

ROOT=Path(__file__).resolve().parent
FLAGS=CORE.FLAGS
require=CORE.require
POLICY=dict(reconstruction='same exact024 center plus saved final269bit z; cached780-row descending backsub and canonical1957 lift',equations='all5641 original equations plus learned023 row, before cone rejection',scalars='all1597 licensed nonnegative original coordinates',PSD='skip all three blocks after any exact negative scalar; otherwise check all three exact15x15 blocks',result_bits=4096,temporary_bits=8193,scope='this explicit recovered point only; original producer remains UNKNOWN')
SCHEMA='primitive-state-backtracking-recovery-independent-review-v1'
ENDPOINT_SCHEMA='primitive-state-backtracking-recovered-endpoint-v1'
RECOVERY_TESTS=['test_check_primitive_state_backtracking_recovery','test_primitive_state_backtracking_recovery_soundness','test_publish_cancellation_primitive_state_backtracking_recovery']
RECOVERY_FILES=['check_primitive_state_backtracking_recovery.py','test_check_primitive_state_backtracking_recovery.py','primitive_state_backtracking_recovery_resource_scope.txt']
_IO=contextvars.ContextVar('backtracking_recovery_io',default=None)


def recovery_protocol():
    return dict(schema='primitive-state-backtracking-recovery-protocol-v1',tests=RECOVERY_TESTS,policy=POLICY,original_protocol_unchanged=True,original_producer_required_status='UNKNOWN',original_failure_reason='rational result bit cap',original_failure_type='OverflowError',failed_result_bits_min=4097,failed_result_bits_max=8193,max_operations=150000000,max_cells=6000000,max_fill_cells=20000000,max_coefficient_bits=4096,max_endpoint_bytes=2097152,max_review_bytes=65536,max_metadata_bytes=65536,max_tests_bytes=1048576,cooperative_seconds=3600,memory_bytes=6*1024**3,joint_work=dict(max_work=450000000,preparation=50000000,map_setup=5000000,proposal=220000000,exact_endpoint=25000000,final_independent=150000000),no_second_final_audit=True,no_new_proposal=True,no_hashes=True,**FLAGS)


def read(path,cap=1048576):
    require(type(cap)is int and 0<cap<=33554432,'bounded recovery mathematical input')
    with Path(path).open('rb')as f:data=f.read(cap+1)
    if len(data)>cap:raise OverflowError('recovery input byte cap')
    io=_IO.get()
    if io is not None:
        io[0]+=2*(len(data)//64+1);io[1]+=len(data)
        if io[0]>10000000:raise OverflowError('recovery IO reserve within original preparation')
        if time.monotonic()>io[2]:raise TimeoutError('recovery input deadline')
    return json.loads(data)


def validate_failed_endpoint(endpoint,proposal):
    require(type(endpoint)is dict and endpoint.get('schema')=='primitive-state-backtracking-cone-endpoint-v1'and endpoint.get('complete')is False and endpoint.get('reason')=='rational result bit cap'and endpoint.get('error_type')=='OverflowError','specific incomplete producer result-bit failure')
    CORE.false_flags(endpoint);require(all(endpoint.get(k)is False for k in FLAGS),'failed producer cannot certify any result')
    require(endpoint.get('candidate_original_vector')is None and endpoint.get('final_projected_vector')is None and endpoint.get('diagnostics')is None,'failed producer retained no complete original vector or PSD verdict')
    require(endpoint.get('free_indices')==proposal.get('free_indices')and endpoint.get('limits')==dict(max_operations=25000000,max_coefficient_bits=4096,max_endpoint_bytes=2097152),'original failure coordinate/cap binding')
    counts=endpoint.get('counts');require(type(counts)is dict and set(counts)=={'operations','peak_live_cells','maximum_rational_bits'},'explicit failed counters')
    require(type(counts['operations'])is int and 0<=counts['operations']<=25000000 and type(counts['peak_live_cells'])is int and 0<=counts['peak_live_cells']<=6000000 and type(counts['maximum_rational_bits'])is int and 4096<counts['maximum_rational_bits']<=8193,'first violating result recorded only on failed diagnostic')
    require(proposal.get('schema')==CORE.SCHEMA and proposal.get('status')=='proposed'and proposal.get('complete')is True,'only a complete saved numerical proposal is recovered')


def scalar_first_endpoint(full,rhs,newrow,newrhs,x,b):
    """Check every equation and sign; PSD is unnecessary after scalar rejection."""
    require(len(full)==len(rhs)==5641 and len(newrow)==len(x)==1957,'full original equation and coordinate scope')
    x=[b.rational(q)for q in x];mismatches=[]
    for i,(row,target)in enumerate(zip(full,rhs)):
        value=F(0)
        for j,q in row.items():value=b.add(value,b.mul(q,x[j]))
        if value!=target:mismatches.append(dict(row=i,residual=str(b.add(value,-target))))
    value=F(0)
    for q,v in zip(newrow,x):value=b.add(value,b.mul(q,v))
    newres=b.add(value,-newrhs);b.charge(1597)
    negatives=[dict(coordinate=i,value=str(x[i]))for i in range(1597)if x[i]<0]
    require(not mismatches and newres==0,'all5641 original and learned equations exactly zero')
    if negatives:
        psd=None;psd_status='NOT_CHECKED_AFTER_SCALAR_REJECTION';feasible=False;checked=0;failures=None
    else:
        psd=[]
        for k,name in enumerate(('full_child','full_parent','storage_K')):
            matrix=[[F(0)]*15 for _ in range(15)];position=1597+120*k
            for i in range(15):
                for j in range(i,15):matrix[i][j]=matrix[j][i]=x[position];position+=1
            psd.append(dict(name=name,**CORE.AFFINE.exact_psd(matrix,b)))
        psd_status='ALL_THREE_EXACT_BLOCKS_CHECKED';checked=3;failures=sum(not v['psd']for v in psd);feasible=failures==0
    return dict(full_original_rows_checked=5641,original_equation_mismatches=mismatches,feedback_row_verified=True,new_equation_residual=str(newres),candidate_equations_verified=True,negative_scalars=negatives,negative_scalar_count=len(negatives),scalar_rejection_witness=negatives[0]if negatives else None,psd_status=psd_status,psd_blocks=psd,PSD_blocks_checked=checked,PSD_failures=failures,finite_candidate_feasible=feasible)


def recover(cache,chart,center,necessary,review024,prior_map,prior_proposal,prior_endpoint,review025,mapreceipt,proposal,failed_endpoint,*,deadline=None,max_operations=150000000,max_cells=6000000,max_coefficient_bits=4096):
    require(type(max_operations)is int and 0<max_operations<=150000000,'original single150m final independent reserve')
    validate_failed_endpoint(failed_endpoint,proposal)
    b=CORE.Budget(time.monotonic()+3600 if deadline is None else deadline,max_operations,max_cells,20000000,max_coefficient_bits)
    license=CORE.warm_license(cache,chart,center,necessary,review024,prior_map,prior_proposal,prior_endpoint,review025,b)
    setup=CORE.verify_setup(license,mapreceipt,b);trace=CORE.verify_proposal_trace(license,proposal,b,max_trace_bytes=33554432);require(trace['complete']is True,'complete independently checked saved proposal')
    z=CORE._vector(proposal['final_z_mp'],444,b);free=[b.add(license.parent_vector[i],b.mul(D,v))for i,D,v in zip(license.free,license.scales,z)]
    require(proposal.get('final_free_vector')==list(map(str,free)),'no rounded endpoint substitution')
    seed=license.parent_vector[:]
    for i,q in zip(license.free,free):seed[i]=q
    y=CORE.AFFINE.backsubstitute(license.rows,seed,b);x=CORE.AFFINE.lift(y,license.retained,b)
    declaration=dict(complete=True,status='complete',original_columns=1957,projected_columns=1224,rows=len(cache['original']['rhs']),retained_indices=license.retained,recipes=[[i,[[j,str(q)]for j,q in sorted(recipe.items())]]for i,recipe in sorted(license.recipes.items())])
    full,_,rhs,_,_=CORE.AFFINE.decode_source(cache,declaration,b)
    diagnostics=scalar_first_endpoint(full,rhs,license.feedback_full,license.feedback_rhs,x,b)
    endpoint=dict(schema=ENDPOINT_SCHEMA,complete=True,policy=POLICY,free_indices=license.free,final_free_vector=list(map(str,free)),final_projected_vector=list(map(str,y)),candidate_original_vector=list(map(str,x)),diagnostics=diagnostics,**FLAGS)
    data=CORE.encoded(endpoint)
    if len(data)>2097152:raise OverflowError('bounded explicit recovered endpoint')
    b.charge(2*(len(data)//64+1))
    search=dict(verified=True,complete=True,endpoint_verified=True,candidate_equations_verified=True,finite_candidate_feasible=diagnostics['finite_candidate_feasible'],full_original_rows_checked=5641,feedback_row_verified=True,chart_used_without_old_tape_replay=True,trace_exports_checked=True,setup_check=setup,trace_check=trace,accepted_iterations=trace['accepted_iterations'],stop_reason=trace['stop_reason'],initial_objective=trace['initial_objective'],final_objective=trace['final_objective'],initial_block_penalties=trace['initial_block_penalties'],final_block_penalties=trace['final_block_penalties'],**FLAGS)
    summary={k:diagnostics[k]for k in ('full_original_rows_checked','feedback_row_verified','candidate_equations_verified','negative_scalar_count','psd_status','PSD_blocks_checked','PSD_failures','finite_candidate_feasible','scalar_rejection_witness')}
    summary.update(verified=True,complete=True,endpoint_verified=True,audit_operations=b.operations,audit_cells=b.audit_cells,peak_live_cells=b.peak_live_cells,strict_result_bits=4096,**FLAGS)
    return endpoint,dict(independent_search_check=search,recovery_check=summary)


def _audit(directory,*,deadline,max_operations,max_cells):
    d=Path(directory)
    require(read(d/'recovery_protocol.json',65536)==recovery_protocol(),'fixed scalar-first recovery policy and original joint allocation')
    ORIGINAL.verify_protocol(read(d/'protocol.json',65536));require(read(d/'parent.json',65536)==ORIGINAL.parent(),'actual designated024/025 mathematical inputs')
    tests=read(d/'recovery_tests.json');match=re.search(r'Ran (\d+) tests?',tests.get('stderr',''));require(tests.get('returncode')==0 and match and tests['stderr'].rstrip().endswith('OK'),'new bounded recovery synthetic tests passed')
    oldtests=read(d/'tests.json');require(oldtests.get('returncode')==0 and oldtests.get('stderr','').rstrip().endswith('OK'),'original frozen tests passed')
    require(read(d/'run_started.json',65536)==dict(one_fixed_search=True),'one original numerical proposal')
    mapreceipt=read(d/'jobs/map.json',8388608);proposal=read(d/'jobs/proposal.json',33554432);failed=read(d/'jobs/endpoint.json',2097152)
    execution=read(d/'execution.json');original_io=ORIGINAL._IO.set(_IO.get())
    try:job=ORIGINAL.verify_job(d,execution,mapreceipt,proposal,failed)
    finally:ORIGINAL._IO.reset(original_io)
    record=read(d/'jobs/search-job.json',65536);progress=read(d/'jobs/progress.json',65536)
    require(job['transport_status']=='available'and record.get('status')=='UNKNOWN'and record.get('producer_complete')is True and record.get('endpoint_complete')is False and record.get('deadline_exceeded')is False and record.get('reason')=='rational result bit cap','only completed original proposal with specific failed endpoint can consume recovery reserve')
    require(record['cost']['elapsed_seconds']<=3600 and record['cost']['peak_rss_kib']<=6*1024**2,'original worker within declared bounds')
    require(progress.get('phase')=='terminal_UNKNOWN'and progress.get('artifacts')==record.get('artifacts')==dict(map='map.json',proposal='proposal.json',endpoint='endpoint.json'),'original failed-endpoint terminal commitment')
    stage=dict(map_setup=mapreceipt['counts'],proposal=proposal['counts'],exact_endpoint=failed['counts']);require(record.get('stage_counts')==progress.get('stage_counts')==stage and record.get('stop_reason')==proposal.get('stop_reason'),'actual stage evidence/counts and stopping reason')
    CORE.CACHED._phase_counts(mapreceipt,5000000);CORE.CACHED._phase_counts(proposal,220000000);validate_failed_endpoint(failed,proposal)
    report024=read(ROOT/(ORIGINAL.PUBLICATION+'/report.json'));require(report024.get('schema')==24 and report024.get('chart_verified')is True and report024.get('candidate_equations_verified')is True and report024.get('independent_audit_complete')is True and report024.get('classification')=='independent'and report024.get('coefficient_rank')==780 and report024.get('augmented_rank')==780 and report024.get('free_count')==444 and report024.get('chosen_pivot')==148 and report024.get('chart_path')==ORIGINAL.CHART and report024.get('affine_receipt_path')==ORIGINAL.AFFINE,'designated published024 exact chart/center premise')
    report025=read(ROOT/(ORIGINAL.WARM_PUBLICATION+'/report.json'));require(report025.get('schema')==25 and report025.get('independent_audit_complete')is True and report025.get('endpoint_verified')is True and report025.get('candidate_equations_verified')is True and report025.get('stop_reason')=='line_search_failed','designated completed025 warm point premise')
    inputs=tuple(read(ROOT/name,ORIGINAL.CAPS[name])for name in(ORIGINAL.CACHE,ORIGINAL.CHART,ORIGINAL.AFFINE,ORIGINAL.CONSTRAINT,ORIGINAL.REVIEW,ORIGINAL.MAP,ORIGINAL.PROPOSAL,ORIGINAL.ENDPOINT,ORIGINAL.WARM_REVIEW))
    endpoint,checks=recover(*inputs,mapreceipt,proposal,failed,deadline=deadline,max_operations=max_operations,max_cells=max_cells)
    recovery=checks['recovery_check'];status='RECOVERED_SCALAR_REJECTED'if recovery['negative_scalar_count']else'RECOVERED_CONE_CHECKED'
    result=dict(schema=SCHEMA,all_passed=True,status=status,policy=POLICY,original_producer_status='UNKNOWN',original_proposal_complete=True,original_endpoint_complete=False,endpoint_verified=True,candidate_equations_verified=True,finite_candidate_feasible=recovery['finite_candidate_feasible'],**checks,tests_passed=int(match.group(1)),joint_work=dict(max_work=450000000,total_work_reserve=450000000,preparation_reserved=50000000,map_setup_reserved=5000000,proposal_reserved=220000000,exact_endpoint_reserved=25000000,independent_reserved=150000000,independent_operations=recovery['audit_operations'],independent_io_operations=_IO.get()[0],independent_io_bytes=_IO.get()[1],independent_io_reserve_within_preparation=10000000,second_final_audit=False),resource_failure=None,**FLAGS)
    if time.monotonic()>deadline:raise TimeoutError('final recovery deadline')
    return endpoint,result


def audit(directory,*,write=False,time_limit=3600,max_operations=150000000,max_cells=6000000):
    require(type(time_limit)in(int,float)and math.isfinite(time_limit)and 0<time_limit<=3600,'strict independent recovery deadline')
    for v,cap in((max_operations,150000000),(max_cells,6000000)):require(type(v)is int and 0<v<=cap,'strict original final-audit caps')
    d=Path(directory);review_path=d/'independent_recovery_verification.json';endpoint_path=d/'recovered-endpoint.json'
    require(not(d/'independent_verification.json').exists(),'original final audit must be unspent')
    for path in(review_path,endpoint_path,d/'recovery_started.json'):
        if path.exists():raise FileExistsError('recovery final-audit reserve already started or used')
    old=resource.getrlimit(resource.RLIMIT_AS);memory=6*1024**3;require(old[1]==resource.RLIM_INFINITY or old[1]>=memory,'supported6GiB recovery boundary')
    start=time.monotonic();cpu=time.process_time();deadline=start+time_limit;token=_IO.set([0,0,deadline]);endpoint=None
    with(d/'recovery_started.json').open('x')as f:json.dump(dict(schema='primitive-state-backtracking-recovery-started-v1',uses_original_final_independent_reserve=True,second_final_audit=False,pid=os.getpid()),f)
    try:
        resource.setrlimit(resource.RLIMIT_AS,(memory,old[1]))
        try:endpoint,result=_audit(d,deadline=deadline,max_operations=max_operations,max_cells=max_cells)
        except(OverflowError,TimeoutError,MemoryError)as error:
            result=dict(schema=SCHEMA,all_passed=False,status='UNKNOWN',policy=POLICY,original_producer_status='UNKNOWN',original_endpoint_complete=False,endpoint_verified=False,candidate_equations_verified=False,finite_candidate_feasible=None,independent_search_check=None,recovery_check=None,resource_failure=dict(reason=str(error)or type(error).__name__,error_type=type(error).__name__),joint_work=dict(max_work=450000000,total_work_reserve=450000000,independent_reserved=150000000,independent_operations=None,independent_io_operations=_IO.get()[0],independent_io_bytes=_IO.get()[1],second_final_audit=False),**FLAGS)
        result['cost']=dict(elapsed_seconds=time.monotonic()-start,cpu_seconds=time.process_time()-cpu,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,pid=os.getpid(),observed_threads_at_completion=len(list(Path('/proc/self/task').iterdir())),audit_memory_limit_bytes=memory,audit_memory_limit_enforced=True,memory_boundary='restorable soft RLIMIT_AS')
        if time.monotonic()>deadline:
            endpoint=None;result.update(all_passed=False,status='UNKNOWN',endpoint_verified=False,candidate_equations_verified=False,finite_candidate_feasible=None,resource_failure=dict(reason='final recovery cost deadline',error_type='TimeoutError'))
        data=CORE.encoded(result)
        if len(data)>65536:
            endpoint=None;result=dict(schema=SCHEMA,all_passed=False,status='UNKNOWN',endpoint_verified=False,candidate_equations_verified=False,finite_candidate_feasible=None,recovery_check=None,independent_search_check=None,resource_failure=dict(reason='recovery review byte cap',error_type='OverflowError'),joint_work=dict(max_work=450000000,total_work_reserve=450000000,independent_reserved=150000000,second_final_audit=False),cost=result['cost'],**FLAGS);data=CORE.encoded(result)
        if write:
            if endpoint is not None:
                payload=CORE.encoded(endpoint);require(len(payload)<=2097152,'recovered endpoint output cap')
                with endpoint_path.open('xb')as f:f.write(payload)
            with review_path.open('xb')as f:f.write(data)
        if time.monotonic()>deadline:
            result.update(all_passed=False,status='UNKNOWN',endpoint_verified=False,candidate_equations_verified=False,finite_candidate_feasible=None,resource_failure=dict(reason='final recovery output deadline',error_type='TimeoutError'))
            if write:review_path.write_bytes(CORE.encoded(result))
        return result
    finally:
        resource.setrlimit(resource.RLIMIT_AS,old);_IO.reset(token);require(resource.getrlimit(resource.RLIMIT_AS)==old,'restored independent memory boundary')

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('directory');p.add_argument('--write',action='store_true');a=p.parse_args();result=audit(a.directory,write=a.write);print(json.dumps({k:result.get(k)for k in('schema','all_passed','status','endpoint_verified','candidate_equations_verified','finite_candidate_feasible','recovery_check','resource_failure','joint_work','cost')},sort_keys=True))
