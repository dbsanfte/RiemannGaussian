"""Fresh-interpreter/full-import/spawn regression for corrected NEW086 launch.

Only tiny development geometry is evaluated; no scientific fresh draw is made.
The wrapper module and launcher adapter are supplied after its source exists.
"""
import importlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import traceback

ROOT = Path(__file__).resolve().parent
RECEIPT = ROOT/'mobius_arithmetic_bank_audit_086_development.jsonl'
NATIVE_KEYS = ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS',
               'NUMEXPR_NUM_THREADS','VECLIB_MAXIMUM_THREADS')


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def native_state():
    from threadpoolctl import threadpool_info
    return dict(environment={key:os.environ.get(key) for key in NATIVE_KEYS},
                loaded_pools=threadpool_info(),pid=os.getpid())


def check_native(state):
    require(state['environment']['OPENBLAS_NUM_THREADS']=='1', 'OPENBLAS environment exactly one after full imports')
    require(state['environment']['OMP_NUM_THREADS']=='1', 'OMP environment exactly one after full imports')
    require(all(value in (None,'1') for value in state['environment'].values()), 'optional native environments unset or one')
    pools=[p for p in state['loaded_pools'] if p.get('user_api') in ('blas','openmp')]
    require(any(p.get('user_api')=='blas' for p in pools), 'actual BLAS libraries loaded for regression')
    require(all(p['num_threads']==1 for p in pools), 'every loaded BLAS/OpenMP native pool actually one')


def tiny_program():
    return dict(schema='coupled-divisor-completion-v1',
                kernel=[dict(divisor=d,weight=w) for d,w in [(4,'-1'),(5,'1'),(8,'1'),(10,'-1')]],
                memory=2,rays=[dict(a=['1','1'],weight='1/4')],drift_multiplier='3/2',
                coupled_terms=[dict(cut=dict(scale='1',n_exponent='1',u_exponent='0',complement=c,unit_balance=True),
                                    weight=dict(kind='product',i=0,j=0,arithmetic='all'),theta='5/2') for c in (False,True)],
                gram_weights=['0','0','0'],prime_anchor=True)


def tiny_worker(task):
    started=time.monotonic()
    wrapper=importlib.import_module(task['wrapper_module'])
    # The corrected pool's actual initializer must have run before this worker.
    before=native_state();check_native(before)
    ready=Path(task['barrier_directory']);(ready/str(os.getpid())).write_text('ready\n')
    while len(list(ready.iterdir()))<3:
        require(time.monotonic()-started<30, 'all three distinct spawned workers reach barrier')
        time.sleep(.02)
    import mobius_bank_witness_086 as lower
    import check_mobius_arithmetic_bank_086 as checker
    p=tiny_program();outer=lower.MIXED.SQUARE.O.synthesize(p)['certificate']
    model=lower.MIXED.build_model(p,59)
    bank=[dict(kind='prime_pair',cut_on='prime',cut=dict(scale='1',u_exponent='1',complement=False),weight=dict(kind='one'))]
    report=lower.solve_model(model,bank,time_limit=1,attempts=4,seed=17+task['index'],local_steps=1)
    require(report['status']=='EXACT_COMPATIBLE_BANK_WITNESS_PROPOSAL', 'real tiny witness produced')
    proposals=[a for a in report['attempts'] if 'milp_attempt' in a]
    require(len(proposals)==4 and sorted(a['milp_attempt'] for a in proposals)==[0,1,2,3], 'all four real tiny MILP proposals executed')
    admissions=[]
    for attempt in proposals:
        require(attempt['status']=='EXACT_COMPATIBLE_CERTIFICATE', 'real tiny MILP returned an exactly compatible proposal')
        require(attempt['solver_status']==0, 'real tiny MILP completed successfully')
        require(attempt['highs_threads_requested']==1, 'HiGHS one-thread option retained')
        admitted=checker.verify_lower(p,59,outer,bank,attempt['certificate'])
        require(admitted['status']=='VERIFIED_FINITE_ARITHMETIC_BANK_LOWER_BOUND', 'independent exact tiny lower admission')
        admissions.append(admitted)
    after=native_state();check_native(after)
    return dict(id='tiny_native_'+str(task['index']),status='VERIFIED_TINY_NATIVE_WORKER_LAUNCH',
                pid=os.getpid(),before=before,after=after,tiny_parent=59,
                witness_report=report,independent_admissions=admissions,
                elapsed_seconds=time.monotonic()-started,scientific_geometry_evaluated=False,
                unknown_Mobius_values_used=False,fresh_draw_computed=False)


def append_receipt(result):
    with RECEIPT.open('a') as stream:
        stream.write(json.dumps(result,sort_keys=True)+'\n')


def baseline_process():
    for key in NATIVE_KEYS:
        os.environ[key]='1'
    import run_mobius_arithmetic_bank_086
    state=native_state()
    return dict(stage='full_import_order_failure_reproduction',status='CONFIRMED_IMPORT_ORDER_IMPLEMENTATION_FAILURE',
                native_after_full_frozen_import=state, scientific_geometry_evaluated=False,
                solver_executed=False,unknown_Mobius_values_used=False,fresh_draw_computed=False)


def fresh_process(wrapper_module):
    for key in NATIVE_KEYS:
        os.environ[key]='1'
    wrapper=importlib.import_module(wrapper_module)
    main=native_state();check_native(main)
    with tempfile.TemporaryDirectory(prefix='mobius086native_') as directory:
        tasks=[dict(id='tiny_native_'+str(i),index=i,wrapper_module=wrapper_module,barrier_directory=directory) for i in range(3)]
        # Updated to the wrapper's public launcher once its API is available.
        rows=wrapper.RUN.POOL.pool_tasks(tiny_worker,tasks,time.monotonic(),'independent_tiny_native_launch')
    require(len(rows)==3 and len({r['pid'] for r in rows})==3, 'three distinct actual spawned workers')
    require(all(r['status']=='VERIFIED_TINY_NATIVE_WORKER_LAUNCH' for r in rows), 'every worker admitted')
    return dict(stage='fresh_full_import_and_three_spawned_workers',status='PASS',wrapper_module=wrapper_module,
                main_native_state=main,workers=rows,worker_count=3,real_MILP_proposals=12,
                independent_tiny_lower_admissions=12,scientific_geometry_evaluated=False,
                unknown_Mobius_values_used=False,fresh_draw_computed=False)


def native_guard_fault_process(wrapper_module):
    wrapper=importlib.import_module(wrapper_module)
    before=native_state();check_native(before)
    os.environ['OMP_NUM_THREADS']='2'
    environment_rejected=False
    try:
        wrapper.native_snapshot()
    except RuntimeError:
        environment_rejected=True
    finally:
        os.environ['OMP_NUM_THREADS']='1'
    import threadpoolctl
    native_rejected=False
    try:
        threadpoolctl.threadpool_limits(limits=2)
        drift=native_state()
        require(any(p['num_threads']==2 for p in drift['loaded_pools']), 'actual loaded pool fault injected')
        try:
            wrapper.native_snapshot()
        except RuntimeError:
            native_rejected=True
    finally:
        threadpoolctl.threadpool_limits(limits=1)
    require(environment_rejected and native_rejected, 'wrapper independently rejects environment and actual pool faults')
    after=native_state();check_native(after)
    counts=wrapper.validate_all()
    require(sum(counts)==703, 'all686 prior plus17 aborted sources preserved')
    return dict(stage='actual_native_and_environment_fault_guards',status='PASS',wrapper_module=wrapper_module,
                environment_fault_rejected=True,actual_loaded_pool_fault_rejected=True,
                direct_byte_preserved_sources=sum(counts),before=before,after=after,
                scientific_geometry_evaluated=False,solver_executed=False,fresh_draw_computed=False)


if __name__=='__main__':
    if len(sys.argv)>1 and sys.argv[1]=='--child':
        started=time.monotonic()
        try:
            if sys.argv[2]=='baseline':
                result=baseline_process()
            elif sys.argv[2].startswith('guard:'):
                result=native_guard_fault_process(sys.argv[2].split(':',1)[1])
            else:
                result=fresh_process(sys.argv[2])
        except Exception:
            result=dict(status='FAIL',stage='fresh_native_launch_regression',traceback=traceback.format_exc(),
                        scientific_geometry_evaluated=False,fresh_draw_computed=False)
        result['elapsed_seconds']=time.monotonic()-started
        Path(sys.argv[3]).write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
        raise SystemExit(0 if result['status'] in ('PASS','CONFIRMED_IMPORT_ORDER_IMPLEMENTATION_FAILURE') else 1)
    mode=sys.argv[1] if len(sys.argv)>1 else 'baseline'
    with tempfile.TemporaryDirectory(prefix='mobius086native_main_') as directory:
        result_path=Path(directory)/'result.json'
        command=[sys.executable,'-B',str(Path(__file__).resolve()),'--child',mode,str(result_path)]
        launched=subprocess.run(command,cwd=ROOT,capture_output=True,text=True,timeout=120)
        result=json.loads(result_path.read_text()) if result_path.exists() else dict(status='FAIL',reason='fresh child did not retain result')
        result.update(child_exit_code=launched.returncode,stdout=launched.stdout,stderr=launched.stderr)
        append_receipt(result)
        print(json.dumps({k:v for k,v in result.items() if k not in ('workers','main_native_state','native_after_full_frozen_import')},sort_keys=True))
