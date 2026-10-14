"""Corrected086 launch: enforce native limits after all historical imports.

The first attempt and its seventeen scientific sources remain frozen. Only
process launch/thread enforcement changes; arithmetic, seeds and budgets do
not change. No new validation parent had been drawn in the stopped attempt.
"""
import os
for key in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS','VECLIB_MAXIMUM_THREADS'):os.environ[key]='1'
import json
import threadpoolctl
import run_mobius_arithmetic_bank_086 as RUN

ABORTED_OUT=RUN.PRIOR.OUT/'arithmetic_bank_followup_001'
ABORTED_SOURCES=tuple(RUN.read(ABORTED_OUT/'protocol.json')['source_files'])
THREAD_KEYS=('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS','VECLIB_MAXIMUM_THREADS')
for key in THREAD_KEYS:os.environ[key]='1'
_NATIVE_LIMITER=threadpoolctl.threadpool_limits(limits=1)


def native_snapshot():
    environment={key:os.environ.get(key)for key in THREAD_KEYS}
    pools=threadpoolctl.threadpool_info()
    if any(v!='1'for v in environment.values())or any(p['num_threads']!=1 for p in pools):
        raise RuntimeError('086 native thread limit drift after inherited imports')
    if not pools:raise RuntimeError('086 expected loaded numerical native libraries')
    return dict(pid=os.getpid(),environment=environment,pools=pools,threadpoolctl_version=threadpoolctl.__version__)


def validate_all():
    prior=RUN.PRIOR;counts=prior.validate_parent()
    for name in prior.FILES:
        if (RUN.ROOT/name).read_bytes()!=(prior.OUT/'source_snapshot'/name).read_bytes():raise ValueError('preserve085 '+name)
    publication=RUN.read(prior.OUT/'publication_integrity.json')
    for name in publication['postrun_files']:
        if (RUN.ROOT/name).read_bytes()!=(prior.OUT/'postrun_snapshot'/name).read_bytes():raise ValueError('preserve085 postrun '+name)
    counts += [len(prior.FILES),len(publication['postrun_files'])]
    for name in ABORTED_SOURCES:
        if (RUN.ROOT/name).read_bytes()!=(ABORTED_OUT/'source_snapshot'/name).read_bytes():raise ValueError('preserve086 aborted source '+name)
    manifest=RUN.read(ABORTED_OUT/'abort_manifest.json')
    if manifest['status']!='ABORTED_CONFIRMED_IMPORT_ORDER_THREAD_GUARD_FAILURE'or manifest['fresh_draw_reached']:raise ValueError('confirmed launch correction scope')
    for name in manifest['preserved_artifact_files']:
        if (ABORTED_OUT/name).read_bytes()!=(ABORTED_OUT/'aborted_launch_snapshot'/name).read_bytes():raise ValueError('preserve086 aborted artifact '+name)
    native_snapshot()
    return counts+[len(ABORTED_SOURCES)]


if not hasattr(RUN,'_original086_learn_task'):RUN._original086_learn_task=RUN.learn_task
if not hasattr(RUN,'_original086_upper_task'):RUN._original086_upper_task=RUN.upper_task


def learn_task(task):
    before=native_snapshot();result=RUN._original086_learn_task(task);after=native_snapshot()
    RUN.write(RUN.OUT/('native_learn_'+task['id']+'.json'),dict(before=before,after=after))
    return result


def upper_task(task):
    before=native_snapshot();result=RUN._original086_upper_task(task);after=native_snapshot()
    RUN.write(RUN.OUT/('native_upper_'+task['id']+'.json'),dict(before=before,after=after))
    return result


RUN.OUT=ABORTED_OUT/'corrected_launch_001'
RUN.FILES=['run_mobius_arithmetic_bank_retry_086.py','test_mobius_arithmetic_launch_086.py',
           'mobius_arithmetic_launch_086_development.json','mobius_arithmetic_launch_correction_086.txt',
           'audit_mobius_arithmetic_native_launch_086.py']
RUN.SPEC=dict(RUN.SPEC,launch_correction='enforce environment and actual BLAS/OpenMP pools after all inherited imports in parent and spawned workers',
              aborted_attempt_preserved=str(ABORTED_OUT),aborted_attempt_new_validation_draw=False,
              arithmetic_and_search_policy_unchanged=True,threadpoolctl_version=threadpoolctl.__version__)
RUN.validate_parent=validate_all;RUN.learn_task=learn_task;RUN.upper_task=upper_task
native_snapshot()


if __name__=='__main__':RUN.main()
