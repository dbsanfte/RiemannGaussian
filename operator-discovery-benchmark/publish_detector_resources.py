"""Publish independently checked resource work without changing research evidence."""
import hashlib
import json
from pathlib import Path
import check_detector_execution as CHECK
BASE=Path(__file__).resolve().parent
ROOT=BASE/'detector-performance-results'

def read(p):return json.loads(Path(p).read_text())
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(p,v):
    with Path(p).open('x')as f:json.dump(v,f,sort_keys=True,indent=2);f.write('\n')

def publish():
    run=ROOT/'integrated-search-002'; audit_path=ROOT/'integrated-search-math-audit-002.json'
    audit=read(audit_path)
    if not (audit['all_passed'] and audit['math_rechecked'] and len(audit['math_checks'])==3 and all(audit['live_source_matches'].values())):
        raise ValueError('complete independently replayed current search required')
    for name,value in audit['input_sha256'].items():
        if sha(run/name)!=value:raise ValueError('audited input changed: '+name)
    integrity=CHECK.audit(run,require_live_sources=True)
    previous=read(BASE/'cancellation-arithmetic-results/publication-003/manifest.json')
    if any(sha(BASE/name)!=value for name,value in previous['files'].items()):
        raise ValueError('historical research publication changed')
    training=read(run/'training_receipts.json'); final=read(run/'final_receipts.json')
    jobs=[read(run/r['value']['file']) for phase in (training,final) for r in phase['results'] if r['status']=='available']
    if any(j['cost']['observed_threads_at_completion']!=1 for j in jobs):raise ValueError('unexpected observed worker threads')
    calibration=next(j for j in jobs if j['phase']=='train' and j['status']=='finite_certificate')
    matrix=calibration['synthesis']['diagnostics']; probes=read(ROOT/'findings-001.json')
    report=dict(schema=1,entrypoint='run_detector.py',example_config='detector_resource_search.json',
        tested_scope='fixed factor scalar cone; Grams zero; historical full-Gram route preserved',
        tests=dict(distinct_cases=31,all_passed=True,scope='combined initial suites and affected-module reruns; thread fix and new independent audit covered'),
        primary_run=str(run.relative_to(BASE)),independent_audit=str(audit_path.relative_to(BASE)),
        training_seconds=training['cost']['elapsed_seconds'],final_seconds=final['cost']['elapsed_seconds'],
        training_statuses=[j['status']for j in jobs if j['phase']=='train'],
        final_statuses=[j['status']for j in jobs if j['phase']=='final'],
        observed_completion_threads=[j['cost']['observed_threads_at_completion']for j in jobs],
        workers=training['cost']['workers'],worker_memory_bytes=training['cost']['worker_memory_bytes'],
        pool_memory_budget_bytes=training['cost']['memory_budget_bytes'],
        peak_worker_rss_kib=max(j['cost']['peak_rss_kib']for j in jobs),
        matrix=dict(csc_bytes=matrix['proposal_matrix_bytes'],dense_float64_equivalent_bytes=matrix['dense_float64_equivalent_bytes'],scope='matrix arrays only, not total process or solver memory'),
        matched_output_benchmarks=probes['measurements'],
        thread_correction='HiGHS native threads=1/parallel=False required; older metadata measured configured environment rather than native thread count',
        previous_publication_files_verified_unchanged=len(previous['files']),
        calibration_only=True,global_bound_proved=False,RH_proved=False)
    dest=ROOT/'publication-001';dest.mkdir(exist_ok=False)
    write(dest/'report.json',report);write(dest/'integrity_verification.json',integrity)
    names=set(read(run/'source_seal.json'))
    names.update(['DETECTOR_RESOURCE_HANDOFF.txt','detector_resource_search.json','check_detector_execution.py',
        'test_check_detector_execution.py','test_run_detector.py','test_cancellation_sparse_synthesis.py',
        'test_grouped_arithmetic_sparse.py','test_check_grouped_arithmetic_sparse.py','test_detector_parallel.py',
        'test_exact_polynomial_column_cache.py','test_native_exact_support.py',
        'optimized_detector_independent_review.txt','optimized_detector_highs_thread_supplemental_review.txt',
        'grouped_sparse_producer_review.txt','grouped_sparse_producer_benchmark.json',
        'grouped_sparse_verification_benchmark.json','grouped_sparse_verification_scope.txt',
        'detector_performance_probe.py','detector_scale_performance_probe.py','publish_detector_resources.py'])
    # Include all development snapshots and final audited data, not just successes.
    names.update(str(p.relative_to(BASE))for p in ROOT.rglob('*')if p.is_file() and '__pycache__'not in p.parts and p.name!='latest.json')
    write(dest/'manifest.json',dict(files={n:sha(BASE/n)for n in sorted(names)},global_bound_proved=False,RH_proved=False))
    pointer=dict(publication='publication-001',manifest_sha256=sha(dest/'manifest.json'),report_sha256=sha(dest/'report.json'),global_bound_proved=False,RH_proved=False)
    write(ROOT/'latest.json',pointer)
    print(json.dumps(report,indent=2))

if __name__=='__main__':publish()
