"""Distinct-scale exact-construction resource benchmark; no bound evaluations."""
import pathlib,json,time,hashlib,resource,os
import cancellation_factor_search_language as F
import detector_parallel as P

def construction_job(job):
 start=time.monotonic();before=resource.getrusage(resource.RUSAGE_SELF);p=job['program'];b=F.build_instance(**p,X=job['X']);data=json.dumps(b['instance'],sort_keys=True,separators=(',',':')).encode();after=resource.getrusage(resource.RUSAGE_SELF)
 return dict(X=job['X'],instance_sha256=hashlib.sha256(data).hexdigest(),elapsed_seconds=time.monotonic()-start,cpu_seconds=after.ru_utime+after.ru_stime-before.ru_utime-before.ru_stime,peak_RSS_KiB=after.ru_maxrss,thread_environment={key:os.environ.get(key)for key in P.THREAD_VARIABLES},pid=os.getpid(),construction_cost=b['construction_cost'])
def run(directory):
 d=pathlib.Path(directory);d.mkdir(exist_ok=False,parents=True);(d/'source_snapshot').mkdir()
 names=['detector_scale_performance_probe.py','detector_parallel.py','cancellation_factor_search_language.py','cancellation_factor_blocks.py','cancellation_arithmetic_templates.py','cancellation_arithmetic_language.py','grouped_arithmetic_templates.py','grouped_arithmetic_language.py','arithmetic_cycle_language.py','cancellation_gram_language.py'];sources={n:hashlib.sha256(pathlib.Path(n).read_bytes()).hexdigest()for n in names}
 for n in names:(d/'source_snapshot'/n).write_bytes(pathlib.Path(n).read_bytes())
 jobs=[dict(program=dict(target='mu',q=6,C=32,claim='critical'),X=X)for X in [1,2,3,5]]
 spec=dict(kind='development resource benchmark; no arithmetic coefficient responses or bound scores',jobs=jobs,workers=[1,2],source_sha256=sources,worker_memory_bytes=512*1024**2,pool_memory_bytes=1024**3,cpu_budget=P.cpu_budget())
 with (d/'spec.json').open('x')as f:json.dump(spec,f,sort_keys=True,indent=2)
 results=[P.run_jobs(jobs,worker='detector_scale_performance_probe:construction_job',workers=w,max_in_flight=w,timeout_seconds=90,worker_memory_bytes=spec['worker_memory_bytes'],memory_budget_bytes=spec['pool_memory_bytes'])for w in spec['workers']]
 digests=[[r['value']['instance_sha256']for r in run['results']if r['status']=='available']for run in results]
 if len(digests[0])!=4 or digests[0]!=digests[1]:raise ValueError('complete serial/parallel exactoutput mismatch')
 if any(hashlib.sha256(pathlib.Path(n).read_bytes()).hexdigest()!=h for n,h in sources.items()):raise ValueError('benchmark source changed')
 report=dict(spec=spec,runs=results,exact_digest_equality=True,no_detector_scores=True,speedup=results[0]['cost']['elapsed_seconds']/results[1]['cost']['elapsed_seconds'])
 with (d/'report.json').open('x')as f:json.dump(report,f,sort_keys=True,indent=2,allow_nan=False)
 return report
if __name__=='__main__':
 import sys
 r=run(sys.argv[1]);print(json.dumps(dict(seconds=[x['cost']['elapsed_seconds']for x in r['runs']],speedup=r['speedup'],exact_digest_equality=r['exact_digest_equality'])))
