"""Resource-development measurements only; no arithmetic bound responses/scores."""
import pathlib,json,time,hashlib
import cancellation_factor_search_language as F
import detector_parallel as P
from exact_polynomial_column_cache import ColumnCache

def construction_job(job):
 start=time.monotonic();b=F.build_instance('mu',job['scale'],6,32)
 payload=json.dumps(b['instance'],sort_keys=True,separators=(',',':')).encode()
 return dict(instance_sha256=hashlib.sha256(payload).hexdigest(),construction_seconds=time.monotonic()-start,scale=job['scale'],groups=[len(b['instance'][k])for k in ('square_groups','relation_groups')],construction_cost=b['construction_cost'])

def run(directory):
 d=pathlib.Path(directory);d.mkdir(exist_ok=False,parents=True)
 spec=dict(kind='development performance only; no detector score or actual signed responses',jobs=[dict(scale=3)]*4,workers=[1,min(4,P.available_cpu_count())],source_sha256={n:hashlib.sha256(pathlib.Path(n).read_bytes()).hexdigest()for n in ['detector_parallel.py','detector_performance_probe.py','exact_polynomial_column_cache.py']})
 with (d/'spec.json').open('x')as f:json.dump(spec,f,sort_keys=True,indent=2)
 runs=[]
 for workers in spec['workers']:runs.append(P.run_jobs(spec['jobs'],worker='detector_performance_probe:construction_job',workers=workers,max_in_flight=workers,timeout_seconds=90))
 hashes=[[r['value']['instance_sha256']for r in run['results']if r['status']=='available']for run in runs]
 if len(hashes[0])!=4 or hashes[0]!=hashes[1]:raise ValueError('parallel exact construction outputs differ or unavailable')
 build=F.build_instance('mu',3,6,32);cache=ColumnCache(max_entries=2);first=cache.prepare([build['instance']],deadline=time.monotonic()+90);second=cache.prepare([build['instance']],deadline=time.monotonic()+90)
 # Change only the target scalar; structural columns must remain identical.
 modified=dict(build['instance']);modified['lhs']=[dict(t)for t in modified['lhs']]
 for term in modified['lhs']:
  if not term['m']:term['c']=str(int(term['c'])+1)
 changed=cache.prepare([modified],deadline=time.monotonic()+90)
 if first['columns']!=second['columns'] or first['columns']!=changed['columns']:raise ValueError('cached exact columns differ')
 report=dict(spec=spec,parallel=runs,cache=[first['metadata'],second['metadata'],changed['metadata']],cache_exact_equality_verified=True,structural_coefficients=sum(len(c)for c in first['columns']),no_detector_scores=True,global_bound_proved=False)
 if any(hashlib.sha256(pathlib.Path(n).read_bytes()).hexdigest()!=h for n,h in spec['source_sha256'].items()):raise ValueError('probe source changed')
 with (d/'report.json').open('x')as f:json.dump(report,f,sort_keys=True,indent=2)
 return report
if __name__=='__main__':
 import sys
 r=run(sys.argv[1]);print(json.dumps(dict(parallel_seconds=[x['cost']['elapsed_seconds']for x in r['parallel']],cache_seconds=[x['elapsed_seconds']for x in r['cache']])))
