"""Bounded process parallelism for independent detector jobs.
Small job specifications travel to workers; construction belongs in the worker.
Results keep input order. No failed process execution falls back to serial work.
"""
import os,math,time,pickle,importlib,multiprocessing
from concurrent.futures import ProcessPoolExecutor,wait,FIRST_COMPLETED
THREAD_VARIABLES=('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS','VECLIB_MAXIMUM_THREADS','BLIS_NUM_THREADS')
_THREAD_CONTROLLER=None

def _quota_cpu_count(text):
 fields=text.split()
 if len(fields)!=2:raise ValueError('quota format')
 if fields[0]=='max':return None
 quota,period=map(int,fields)
 if period<=0 or quota<0:raise ValueError('quota domain')
 return max(1,quota//period)

def cpu_budget():
 sources={'os_cpu_count':os.cpu_count()or 1}
 try:sources['affinity']=len(os.sched_getaffinity(0))
 except (AttributeError,OSError):pass
 # Both cgroup layouts are checked; unavailable files do not imply an unlimited CPU grant.
 try:
  with open('/sys/fs/cgroup/cpu.max')as f:q=_quota_cpu_count(f.read())
  if q is not None:sources['cgroup_v2_quota']=q
 except (OSError,ValueError):pass
 try:
  with open('/sys/fs/cgroup/cpu/cpu.cfs_quota_us')as f:q=int(f.read())
  with open('/sys/fs/cgroup/cpu/cpu.cfs_period_us')as f:p=int(f.read())
  if q>=0 and p>0:sources['cgroup_v1_quota']=max(1,q//p)
 except (OSError,ValueError):pass
 return dict(available_cpus=max(1,min(v for v in sources.values()if v>0)),sources=sources,quota_rounding='floor with minimum one')

def available_cpu_count():return cpu_budget()['available_cpus']
def _initialize_worker(memory_bytes):
 global _THREAD_CONTROLLER
 if memory_bytes is not None:
  import resource
  soft,hard=resource.getrlimit(resource.RLIMIT_AS)
  limit=memory_bytes if hard==resource.RLIM_INFINITY else min(memory_bytes,hard)
  resource.setrlimit(resource.RLIMIT_AS,(limit,hard))
 for key in THREAD_VARIABLES:os.environ[key]='1'
 try:
  from threadpoolctl import threadpool_limits
  _THREAD_CONTROLLER=threadpool_limits(limits=1)
 except ImportError:_THREAD_CONTROLLER=None # Spawn inherits thread caps before numeric imports.

def _resolve_worker(name):
 if type(name)is not str or name.count(':')!=1:raise ValueError('worker must be module:function')
 module,attribute=name.split(':')
 if not module or any(not s.isidentifier()for s in module.split('.'))or not attribute.isidentifier():raise ValueError('importable worker name')
 function=getattr(importlib.import_module(module),attribute)
 if not callable(function):raise ValueError('callable worker required')
 return function

def _execute(worker,payload,index,max_result_bytes):
 try:
  value=_resolve_worker(worker)(payload)
  if len(pickle.dumps(value,protocol=5))>max_result_bytes:raise OverflowError('worker result byte cap')
  return dict(index=index,status='available',value=value)
 except (OverflowError,TimeoutError,MemoryError)as e:return dict(index=index,status='missing_resource',reason=(str(e)or type(e).__name__)[:512],exception_type=type(e).__name__[:128])
 except Exception as e:return dict(index=index,status='error',reason=(str(e)or type(e).__name__)[:512],exception_type=type(e).__name__[:128])

def run_jobs(jobs,*,worker,workers=None,max_in_flight=None,start_method='spawn',timeout_seconds=None,max_jobs=10000,max_payload_bytes=65536,max_result_bytes=1048576,max_total_result_bytes=33554432,max_total_payload_bytes=33554432,max_workers=8,worker_memory_bytes=None,memory_budget_bytes=None):
 start=time.monotonic();budget=cpu_budget()
 if type(jobs)is not list:raise ValueError('ordered job list required')
 for v in (max_jobs,max_payload_bytes,max_result_bytes,max_total_result_bytes,max_total_payload_bytes,max_workers):
  if type(v)is not int or v<1:raise ValueError('positive job resource bounds')
 if len(jobs)>max_jobs:raise OverflowError('job count cap')
 # Check names without importing potentially expensive application modules in the parent.
 if type(worker)is not str or worker.count(':')!=1:raise ValueError('worker module:function')
 module,attribute=worker.split(':')
 if not module or any(not s.isidentifier()for s in module.split('.'))or not attribute.isidentifier():raise ValueError('worker name')
 if workers is None:workers=min(4,budget['available_cpus'])
 for limit in (worker_memory_bytes,memory_budget_bytes):
  if limit is not None and (type(limit)is not int or limit<1):raise ValueError('optional positive memory budget')
 if memory_budget_bytes is not None and (worker_memory_bytes is None or memory_budget_bytes<worker_memory_bytes):raise ValueError('memory budget needs a fitting per-worker bound')
 if type(workers)is not int or workers<1:raise ValueError('positive workers')
 requested=workers;workers=min(workers,max_workers,budget['available_cpus'],max(1,len(jobs)))
 if memory_budget_bytes is not None:workers=min(workers,memory_budget_bytes//worker_memory_bytes)
 if max_in_flight is None:max_in_flight=workers
 if type(max_in_flight)is not int or not 1<=max_in_flight<=2*workers:raise ValueError('positive in-flight cap')
 if start_method!='spawn'or start_method not in multiprocessing.get_all_start_methods():raise ValueError('safe available process start method')
 if timeout_seconds is not None and (isinstance(timeout_seconds,bool)or type(timeout_seconds)not in(int,float)or not math.isfinite(timeout_seconds)or timeout_seconds<=0):raise ValueError('positive global deadline')
 payload_bytes=0
 for payload in jobs:
  size=len(pickle.dumps(payload,protocol=5));payload_bytes+=size
  if size>max_payload_bytes or payload_bytes>max_total_payload_bytes:raise OverflowError('job specifications exceed byte cap; construct inside worker')
 results=[None]*len(jobs);metadata=dict(cpu_budget=budget,requested_workers=requested,workers=workers,numerical_threads_per_worker=1,worker_memory_bytes=worker_memory_bytes,memory_budget_bytes=memory_budget_bytes,worker_memory_limit_enforced=worker_memory_bytes is not None,max_total_result_bytes=max_total_result_bytes,max_total_payload_bytes=max_total_payload_bytes,payload_bytes=payload_bytes,bounded_status_overhead_bytes=max_jobs*4096,start_method=start_method,max_in_flight=max_in_flight,serial_fallback=False,numerical_thread_control='spawn-inherited environment; threadpoolctl additionally if installed')
 if not jobs:return dict(results=[],cost=dict(metadata,elapsed_seconds=time.monotonic()-start))
 # Reserve every receipt's declared maximum in INPUT order before scheduling.
 # This prevents completion timing from selecting who survives aggregate exhaustion.
 if len(jobs)*(max_result_bytes+4096)>max_total_result_bytes:
  return dict(results=[dict(index=i,status='missing_resource',reason='aggregate receipt budget cannot reserve every job maximum')for i in range(len(jobs))],cost=dict(metadata,result_bytes=0,elapsed_seconds=time.monotonic()-start,available=0,missing=len(jobs),errors=0))
 executor=None;pending={};next_index=0;failure=None;result_bytes=0;old_environment={key:os.environ.get(key)for key in THREAD_VARIABLES}
 try:
  # Spawn imports may load numerical libraries before initializer; inherited env already limits them.
  for key in THREAD_VARIABLES:os.environ[key]='1'
  executor=ProcessPoolExecutor(max_workers=workers,mp_context=multiprocessing.get_context(start_method),initializer=_initialize_worker,initargs=(worker_memory_bytes,))
  while next_index<len(jobs)or pending:
   while next_index<len(jobs)and len(pending)<max_in_flight:
    future=executor.submit(_execute,worker,jobs[next_index],next_index,max_result_bytes);pending[future]=next_index;next_index+=1
   remaining=None if timeout_seconds is None else timeout_seconds-(time.monotonic()-start)
   if remaining is not None and remaining<=0:raise TimeoutError('parallel global deadline')
   done,_=wait(pending,timeout=remaining,return_when=FIRST_COMPLETED)
   if not done:raise TimeoutError('parallel global deadline')
   for future in done:
    index=pending.pop(future)
    try:
     result=future.result();size=len(pickle.dumps(result,protocol=5))
     if result_bytes+size>max_total_result_bytes:raise OverflowError('aggregate receipt byte cap')
     result_bytes+=size;results[index]=result
    except Exception as e:results[index]=dict(index=index,status='missing_resource',reason=('worker process unavailable: '+str(e))[:512],exception_type=type(e).__name__[:128])
 except Exception as e:
  failure=dict(reason=(str(e)or type(e).__name__)[:512],exception_type=type(e).__name__[:128])
 finally:
  if executor is not None:
   if failure:
    for future in pending:future.cancel()
    # Python versions before terminate_workers require explicit process termination.
    processes=list((getattr(executor,'_processes',None)or {}).values())
    for process in processes:
     if process.is_alive():process.terminate()
    for process in processes:process.join(timeout=1)
    for process in processes:
     if process.is_alive():process.kill();process.join(timeout=1)
    executor.shutdown(wait=True,cancel_futures=True)
   else:executor.shutdown(wait=True)
  for key,value in old_environment.items():
   if value is None:os.environ.pop(key,None)
   else:os.environ[key]=value
 if failure:
  for i,result in enumerate(results):
   if result is None:results[i]=dict(index=i,status='missing_resource',**failure)
 metadata.update(result_bytes=result_bytes,elapsed_seconds=time.monotonic()-start,available=sum(r['status']=='available'for r in results),missing=sum(r['status']=='missing_resource'for r in results),errors=sum(r['status']=='error'for r in results))
 return dict(results=results,cost=metadata)
