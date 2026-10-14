"""Numerical traces only. No exact feasibility or infeasibility admission.

Run in an isolated one-thread worker: native log capture redirects process fds.
"""
from fractions import Fraction as F
import contextlib
import ctypes
import sys
import hashlib
import json
import math
import os
import threading
import time
from types import SimpleNamespace
import primitive_state_numerical_proposals as frozen

SCHEMA='primitive-state-solver-trace-v1'

def digest(value):
    return hashlib.sha256(json.dumps(value,sort_keys=True,separators=(',',':'),allow_nan=False).encode()).hexdigest()

def finite(value):
    try:
        x=float(value)
        return x if math.isfinite(x) else None
    except (TypeError,ValueError):return None

def fields(obj):
    out={}
    for key in dir(obj):
        if key.startswith('_'):continue
        try:v=getattr(obj,key)
        except Exception:continue
        if callable(v):continue
        if isinstance(v,(str,bool,int)) or v is None:out[key]=v
        elif isinstance(v,float):out[key]=finite(v)
        elif isinstance(v,(list,tuple)) or hasattr(v,'tolist'):out[key]=[finite(x) for x in v]
        else:out[key]=str(v)
    return out

@contextlib.contextmanager
def native_log(path=None,max_bytes=1048576):
    if type(max_bytes)is not int or max_bytes<1:raise ValueError('positive log byte cap')
    receipt={'bytes_seen':0,'bytes_retained':0,'overflow_bytes':0,'sha256':None,'path':path}
    chunks=[];h=hashlib.sha256();retained_hash=hashlib.sha256();read,write=os.pipe();saved=[os.dup(1),os.dup(2)]
    sink=open(path,'wb') if path else None
    def drain():
        while True:
            chunk=os.read(read,65536)
            if not chunk:break
            h.update(chunk);receipt['bytes_seen']+=len(chunk)
            keep=chunk[:max(0,max_bytes-receipt['bytes_retained'])]
            receipt['bytes_retained']+=len(keep);retained_hash.update(keep)
            if sink:
                try:sink.write(keep);sink.flush()
                except OSError as e:receipt['sink_error']=str(e)
            else:chunks.append(keep)
        os.close(read)
    thread=threading.Thread(target=drain,daemon=True);thread.start()
    try:
        sys.stdout.flush();sys.stderr.flush();ctypes.CDLL(None).fflush(None)
        os.dup2(write,1);os.dup2(write,2);os.close(write)
        yield receipt
    finally:
        sys.stdout.flush();sys.stderr.flush();ctypes.CDLL(None).fflush(None)
        for fd,old in zip((1,2),saved):os.dup2(old,fd);os.close(old)
        thread.join()
        if sink:sink.close()
        receipt['overflow_bytes']=receipt['bytes_seen']-receipt['bytes_retained'];receipt['full_stream_sha256']=h.hexdigest();receipt['sha256']=retained_hash.hexdigest()
        if not path:receipt['text']=b''.join(chunks).decode('utf-8',errors='replace')

def sparse_system(A,b,c):
    A=A.tocsr()
    return {'variables':A.shape[1],'rows':[[[int(j),float(v)] for j,v in zip(A.indices[A.indptr[i]:A.indptr[i+1]],A.data[A.indptr[i]:A.indptr[i+1]])] for i in range(A.shape[0])],'rhs':[float(v) for v in b],'objective':[float(v) for v in c]}

def magnitude(system):
    values=[abs(v) for row in system['rows'] for _,v in row if v]+[abs(v) for v in system['rhs'] if v]+[abs(v) for v in system['objective'] if v]
    return {'nonzero_count':len(values),'min_nonzero':min(values) if values else None,'max_abs':max(values) if values else None,'dynamic_range':finite(max(values)/min(values)) if values else None}

def prepare(rows,rhs,n,c,nonnegative,blocks,deadline,limits):
    import numpy as np
    clean,targets,receipt=frozen.compress_rows(rows,rhs,n,deadline=deadline,**limits)
    A,b=frozen._matrix(clean,targets,n,receipt)
    system={'rows':[[[j,str(q)] for j,q in sorted(row.items())] for row in rows],'rhs':list(map(str,rhs)),'variables':n,'objective':list(map(float,c)),'nonnegative_indices':nonnegative,'psd_blocks':blocks}
    scaled=sparse_system(A,b,c)
    trace={'schema':SCHEMA,'numerical_evidence_only':True,'original_system':system,'original_system_hash':digest(system),'transformation_receipt':receipt,'scaled_original_system':scaled,'scaled_original_system_hash':digest(scaled),'coefficient_metrics':magnitude(scaled),'original_vector':[None]*n,'diagnostics':{},'source_hashes':{}}
    for path in (__file__,frozen.__file__):
        with open(path,'rb') as f:trace['source_hashes'][os.path.basename(path)]=hashlib.sha256(f.read()).hexdigest()
    return A,b,trace

def evaluate(trace):
    import numpy as np
    x=trace['original_vector'];system=trace['original_system'];d=trace['diagnostics']
    d['unknown_coordinates']=[i for i,v in enumerate(x) if v is None]
    residuals=[None if any(x[j] is None for j,_ in row) else finite(sum(float(F(v))*x[j] for j,v in row)-float(F(b))) for row,b in zip(system['rows'],system['rhs'])]
    d['equality_residuals']=residuals;d['equality_max_abs']=max((abs(v) for v in residuals if v is not None),default=None)
    nn=[x[j] for j in system['nonnegative_indices']];d['nonnegative_min']=min(nn) if nn and all(v is not None for v in nn) else None
    d['psd_min_eigenvalues']={}
    for block in system['psd_blocks']:
        vals=[x[j] for j in block['indices']];minimum=None
        if all(v is not None for v in vals):
            matrix=np.zeros((block['size'],block['size']));k=0
            for a in range(block['size']):
                for b in range(a,block['size']):matrix[a,b]=matrix[b,a]=vals[k];k+=1
            minimum=finite(np.linalg.eigvalsh(matrix)[0])
        d['psd_min_eigenvalues'][block['name']]=minimum
    d['objective']=finite(sum(c*v for c,v in zip(system['objective'],x))) if all(v is not None for v in x) else None
    return trace

def trace_support(columns,lhs,monomials,nonnegative,relations,*,deadline,max_rows,max_variables,max_work,max_cells=4000000,max_coefficient_bits=4096,log_path=None,max_log_bytes=1048576,include_systems=False,checkpoint_path=None):
    import numpy as np
    import scipy
    from scipy.optimize import linprog,OptimizeWarning
    import warnings
    start=time.monotonic();frozen._domain(columns,lhs,monomials)
    ids=nonnegative+relations
    if len(set(ids))!=len(ids) or set(ids)!=set(range(len(columns))):raise ValueError('complete classifications')
    M=len(monomials);n=2*M+len(nonnegative);selected=relations+nonnegative
    if len(selected)+1>max_rows or n>max_variables or (len(selected)+1)*n>max_work:raise OverflowError('dual dimensions/work')
    if 2*sum(len(columns[i]) for i in selected)+len(nonnegative)+2*len(lhs)+len(selected)+1>max_cells:raise OverflowError('dual assembly cell cap')
    lookup={m:j for j,m in enumerate(monomials)};rows=[]
    for i in selected:rows.append({j:q for m,v in columns[i].items() for j,q in ((lookup[m],v),(M+lookup[m],-v))})
    for j in range(len(nonnegative)):rows[len(relations)+j][2*M+j]=F(-1)
    rows.append({j:q for m,v in lhs.items() for j,q in ((lookup[m],v),(M+lookup[m],-v))})
    A,b,t=prepare(rows,[F(0)]*len(selected)+[F(-1)],n,np.ones(n),list(range(n)),[],deadline,dict(max_operations=max_work,max_cells=max_cells,max_coefficient_bits=max_coefficient_bits));t['kind']='support';t['include_systems']=include_systems
    t['original_coordinate_map']={'moment_monomials':[repr(m) for m in monomials],'positive_moment_offset':0,'negative_moment_offset':M,'slack_offset':2*M,'slack_source_column_indices':nonnegative,'relation_source_column_indices':relations};t['solver_system']=t['scaled_original_system'];t['solver_system_hash']=digest(t['solver_system'])
    options={'time_limit':max(0.,deadline-time.monotonic()),'threads':1,'parallel':False,'disp':True};t['solver']={'name':'scipy-highs','versions':{'scipy':scipy.__version__},'options':options,'options_hash':digest(options)}
    t['solver']['versions_hash']=digest(t['solver']['versions'])
    try:
        if options['time_limit']<=0:raise TimeoutError('LP preparation deadline')
        if checkpoint_path:write_checkpoint(checkpoint_path,progress_checkpoint(t))
        with native_log(log_path,max_log_bytes) as log,warnings.catch_warnings():
            warnings.simplefilter('ignore',OptimizeWarning)
            result=linprog(np.ones(n),A_eq=A,b_eq=b,bounds=(0,None),method='highs',options=options)
        t['native_log']=log;t['raw_result']={k:fields(v) if hasattr(v,'keys') else ([finite(x) for x in v] if isinstance(v,np.ndarray) else v) for k,v in result.items()}
        if result.x is not None and len(result.x)==n:t['original_vector']=[finite(v) for v in result.x]
        t['termination_status']=int(result.status);t['termination_message']=str(result.message)
    except Exception as e:
        t['error']={'type':type(e).__name__,'message':str(e)}
        if 'log' in locals():t['native_log']=log
    t['elapsed_seconds']=time.monotonic()-start;t['deadline_exceeded']=time.monotonic()>deadline
    result=finish(t)
    if checkpoint_path:write_checkpoint(checkpoint_path,result)
    return result

def trace_primal(columns,lhs,monomials,shape,offset,specs,*,deadline,max_operations=200000000,max_cells=4000000,max_coefficient_bits=4096,log_path=None,max_log_bytes=1048576,include_systems=False,checkpoint_path=None):
    import numpy as np
    import scipy.sparse as sp
    import cvxpy as cp
    import clarabel
    from cvxpy.reductions.solvers.conic_solvers.clarabel_conif import dims_to_solver_cones
    start=time.monotonic();frozen._domain(columns,lhs,monomials)
    if type(offset)is not int or not 0<=offset<=len(columns) or len(shape)!=2 or any(type(n)is not int or n<0 for n in shape):raise ValueError('primal layout')
    if any(type(n)is not int or n<1 for n in specs.values()) or offset+sum(n*(n+1)//2 for n in specs.values())!=len(columns) or shape[0]+2*shape[1]>offset:raise ValueError('complete PSD layout')
    if sum(map(len,columns))+len(monomials)>min(max_cells,max_operations):raise OverflowError('SDP assembly cap')
    lookup={m:i for i,m in enumerate(monomials)};rows=[{} for _ in monomials]
    for j,p in enumerate(columns):
        for m,q in p.items():rows[lookup[m]][j]=q
    blocks=[];c=np.zeros(len(columns));c[:shape[0]+2*shape[1]]=1;k=offset
    for name,n in specs.items():
        indices=[]
        for a in range(n):
            for b in range(a,n):indices.append(k);c[k]=int(a==b);k+=1
        blocks.append({'name':str(name),'size':n,'indices':indices})
    A,b,t=prepare(rows,[lhs.get(m,F(0)) for m in monomials],len(columns),c,list(range(offset)),blocks,deadline,dict(max_operations=max_operations,max_cells=max_cells,max_coefficient_bits=max_coefficient_bits));t['kind']='primal';t['include_systems']=include_systems
    scalar=cp.Variable(offset,nonneg=True) if offset else None;matrices={r:cp.Variable((n,n),symmetric=True) for r,n in specs.items()}
    vector=cp.hstack(([scalar] if offset else [])+[matrices[r][a,b] for r,n in specs.items() for a in range(n) for b in range(a,n)])
    problem=cp.Problem(cp.Minimize(c@vector),([A@vector==b] if len(rows) else [])+[v>>0 for v in matrices.values()])
    try:
        data,chain,inverse=problem.get_problem_data(cp.CLARABEL)
        t['solver_system']=sparse_system(data['A'],data['b'],data['c']);t['solver_system']['cones']=str(data['dims']);t['solver_system_hash']=digest(t['solver_system'])
        # Canonical coordinate maps are explicit: one unit basis per original entry.
        param=data['param_prob'];t['canonical_variable_map']={str(key):int(value) for key,value in param.var_id_to_col.items()}
        t['original_coordinate_map']={'scalar_offset':0,'scalar_count':offset,'psd_blocks':blocks,'upper_triangle_order':'row-major-a-then-b-a-through-n-minus-1','source_column_order':'identity'}
        t['original_variable_ids']={'scalar':scalar.id if scalar is not None else None,'matrices':{str(r):v.id for r,v in matrices.items()}}
        settings=clarabel.DefaultSettings();settings.max_threads=1;settings.time_limit=max(0.,deadline-time.monotonic());settings.verbose=True
        options=fields(settings);t['solver']={'name':'clarabel-native','versions':{'clarabel':clarabel.__version__,'cvxpy':cp.__version__},'options':options,'options_hash':digest(options)}
        t['solver']['versions_hash']=digest(t['solver']['versions'])
        if settings.time_limit<=0:raise TimeoutError('SDP preparation deadline')
        solver=clarabel.DefaultSolver(sp.csc_matrix((len(data['c']),len(data['c']))),data['c'],data['A'],data['b'],dims_to_solver_cones(data['dims']),settings)
        startup=progress_checkpoint(t)
        if checkpoint_path:write_checkpoint(str(checkpoint_path)+'.source.json',startup)
        def callback(info):
            if checkpoint_path:write_checkpoint(checkpoint_path,{'schema':SCHEMA,'kind':'primal-progress','numerical_evidence_only':True,'source_checkpoint_hash':digest(startup),'raw_info':fields(info),'original_vector':None,'vector_role':'unavailable'})
            return time.monotonic()>deadline
        solver.set_termination_callback(callback)
        if checkpoint_path:write_checkpoint(checkpoint_path,progress_checkpoint(t))
        with native_log(log_path,max_log_bytes) as log:solver.solve()
        t['native_log']=log;t['raw_info']=fields(solver.get_info());solution=solver.get_solution();t['raw_solution']=fields(solution);t['termination_status']=str(solution.status)
        # Force only the inversion adapter to transport x. This is NOT a status claim.
        if len(solution.x)==len(data['c']) and all(finite(v) is not None for v in solution.x):
            transport=SimpleNamespace(status='Solved',x=solution.x,z=solution.z,obj_val=solution.obj_val,solve_time=solution.solve_time,iterations=solution.iterations)
            problem.unpack(chain.invert(transport,inverse));values=np.asarray(vector.value).reshape(-1)
            if len(values)==len(columns):t['original_vector']=[finite(v) for v in values]
            t['iterate_transport_only']=True
    except Exception as e:
        t['error']={'type':type(e).__name__,'message':str(e)}
        if 'log' in locals():t['native_log']=log
        if 'solver' in locals():
            t['raw_info']=fields(solver.get_info());t['raw_solution']=fields(solver.get_solution())
    t['elapsed_seconds']=time.monotonic()-start;t['deadline_exceeded']=time.monotonic()>deadline
    result=finish(t)
    if checkpoint_path:write_checkpoint(checkpoint_path,result)
    return result


def finish(trace):
    evaluate(trace)
    vector=trace['original_vector']
    complete=all(v is not None for v in vector)
    trace['vector_role']='raw_failed_last_iterate' if complete else 'unavailable'
    if not complete:
        if any(v is not None for v in vector):trace['raw_partial_original_vector']=vector
        trace['original_vector']=None
    if 'solver' in trace:trace['solver']['versions_hash']=digest(trace['solver']['versions'])
    trace.setdefault('termination_status','error:'+trace.get('error',{}).get('type','unavailable'))
    log=trace.get('native_log')
    if log is not None:
        trace['retained_log']={'text':log.get('text'),'path':log.get('path'),'encoding':'utf-8','retained_bytes':log['bytes_retained'],'total_bytes':log['bytes_seen'],'truncated':bool(log['overflow_bytes']),'sha256':log['sha256'],'full_stream_sha256':log['full_stream_sha256']}
    trace.setdefault('retained_log',{'text':'','encoding':'utf-8','retained_bytes':0,'total_bytes':0,'truncated':False,'sha256':hashlib.sha256(b'').hexdigest()})
    if not trace.pop('include_systems',False):
        original=trace.pop('original_system')
        trace['original_system_metadata']={k:v for k,v in original.items() if k not in ('rows','rhs')}
        trace['original_system_metadata']['rows_count']=len(original['rows'])
        for key in ('solver_system','scaled_original_system'):
            if key in trace:
                system=trace.pop(key)
                trace[key+'_metadata']={k:v for k,v in system.items() if k not in ('rows','rhs')}
                trace[key+'_metadata']['rows_count']=len(system['rows'])
                trace[key+'_metadata']['coefficient_metrics']=magnitude(system)
    return trace


def write_checkpoint(path,value):
    payload=json.dumps(value,sort_keys=True,separators=(',',':'),allow_nan=False).encode()
    if len(payload)>8*1024*1024:raise OverflowError('checkpoint byte cap')
    temporary=str(path)+'.tmp'
    with open(temporary,'wb') as f:f.write(payload);f.flush();os.fsync(f.fileno())
    os.replace(temporary,path)


def progress_checkpoint(trace):
    return {'schema':SCHEMA,'kind':trace['kind']+'-progress','numerical_evidence_only':True,'original_vector':None,'vector_role':'unavailable','solver':trace.get('solver'),'source_hashes':trace.get('source_hashes'),'original_system_hash':trace.get('original_system_hash'),'scaled_original_system_hash':trace.get('scaled_original_system_hash'),'solver_system_hash':trace.get('solver_system_hash'),'transformation_receipt':trace.get('transformation_receipt')}
