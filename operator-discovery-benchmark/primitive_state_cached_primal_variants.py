"""Bounded shared-source cache and two fixed native numerical variants only."""
from fractions import Fraction as F
import hashlib
import json
import math
import os
import time
import primitive_state_basis_primal as P

SCHEMA='primitive-state-cached-primal-v1'
VARIANTS=[dict(id='qdldl_default',options=dict(direct_solve_method='qdldl')),
    dict(id='faer_static_1e-6',options=dict(direct_solve_method='faer',static_regularization_constant=1e-6))]
FLAGS=dict(P.FLAGS)


def variant_spec(variant):
    for value in VARIANTS:
        if variant==value['id']:return dict(id=value['id'],options=dict(value['options']))
    raise ValueError('exact preregistered native variant')


def settings(variant,seconds,verbose=True):
    import clarabel
    if type(seconds)not in (int,float) or not math.isfinite(seconds) or not 0<=seconds<=900:raise ValueError('bounded native time allowance')
    value=clarabel.DefaultSettings();value.max_threads=1;value.time_limit=seconds;value.verbose=verbose
    for key,q in variant_spec(variant)['options'].items():setattr(value,key,q)
    return value


def source_hashes():
    result={}
    for path in (__file__,P.__file__,P.LOG.__file__):
        with open(path,'rb') as f:result[os.path.basename(path)]=hashlib.sha256(f.read()).hexdigest()
    return result


def encode_cache(data,assembly,columns,lhs,monomials,shape,offset,specs,selected_indices,parent_bindings,*,deadline,max_operations=50000000,max_cells=4000000,max_coefficient_bits=4096,max_cache_bytes=134217728):
    """Cache exact original columns and actual native CSC; no executable formats."""
    if type(max_cache_bytes)is not int or max_cache_bytes<1:raise ValueError('strict cache byte cap')
    budget=P.Budget(deadline,max_operations,max_cells,max_coefficient_bits);budget.charge()
    if any(type(m)is not tuple or len(m)>64 or any(type(i)is not int or i<0 or i.bit_length()>63 for i in m) for m in monomials):raise ValueError('bounded integer-tuple monomial labels')
    lookup={m:i for i,m in enumerate(monomials)};original_columns=[]
    for column in columns:
        encoded=[];budget.charge(len(column)*max(1,len(column).bit_length()),cells=len(column))
        for m in sorted(column,key=lookup.get):encoded.append([lookup[m],str(budget.rational(column[m]))])
        original_columns.append(encoded)
    original=dict(columns=original_columns,rhs=[str(budget.rational(lhs.get(m,F(0)))) for m in monomials],monomials=[list(m) for m in monomials],
        shape=list(shape),offset=offset,specs=[[name,n] for name,n in sorted(specs.items())],selected_original_indices=list(selected_indices))
    A=data['A'];canonical=dict(format='csc-floathex-v1',shape=list(A.shape),indptr=list(map(int,A.indptr)),indices=list(map(int,A.indices)),
        values=[float(v).hex() for v in A.data],rhs=[float(v).hex() for v in data['b']],objective=[float(v).hex() for v in data['c']],P='zero',cones=data['cones'])
    budget.charge(len(A.data)+len(A.indptr)+len(data['b'])+len(data['c']),cells=len(A.data)+len(A.indptr))
    cache=dict(schema=SCHEMA,original=original,canonical=canonical,assembly=assembly,parent_bindings=parent_bindings,
        original_source_hash=P.digest(original),canonical_cache_hash=P.digest(canonical),assembly_hash=P.digest(assembly),source_hashes=source_hashes(),**FLAGS)
    payload=P.encoded(cache)
    if len(payload)>max_cache_bytes:raise OverflowError('shared cache byte cap')
    budget.charge(len(payload)//64+1)
    return cache,dict(operations=budget.operations,cells=budget.cells,cache_bytes=len(payload),encode_work_reserve=budget.operations+len(payload)+1)


def read_cache(path,*,max_cache_bytes=134217728,expected_sha256=None):
    if type(max_cache_bytes)is not int or max_cache_bytes<1:raise ValueError('strict cache byte cap')
    if os.stat(path).st_size>max_cache_bytes:raise OverflowError('shared cache byte cap before allocation')
    with open(path,'rb') as f:payload=f.read(max_cache_bytes+1)
    if len(payload)>max_cache_bytes:raise OverflowError('shared cache byte cap')
    if expected_sha256 is not None and hashlib.sha256(payload).hexdigest()!=expected_sha256:raise ValueError('immutable actual shared cache bytes')
    return json.loads(payload),dict(cache_bytes=len(payload),cache_file_hash=hashlib.sha256(payload).hexdigest())


def decode_cache(cache,*,deadline,max_operations=50000000,max_cells=4000000,max_coefficient_bits=4096):
    """Bounded exact/CSC decoding. Independent checker licenses actual mappings."""
    import numpy as np
    from scipy.sparse import csc_matrix
    budget=P.Budget(deadline,max_operations,max_cells,max_coefficient_bits);budget.charge()
    if type(cache)is not dict or cache.get('schema')!=SCHEMA:raise ValueError('known shared cache schema')
    for flag in FLAGS:
        if cache.get(flag)is not False:raise ValueError('cache is diagnostic source evidence only')
    original=cache.get('original');canonical=cache.get('canonical')
    if type(original)is not dict or type(canonical)is not dict or cache.get('original_source_hash')!=P.digest(original) or cache.get('canonical_cache_hash')!=P.digest(canonical) or cache.get('assembly_hash')!=P.digest(cache.get('assembly')):raise ValueError('complete shared cache content hashes')
    labels=original['monomials']
    if type(labels)is not list or any(type(m)is not list or len(m)>64 or any(type(i)is not int or i<0 or i.bit_length()>63 for i in m) for m in labels):raise ValueError('bounded integer-tuple monomial domain')
    monomials=[tuple(m) for m in labels]
    if len(set(monomials))!=len(monomials):raise ValueError('unique cache monomial domain')
    rows_count=len(monomials);columns=[];exact_rows=[{} for _ in monomials]
    def rational_text(text):
        if type(text)is not str or len(text)>4*max_coefficient_bits+4 or any(c not in '0123456789+-/' for c in text):raise ValueError('bounded exact coefficient text')
        q=budget.rational(F(text))
        if str(q)!=text:raise ValueError('canonical exact coefficient text')
        return q
    for j,column in enumerate(original['columns']):
        if type(column)is not list:raise ValueError('complete sparse cache column')
        previous=-1;value={}
        for term in column:
            budget.charge(cells=1)
            if type(term)is not list or len(term)!=2 or type(term[0])is not int or not previous<term[0]<rows_count:raise ValueError('sorted unique original column row coordinates')
            row,text=term;previous=row;q=rational_text(text);value[monomials[row]]=q
            if q:exact_rows[row][j]=q
        columns.append(value)
    if len(original['rhs'])!=rows_count:raise ValueError('complete original RHS')
    rhs=[rational_text(text) for text in original['rhs']];lhs={m:q for m,q in zip(monomials,rhs) if q}
    shape=canonical['shape'];n=len(columns)
    if type(shape)is not list or len(shape)!=2 or any(type(i)is not int or i<0 for i in shape) or shape[1]!=n:raise ValueError('complete canonical cache dimensions')
    indptr=canonical['indptr'];indices=canonical['indices'];values=canonical['values']
    if canonical.get('format')!='csc-floathex-v1' or canonical.get('P')!='zero' or type(indptr)is not list or len(indptr)!=n+1 or indptr[0]!=0 or any(type(i)is not int or i<0 for i in indptr) or any(a>b for a,b in zip(indptr,indptr[1:])) or indptr[-1]!=len(indices) or len(indices)!=len(values):raise ValueError('complete canonical CSC structure')
    budget.charge(len(indices),cells=len(indices))
    for j in range(n):
        previous=-1
        for i in indices[indptr[j]:indptr[j+1]]:
            if type(i)is not int or not previous<i<shape[0]:raise ValueError('sorted unique native CSC rows')
            previous=i
    def number(text):
        budget.charge()
        if type(text)is not str or len(text)>32:raise ValueError('bounded native float.hex coefficient')
        x=float.fromhex(text)
        if not math.isfinite(x) or x.hex()!=text:raise ValueError('canonical finite native float.hex')
        return x
    vv=[number(text) for text in values];bb=[number(text) for text in canonical['rhs']];cc=[number(text) for text in canonical['objective']]
    if len(bb)!=shape[0] or len(cc)!=n:raise ValueError('complete canonical objective/RHS')
    data=dict(A=csc_matrix((np.asarray(vv),np.asarray(indices),np.asarray(indptr)),shape=tuple(shape)),b=np.asarray(bb),c=np.asarray(cc),cones=canonical['cones'],original_rows=exact_rows,original_rhs=rhs)
    return dict(data=data,columns=columns,lhs=lhs,monomials=monomials,shape=original['shape'],offset=original['offset'],specs=dict(original['specs']),selected_indices=original['selected_original_indices'],assembly=cache['assembly']),dict(operations=budget.operations,cells=budget.cells)


def solve_cached(decoded,cache,cache_binding,variant,*,deadline,max_operations=50000000,max_cells=4000000,max_coefficient_bits=4096,max_trace_bytes=8388608,max_log_bytes=1048576,log_path=None,checkpoint_path=None):
    import clarabel
    import numpy as np
    import scipy
    from scipy.sparse import csc_matrix
    variant_spec(variant);data=decoded['data'];assembly=decoded['assembly'];budget=P.Budget(deadline,max_operations,max_cells,max_coefficient_bits);start=time.monotonic()
    trace=dict(schema=P.SCHEMA,assembly=assembly,numerical_evidence_only=True,original_vector=None,vector_role='unavailable',raw_solution=None,raw_info=None,
        termination_status='unavailable',source_hashes=source_hashes(),cache_binding=cache_binding,variant=variant,**FLAGS)
    option=settings(variant,max(0.,deadline-time.monotonic()));opts=P.LOG.fields(option);versions=dict(clarabel=clarabel.__version__,scipy=scipy.__version__,numpy=np.__version__)
    trace['solver']=dict(name='clarabel-native',options=opts,versions=versions,options_hash=P.digest(opts),versions_hash=P.digest(versions))
    def checkpoint(value):
        if checkpoint_path:
            payload=P.encoded(value)
            if len(payload)>max_trace_bytes:raise OverflowError('variant checkpoint byte cap')
            P.LOG.write_checkpoint(checkpoint_path,value)
    if checkpoint_path:P.LOG.write_checkpoint(str(checkpoint_path)+'.source.json',dict(trace,phase='cached_assembled'))
    try:
        if option.time_limit<=0:raise TimeoutError('cached native preparation deadline')
        cones=[{'Zero':clarabel.ZeroConeT,'Nonnegative':clarabel.NonnegativeConeT,'PSDTriangle':clarabel.PSDTriangleConeT}[name](n) for name,n in data['cones']]
        solver=clarabel.DefaultSolver(csc_matrix((len(data['c']),len(data['c']))),data['c'],data['A'],data['b'],cones,option)
        startup=dict(schema=P.SCHEMA,phase='native_started',cache_binding=cache_binding,variant=variant,assembly_hash=P.digest(assembly),solver=trace['solver'],original_vector=None,**FLAGS)
        def callback(info):checkpoint(dict(startup,raw_info=P.LOG.fields(info)));return time.monotonic()>deadline
        solver.set_termination_callback(callback);checkpoint(startup)
        with P.LOG.native_log(log_path,max_log_bytes) as log:solver.solve()
        trace['native_log']=log
    except Exception as e:
        trace['error']=dict(type=type(e).__name__,message=str(e));trace['termination_status']='error:'+type(e).__name__
        if 'log' in locals():trace['native_log']=log
    if 'solver' in locals():
        try:
            solution=solver.get_solution();trace.update(raw_solution=P.LOG.fields(solution),raw_info=P.LOG.fields(solver.get_info()),termination_status=str(solution.status))
            if len(solution.x)==assembly['variables'] and all(P.LOG.finite(v)is not None for v in solution.x):
                trace['original_vector']=[float(v) for v in solution.x];trace['vector_role']='raw_native_solution' if str(solution.status) in ('Solved','AlmostSolved') else 'raw_failed_last_iterate'
        except Exception as e:trace['export_error']=dict(type=type(e).__name__,message=str(e))
    log=trace.pop('native_log',None)
    if log and log.get('text')is None:
        with open(log_path,'rb') as f:text=f.read(max_log_bytes+1)
        if len(text)>max_log_bytes:raise OverflowError('cached native log byte cap')
        log['text']=text.decode('utf-8')
    trace['retained_log']=(dict(text=log.get('text'),path=log.get('path'),encoding='utf-8',retained_bytes=log['bytes_retained'],total_bytes=log['bytes_seen'],truncated=bool(log['overflow_bytes']),sha256=log['sha256'],full_stream_sha256=log['full_stream_sha256']) if log else dict(text='',encoding='utf-8',retained_bytes=0,total_bytes=0,truncated=False,sha256=hashlib.sha256(b'').hexdigest()))
    try:trace['diagnostics']=P.diagnostics(data,assembly,trace['original_vector'],budget)
    except (OverflowError,TimeoutError,MemoryError,ValueError) as e:trace['diagnostic_error']=dict(type=type(e).__name__,message=str(e));trace['diagnostics']=dict(complete=False)
    trace.update(elapsed_seconds=time.monotonic()-start,deadline_exceeded=time.monotonic()>deadline,counts=dict(assembly_operations=0,diagnostic_operations=budget.operations,producer_work_reserve=budget.operations,source_cells=assembly['counts']['source_cells']))
    if len(P.encoded(trace))>max_trace_bytes:raise OverflowError('cached native trace byte cap')
    checkpoint(dict(trace,phase='native_returned'));return trace
