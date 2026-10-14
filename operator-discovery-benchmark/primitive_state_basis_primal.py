"""Direct Clarabel diagnostic on licensed ORIGINAL equation rows.

No variable/cone/objective reduction; raw native x is never projected or clipped.
No numerical status admits a certificate or an infeasibility statement.
"""
from fractions import Fraction as F
import hashlib
import json
import math
import os
import time
import primitive_state_solver_trace as LOG

SCHEMA='primitive-state-basis-primal-v1'
ASSEMBLY_SCHEMA='primitive-state-basis-primal-assembly-v1'
FLAGS=dict(certified=False,exact_admission=False,infeasibility_proved=False,global_bound_proved=False,RH_proved=False)


def encoded(value):return json.dumps(value,sort_keys=True,separators=(',',':'),allow_nan=False).encode()
def digest(value):return hashlib.sha256(encoded(value)).hexdigest()


class Budget:
    def __init__(self,deadline,max_operations,max_cells,bits):
        if type(deadline)not in (int,float) or not math.isfinite(deadline):raise ValueError('finite absolute deadline')
        if any(type(v)is not int or v<1 for v in (max_operations,max_cells,bits)):raise ValueError('positive strict assembly caps')
        self.deadline=deadline;self.max_operations=max_operations;self.max_cells=max_cells;self.bits=bits;self.operations=0;self.cells=0
    def charge(self,n=1,cells=0):
        self.operations+=n;self.cells+=cells
        if self.operations>self.max_operations or self.cells>self.max_cells:raise OverflowError('basis primal operation/cell cap')
        if time.monotonic()>self.deadline:raise TimeoutError('basis primal deadline')
    def rational(self,q):
        self.charge()
        if type(q)not in (int,F):raise ValueError('exact rational source required')
        q=F(q)
        if max(abs(q.numerator).bit_length(),q.denominator.bit_length())>self.bits:raise OverflowError('basis primal coefficient bits')
        return q


def _number(q):
    x=float(q)
    if not math.isfinite(x) or q and x==0:raise OverflowError('numeric coefficient overflow/underflow')
    return x


def row_hash(rows,rhs,n,budget):
    h=hashlib.sha256();h.update(b'{"rhs":[')
    for i,q in enumerate(rhs):
        if i:h.update(b',')
        value=encoded(str(q));h.update(value);budget.charge(len(value)//64+1)
    h.update(b'],"rows":[')
    for i,row in enumerate(rows):
        if i:h.update(b',')
        h.update(b'[');budget.charge(len(row)*max(1,len(row).bit_length()))
        for k,j in enumerate(sorted(row)):
            if k:h.update(b',')
            value=encoded([j,str(row[j])]);h.update(value);budget.charge(len(value)//64+1)
        h.update(b']')
    h.update(b'],"variables":');h.update(str(n).encode());h.update(b'}');return h.hexdigest()


def canonical_hash(rows,rhs,objective,cones,budget):
    # Canonical sorted JSON keys: cones, objective, rhs, rows, variables.
    h=hashlib.sha256();h.update(b'{"cones":');h.update(encoded(cones));h.update(b',"objective":');h.update(encoded([float(v).hex() for v in objective]));h.update(b',"rhs":');h.update(encoded([float(v).hex() for v in rhs]));h.update(b',"rows":[')
    for i,row in enumerate(rows):
        if i:h.update(b',')
        h.update(b'[')
        for k,j in enumerate(sorted(row)):
            if k:h.update(b',')
            value=encoded([j,float(row[j]).hex()]);h.update(value);budget.charge(len(value)//64+1)
        h.update(b']');budget.charge(len(row)*max(1,len(row).bit_length()))
    h.update(b'],"variables":');h.update(str(len(objective)).encode());h.update(b'}');budget.charge(len(rhs)+len(objective)+len(cones));return h.hexdigest()


def assemble(columns,lhs,monomials,shape,offset,specs,selected_indices,*,deadline,
             max_operations=50000000,max_cells=4000000,max_coefficient_bits=4096):
    """Build native A,b,c in original coordinates and an independently replayable receipt."""
    import numpy as np
    from scipy.sparse import csc_matrix
    budget=Budget(deadline,max_operations,max_cells,max_coefficient_bits);budget.charge()
    n=len(columns)
    if type(columns)is not list or not columns or type(lhs)is not dict or type(monomials)is not list or len(set(monomials))!=len(monomials):raise ValueError('complete source domain schema')
    if any(type(p)is not dict for p in columns) or set(monomials)!=set(lhs)|{m for p in columns for m in p}:raise ValueError('complete source/target monomial domain')
    if type(shape)not in (list,tuple) or len(shape)!=2 or any(type(v)is not int or v<0 for v in shape) or type(offset)is not int or not shape[0]+2*shape[1]<=offset<=n:raise ValueError('original scalar layout')
    if type(specs)is not dict or not specs or any(type(k)is not str or type(v)is not int or not 1<=v<=64 for k,v in specs.items()) or offset+sum(v*(v+1)//2 for v in specs.values())!=n:raise ValueError('complete original PSD layout')
    if type(selected_indices)is not list or not selected_indices or any(type(i)is not int or not 0<=i<len(monomials) for i in selected_indices) or len(set(selected_indices))!=len(selected_indices):raise ValueError('unique original equation indices')
    source_cells=sum(map(len,columns))+len(monomials)
    if source_cells>max_cells:raise OverflowError('basis primal source cell cap')
    budget.charge(source_cells,cells=source_cells);lookup={m:i for i,m in enumerate(monomials)};rows=[{} for _ in monomials]
    for j,p in enumerate(columns):
        for m,q in p.items():
            q=budget.rational(q)
            if q:rows[lookup[m]][j]=q
    rhs=[budget.rational(lhs.get(m,F(0))) for m in monomials]
    objective=[0.]*n
    for j in range(shape[0]+2*shape[1]):objective[j]=1.
    blocks=[];pos=offset
    for name,size in sorted(specs.items()):
        entries=[]
        for a in range(size):
            for b in range(a,size):
                entries.append([a,b,pos]);objective[pos]=float(a==b);pos+=1
        blocks.append(dict(name=name,size=size,offset=entries[0][2],indices=entries))
    layout=dict(shape=list(shape),offset=offset,specs=[[k,v] for k,v in sorted(specs.items())],psd_blocks=blocks,
        scalar_nonnegative_indices=list(range(offset)),objective=objective)
    receipt=dict(schema=ASSEMBLY_SCHEMA,variables=n,original_rows=len(rows),selected_original_indices=list(selected_indices),
        selected_row_scales=[],layout=layout,layout_hash=digest(layout),
        original_system_hash=row_hash(rows,rhs,n,budget),monomial_domain_hash=digest(monomials),
        variable_mapping='identity',objective_mapping='identity',cone_mapping='identity',
        storage_definition='R=e_prefix e_prefix^T+K, enforced K PSD',storage_anchor_index=1,
        limits=dict(max_operations=max_operations,max_cells=max_cells,max_coefficient_bits=max_coefficient_bits))
    canonical=[];bb=[]
    for i in selected_indices:
        scale=max([abs(rhs[i])]+[abs(q) for q in rows[i].values()])
        if not scale:raise ValueError('selected zero augmented equation')
        receipt['selected_row_scales'].append(str(scale));budget.charge(len(rows[i])+1)
        canonical.append({j:_number(q/scale) for j,q in rows[i].items()});bb.append(_number(rhs[i]/scale))
    cones=[['Zero',len(selected_indices)],['Nonnegative',offset]]
    if offset:
        for j in range(offset):canonical.append({j:-1.});bb.append(0.)
    for block in blocks:
        mapping={(a,b):j for a,b,j in block['indices']};size=block['size'];cones.append(['PSDTriangle',size])
        for b in range(size):
            for a in range(b+1):canonical.append({mapping[a,b]:-1. if a==b else -math.sqrt(2.)});bb.append(0.)
    canonical_cells=sum(map(len,canonical));budget.charge(canonical_cells+len(bb),cells=canonical_cells+len(bb))
    receipt.update(cones=cones,canonical_rows=len(canonical),canonical_cells=canonical_cells,
        canonical_system_hash=canonical_hash(canonical,bb,objective,cones,budget))
    rr=[];cc=[];vv=[]
    for i,row in enumerate(canonical):
        for j,v in row.items():rr.append(i);cc.append(j);vv.append(v)
    A=csc_matrix((vv,(rr,cc)),shape=(len(canonical),n));b=np.asarray(bb);c=np.asarray(objective)
    budget.charge(canonical_cells+n)
    receipt['counts']=dict(operations=budget.operations,cells=budget.cells,source_cells=source_cells,canonical_cells=canonical_cells)
    return dict(A=A,b=b,c=c,cones=cones,original_rows=rows,original_rhs=rhs),receipt


def diagnostics(data,assembly,values,budget):
    """Finite raw-coordinate residuals and explicit PSD necessary bounds."""
    if values is None:return dict(complete=False,unknown_coordinates=list(range(assembly['variables'])))
    residuals=[]
    for row,target in zip(data['original_rows'],data['original_rhs']):
        budget.charge(2*len(row)+1)
        residuals.append(LOG.finite(math.fsum(_number(q)*values[j] for j,q in row.items())-_number(target)))
    selected=assembly['selected_original_indices'];scales=list(map(F,assembly['selected_row_scales']))
    scaled=[LOG.finite(residuals[i]/_number(scale)) if residuals[i]is not None else None for i,scale in zip(selected,scales)]
    scalar=values[:assembly['layout']['offset']]
    blocks={};eigen={}
    import numpy as np
    for block in assembly['layout']['psd_blocks']:
        size=block['size'];matrix=[[0.]*size for _ in range(size)]
        for a,b,j in block['indices']:matrix[a][b]=matrix[b][a]=values[j]
        lower=min(matrix[a][a]-math.fsum(abs(matrix[a][b]) for b in range(size) if a!=b) for a in range(size));upper=min(matrix[a][a] for a in range(size))
        blocks[block['name']]=dict(matrix=matrix,gershgorin_lower=LOG.finite(lower),min_diagonal=LOG.finite(upper))
        eigen[block['name']]=LOG.finite(np.linalg.eigvalsh(np.asarray(matrix))[0]);budget.charge(size**3)
    return dict(complete=all(v is not None for v in residuals),unknown_coordinates=[],equality_residuals=residuals,
        equality_max_abs=max((abs(v) for v in residuals if v is not None),default=None),selected_scaled_residuals=scaled,
        selected_scaled_max_abs=max((abs(v) for v in scaled if v is not None),default=None),
        nonnegative_min=min(scalar) if scalar else None,negative_scalar_indices=[j for j,v in enumerate(scalar) if v<0],
        objective=LOG.finite(math.fsum(c*x for c,x in zip(assembly['layout']['objective'],values))),
        psd_blocks=blocks,psd_min_eigenvalues=eigen)


def solve_trace(columns,lhs,monomials,shape,offset,specs,selected_indices,*,deadline,
                max_operations=50000000,max_cells=4000000,max_coefficient_bits=4096,
                max_trace_bytes=8388608,max_log_bytes=1048576,log_path=None,checkpoint_path=None):
    import clarabel
    import numpy as np
    from scipy.sparse import csc_matrix
    import scipy
    if any(type(v)is not int or v<1 for v in (max_trace_bytes,max_log_bytes)):raise ValueError('strict positive trace/log caps')
    start=time.monotonic();data,assembly=assemble(columns,lhs,monomials,shape,offset,specs,selected_indices,deadline=deadline,
        max_operations=max_operations,max_cells=max_cells,max_coefficient_bits=max_coefficient_bits)
    remaining=max_operations-assembly['counts']['operations']
    if remaining<1:raise OverflowError('basis primal diagnostic work allowance')
    budget=Budget(deadline,remaining,max_cells,max_coefficient_bits)
    trace=dict(schema=SCHEMA,assembly=assembly,numerical_evidence_only=True,original_vector=None,vector_role='unavailable',raw_solution=None,raw_info=None,
        termination_status='unavailable',source_hashes={},**FLAGS)
    for path in (__file__,LOG.__file__):
        with open(path,'rb') as f:trace['source_hashes'][os.path.basename(path)]=hashlib.sha256(f.read()).hexdigest()
    settings=clarabel.DefaultSettings();settings.max_threads=1;settings.time_limit=max(0.,deadline-time.monotonic());settings.verbose=True
    options=LOG.fields(settings);versions=dict(clarabel=clarabel.__version__,scipy=scipy.__version__,numpy=np.__version__)
    trace['solver']=dict(name='clarabel-native',options=options,versions=versions,options_hash=digest(options),versions_hash=digest(versions))
    def write_progress(value):
        if checkpoint_path:
            payload=encoded(value)
            if len(payload)>max_trace_bytes:raise OverflowError('basis primal checkpoint byte cap')
            LOG.write_checkpoint(checkpoint_path,value)
    startup=dict(schema=SCHEMA,phase='native_started',assembly_hash=digest(assembly),solver=trace['solver'],original_vector=None,**FLAGS)
    if checkpoint_path:LOG.write_checkpoint(str(checkpoint_path)+'.source.json',dict(trace,phase='assembled'))
    try:
        if settings.time_limit<=0:raise TimeoutError('basis primal preparation deadline')
        cones=[]
        for kind,size in data['cones']:
            cones.append({'Zero':clarabel.ZeroConeT,'Nonnegative':clarabel.NonnegativeConeT,'PSDTriangle':clarabel.PSDTriangleConeT}[kind](size))
        solver=clarabel.DefaultSolver(csc_matrix((len(data['c']),len(data['c']))),data['c'],data['A'],data['b'],cones,settings)
        def callback(info):
            write_progress(dict(startup,raw_info=LOG.fields(info)));return time.monotonic()>deadline
        solver.set_termination_callback(callback);write_progress(startup)
        with LOG.native_log(log_path,max_log_bytes) as log:solver.solve()
        trace['native_log']=log
    except Exception as e:
        trace['error']=dict(type=type(e).__name__,message=str(e));trace['termination_status']='error:'+type(e).__name__
        if 'log' in locals():trace['native_log']=log
    if 'solver' in locals():
        try:
            solution=solver.get_solution();trace.update(raw_info=LOG.fields(solver.get_info()),raw_solution=LOG.fields(solution),termination_status=str(solution.status))
            if len(solution.x)==len(columns) and all(LOG.finite(v)is not None for v in solution.x):
                trace['original_vector']=[float(v) for v in solution.x];trace['vector_role']='raw_native_solution' if str(solution.status) in ('Solved','AlmostSolved') else 'raw_failed_last_iterate'
        except Exception as e:trace['export_error']=dict(type=type(e).__name__,message=str(e))
    log=trace.pop('native_log',None)
    if log and log.get('text')is None:
        with open(log_path,'rb') as f:retained=f.read(max_log_bytes+1)
        if len(retained)>max_log_bytes:raise OverflowError('retained native log byte cap')
        log['text']=retained.decode('utf-8')
    trace['retained_log']=(dict(text=log.get('text'),path=log.get('path'),encoding='utf-8',retained_bytes=log['bytes_retained'],total_bytes=log['bytes_seen'],truncated=bool(log['overflow_bytes']),sha256=log['sha256'],full_stream_sha256=log['full_stream_sha256']) if log else dict(text='',encoding='utf-8',retained_bytes=0,total_bytes=0,truncated=False,sha256=hashlib.sha256(b'').hexdigest()))
    try:trace['diagnostics']=diagnostics(data,assembly,trace['original_vector'],budget)
    except (OverflowError,TimeoutError,MemoryError,ValueError) as e:trace['diagnostic_error']=dict(type=type(e).__name__,message=str(e));trace['diagnostics']=dict(complete=False)
    trace.update(elapsed_seconds=time.monotonic()-start,deadline_exceeded=time.monotonic()>deadline,
        counts=dict(assembly_operations=assembly['counts']['operations'],diagnostic_operations=budget.operations,
            producer_work_reserve=assembly['counts']['operations']+budget.operations,source_cells=assembly['counts']['source_cells']))
    if len(encoded(trace))>max_trace_bytes:raise OverflowError('basis primal trace byte cap')
    write_progress(dict(trace,phase='native_returned'));return trace
