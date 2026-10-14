"""Bounded hash-free Farkas proposals on a licensed finite exact chart.

The native LP and endpoint eigensolves propose rational data. Only independent
exact checking of the exported nonnegative cone combination can admit a witness.
"""
from fractions import Fraction as F
import math
import time
import primitive_state_feedback_affine as EXACT

encoded=EXACT.encoded
SCHEMA='primitive-state-chart-dual-search-v1'
RAY_SCHEMA='primitive-state-chart-dual-rays-v1'
CERTIFICATE_SCHEMA='primitive-state-chart-dual-certificate-v1'
FLAGS=dict(global_bound_proved=False,RH_proved=False,universal_identity_proved=False,
           candidate_admitted=False,exact_admission=False,infeasibility_proved=False,
           finite_cone_infeasibility_verified=False,numerical_infeasibility_admitted=False,primal_feasibility_proved=False)
LIMITS=dict(assembly_operations=100000000,native_operations=190000000,
            restoration_operations=60000000,max_cells=6000000,max_bits=4096,
            max_temporary_bits=8193,max_support=443,max_simplex_iterations=100,
            max_outcome_bytes=8388608)
RAY_POLICY=dict(integer_rays_per_block=225,eigenvectors_per_block=15,
                eigenvector_denominator_power=20,eigenvector_rounding='nearest-even binary64 component times2^20',
                eigenvector_sign='first nonzero integer component positive',
                eigenvectors_order='ascending eigenvalue; all15 C then all15 H',
                numerical_eigenvectors_certified=False,
                blocks='C and H=P+4C; offdiagonal coefficient2',
                order='scalar ascending; C axes,pairs plus/minus; H axes,pairs plus/minus; eigenC then eigenH')
LP_POLICY=dict(method='highs-ds',presolve=False,cost='positive original L1 divided by common maximum column scale',
               row_scaling='positive max(abs coefficients,abs rhs); zero row uses1',
               column_scaling='reciprocal positive max(abs row-scaled coefficients); zero column uses1',
               support='all strictly positive finite native scaled variables; no threshold',
               restoration='one deterministic sparse exact solve; free support coordinates zero',
               native_success_required=True,max_support=443,max_simplex_iterations=100,
               numerical_coefficients_may_be_dropped_internally=True)

class Budget(EXACT.Budget):
    def __init__(self,deadline,max_operations=100000000,max_cells=6000000,max_bits=4096):
        if type(deadline)not in(int,float)or not math.isfinite(deadline):raise ValueError('finite dual deadline')
        if any(type(v)is not int or v<1 for v in(max_operations,max_cells,max_bits))or max_operations>190000000 or max_cells>6000000 or max_bits>4096:raise ValueError('bounded dual limits')
        self.deadline=deadline;self.max_operations=max_operations;self.max_cells=max_cells;self.max_bits=max_bits
        self.operations=0;self.peak_cells=0;self.maximum_bits=0;self.resident_cells=0


def decode_chart(chart,budget):
    if chart.get('schema')!='primitive-state-augmented-cone-chart-v1'or chart.get('complete')is not True or chart.get('width')!=1224 or chart.get('original_width')!=1957:raise ValueError('complete licensed augmented chart')
    records=chart['normalized_rows'];pivots=chart['pivot_columns'];free=chart['free_indices']
    if len(records)!=782 or pivots!=sorted(set(pivots))or len(pivots)!=782 or free!=[j for j in range(1224)if j not in pivots]or len(free)!=442 or [r['pivot']for r in records]!=pivots:raise ValueError('complete782/442 partition')
    rows={}
    for record in records:
        p=record['pivot'];row=EXACT.sparse(record['terms'],1224,budget)
        if type(p)is not int or not 0<=p<1224 or row.get(p)!=1 or any(j<p for j in row):raise ValueError('normalized triangular chart row')
        rows[p]=row
    retained,_=EXACT.full15_recipes([366,613],1597,{'full_child':15,'full_parent':15,'storage_K':15},1957)
    if chart.get('retained_indices')!=retained:raise ValueError('complete original-coordinate projection')
    budget.cells(sum(map(len,rows.values()))+len(retained));return rows,free,retained


def reduce_functional(rows,width,functional,budget):
    """Return r,t,lambda with w*x=t+r*x_free on Ax=b; all pivots ascend."""
    if type(width)is not int or not 1<=width<=1224:raise ValueError('bounded functional width')
    work={j:budget.q(q)for j,q in functional.items()if q};t=F(0);multipliers={}
    if any(type(j)is not int or not 0<=j<width for j in work):raise ValueError('functional has no augmented rhs coordinate')
    for p in sorted(rows):
        budget.charge();row=rows[p]
        if row.get(p)!=1 or any(j<p or j>width for j in row):raise ValueError('normalized upper triangular source')
        factor=work.pop(p,F(0))
        if not factor:continue
        multipliers[p]=factor;t=budget.add(t,budget.mul(factor,row.get(width,F(0))))
        for j,q in row.items():
            budget.charge()
            if j in(p,width):continue
            value=budget.add(work.get(j,F(0)),-budget.mul(factor,q))
            if value:work[j]=value
            else:work.pop(j,None)
        budget.cells(len(work)+len(multipliers))
    if set(work)&set(rows):raise ValueError('all pivot coordinates must be eliminated')
    return work,t,multipliers


def geometry(retained):
    position={j:i for i,j in enumerate(retained)}
    if len(position)!=len(retained):raise ValueError('unique retained coordinates')
    return ([position[j]for j in [*range(366),*range(1592,1597)]],
            [position[j]for j in range(1597,1717)],
            [position[j]for j in range(1717,1837)])


def ray_functional(ray,scalar,C,P,budget):
    if ray.get('kind')=='scalar':
        j=ray['coordinate']
        if j not in scalar:raise ValueError('scalar cone generator coordinate')
        return {j:F(1)}
    if ray.get('kind')!='rank_one'or ray.get('block')not in('C','H'):raise ValueError('rank-one cone generator')
    v=[budget.q(q)for q in ray['vector']]
    if len(v)!=15 or not any(v):raise ValueError('nonzero complete15-vector')
    w={};index=0
    for i in range(15):
        for j in range(i,15):
            q=budget.mul(v[i],v[j])
            if i!=j:q=budget.mul(F(2),q)
            if q:
                w[C[index]]=budget.mul(F(4),q)if ray['block']=='H'else q
                if ray['block']=='H':w[P[index]]=q
            index+=1
    return w


def make_rays(retained,endpoint,budget):
    scalar,C,P=geometry(retained);records=[]
    def add(record):record['index']=len(records);records.append(record);budget.charge();budget.cells(16*len(records))
    for j in scalar:add(dict(kind='scalar',coordinate=j))
    for block in('C','H'):
        for i in range(15):
            v=[F(0)]*15;v[i]=F(1);add(dict(kind='rank_one',block=block,vector=list(map(str,v)),origin='axis'))
        for i in range(15):
            for j in range(i+1,15):
                for sign,label in((1,'pair_plus'),(-1,'pair_minus')):
                    v=[F(0)]*15;v[i]=F(1);v[j]=F(sign);add(dict(kind='rank_one',block=block,vector=list(map(str,v)),origin=label))
    if endpoint.get('complete')is not True or len(endpoint.get('final_projected_vector',[]))!=1224:raise ValueError('complete exact028 point for declared eigenvector rays')
    values=[budget.q(q)for q in endpoint['final_projected_vector']]
    import numpy as np
    eigen_diagnostics=[]
    for block in('C','H'):
        matrix=np.zeros((15,15));index=0
        for i in range(15):
            for j in range(i,15):
                q=values[C[index]]if block=='C'else budget.add(values[P[index]],budget.mul(F(4),values[C[index]]))
                value=float(q)
                if not math.isfinite(value)or(q and value==0):raise OverflowError('finite non-underflowing eigenmatrix conversion')
                matrix[i,j]=matrix[j,i]=value;index+=1
        budget.charge(96*15**3);eigval,eigvec=np.linalg.eigh(matrix)
        if not np.isfinite(eigval).all()or not np.isfinite(eigvec).all():raise OverflowError('finite declared eigensolve')
        backward=float(np.max(np.abs(matrix@eigvec-eigvec*eigval)))
        if not math.isfinite(backward):raise OverflowError('finite eigen backward error')
        eigen_diagnostics.append(dict(block=block,eigenvalues=list(map(float,eigval)),backward_error=backward,proposal_only=True))
        for k in range(15):
            integers=[int(round(float(eigvec[i,k])*(1<<20)))for i in range(15)];budget.charge(15)
            if not any(integers):raise ValueError('nonzero quantized eigenvector')
            if next(v for v in integers if v)<0:integers=[-v for v in integers]
            add(dict(kind='rank_one',block=block,vector=[str(F(v,1<<20))for v in integers],origin='endpoint_eigenvector'))
    out=dict(schema=RAY_SCHEMA,complete=True,width=1224,retained_indices=retained,scalar_projected_indices=scalar,C_projected_indices=C,P_projected_indices=P,records=records,policy=RAY_POLICY,eigen_diagnostics=eigen_diagnostics)
    if len(records)!=851:raise ValueError('complete declared851 rays')
    return out


def coordinate_responses(rows,width,coordinates,budget):
    """Memoized exact reverse substitution for requested coordinate functionals."""
    needed=set();pending=list(coordinates)
    while pending:
        j=pending.pop();budget.charge()
        if j in needed:continue
        if type(j)is not int or not 0<=j<width:raise ValueError('coordinate response domain')
        needed.add(j)
        if j in rows:
            row=rows[j]
            if row.get(j)!=1:raise ValueError('normalized response pivot')
            for k,q in row.items():
                budget.charge()
                if k in(j,width):continue
                if k<j or k>=width:raise ValueError('upper triangular response dependency')
                if q:pending.append(k)
    cache={};cells=0;base=budget.resident_cells
    for j in sorted(needed,reverse=True):
        if j not in rows:r={j:F(1)};t=F(0)
        else:
            row=rows[j];r={};t=budget.q(row.get(width,F(0)))
            for k,q in row.items():
                budget.charge()
                if k in(j,width)or not q:continue
                other,constant=cache[k]
                if constant:t=budget.add(t,-budget.mul(q,constant))
                for index,c in other.items():
                    value=budget.add(r.get(index,F(0)),-budget.mul(q,c))
                    if value:r[index]=value
                    else:r.pop(index,None)
        cache[j]=(r,t);cells+=len(r)+1;budget.resident_cells=base+cells;budget.cells(len(r))
    return {j:cache[j]for j in coordinates},len(needed)


def assemble(rows,width,free,retained,rays,budget):
    scalar,C,P=geometry(retained);coordinates=sorted(set(scalar+C+P));columns=[];column_cells=0
    resident=2*sum(map(len,rows.values()))+16*len(rays['records'])+1224
    budget.resident_cells=resident
    cache,materialized=coordinate_responses(rows,width,coordinates,budget)
    # The complete memo survives during assembly; reserve its peak conservatively.
    for ray in rays['records']:
        w=ray_functional(ray,scalar,C,P,budget);column={};t=F(0)
        for j,q in w.items():
            r,constant=cache[j]
            if constant:t=budget.add(t,budget.mul(q,constant))
            for k,c in r.items():
                value=budget.add(column.get(k,F(0)),budget.mul(q,c))
                if value:column[k]=value
                else:column.pop(k,None)
        if t:column[width]=t
        columns.append(column);column_cells+=len(column);budget.cells(column_cells)
    budget.resident_cells=resident+column_cells;return dict(width=width,free=free,rows=rows,retained=retained,rays=rays,columns=columns,target={width:F(-1)},coordinate_functionals=len(coordinates),materialized_coordinates=materialized)


def finite_float(q):
    value=float(q)
    if not math.isfinite(value)or(q and value==0):raise OverflowError('binary64 coefficient underflow or nonfinite conversion')
    return value


def scaled_model(model,budget):
    keys=[*model['free'],model['width']];columns=model['columns'];m=len(keys);n=len(columns)
    maxima={i:abs(model['target'].get(i,F(0)))for i in keys}
    for col in columns:
        for i,q in col.items():budget.charge();maxima[i]=max(maxima[i],abs(q))
    R={i:(maxima[i]or F(1))for i in keys};D=[];scaled=[]
    for col in columns:
        row_scaled={i:budget.div(q,R[i])for i,q in col.items()};maximum=max(map(abs,row_scaled.values()),default=F(0));d=budget.div(F(1),maximum)if maximum else F(1);D.append(d)
        scaled.append({i:budget.mul(q,d)for i,q in row_scaled.items()})
    b=[budget.div(model['target'].get(i,F(0)),R[i])for i in keys]
    return keys,scaled,b,R,D


def native_work_reserve(m,n,iterations=100):
    if any(type(v)is not int or v<1 for v in(m,n,iterations))or iterations>100:raise ValueError('bounded native dimensions/iterations')
    return dict(initial_factorization=m**3,per_iteration=2*m*n+m*m,max_iterations=iterations,input_and_transport=2*m*n+1048576,total=m**3+iterations*(2*m*n+m*m)+2*m*n+1048576)


def _native_proposal(model,budget,deadline,state):
    budget.resident_cells=2*sum(map(len,model.get('rows',{}).values()))+sum(map(len,model['columns']))+16*len(model.get('rays',{}).get('records',[]))
    keys,columns,b,R,D=scaled_model(model,budget);m=len(keys);n=len(columns);reserve=native_work_reserve(m,n);scaled_cells=sum(map(len,columns));budget.cells(scaled_cells+4*n+4*m)
    if reserve['total']>budget.max_operations-budget.operations:raise OverflowError('complete native factorization/pivot reservation')
    budget.charge(reserve['total'])
    import numpy as np
    import scipy
    from scipy.optimize import linprog
    from scipy.sparse import csc_matrix
    position={i:k for k,i in enumerate(keys)};data=[];indices=[];indptr=[0]
    for col in columns:
        for i,q in sorted(col.items(),key=lambda item:position[item[0]]):data.append(finite_float(q));indices.append(position[i])
        indptr.append(len(data))
    matrix=csc_matrix((data,indices,indptr),shape=(m,n));cost_scale=max(D,default=F(1));cost=np.array([finite_float(budget.div(q,cost_scale))for q in D]);rhs=np.array([finite_float(q)for q in b]);budget.cells(scaled_cells+2*len(data)+4*n+4*m)
    start=time.monotonic();options=dict(presolve=False,maxiter=100,time_limit=max(.001,deadline-time.monotonic()),threads=1);state['options']=options
    # scipy forwards these recognized native HiGHS controls; no second solver.
    import warnings
    with warnings.catch_warnings(record=True)as captured:
        warnings.simplefilter('always');state['attempted']=True;result=linprog(cost,A_eq=matrix,b_eq=rhs,bounds=(0,None),method='highs-ds',options=options)
    vector=None if result.x is None else [float(q)for q in result.x]
    if vector is not None and(len(vector)!=n or not all(math.isfinite(q)for q in vector)):vector=None
    valid_iteration_type=isinstance(result.nit,(int,np.integer))and not isinstance(result.nit,(bool,np.bool_))
    valid_iterations=valid_iteration_type and 0<=int(result.nit)<=100
    out=dict(success=bool(result.success),status=int(result.status),message=str(result.message),iterations=int(result.nit)if valid_iteration_type else None,scaled_vector=vector,elapsed_seconds=time.monotonic()-start,scipy_version=scipy.__version__,options=options,warnings=[str(w.message)for w in captured],reservation=reserve,counts=budget.counts(),policy=LP_POLICY,cost_common_scale=str(cost_scale),attempted=True)
    if not valid_iterations:out.update(success=False,resource_failure='native simplex iteration count unavailable or outside0..100',error_type='NativeIterationBound')
    try:budget.charge(0)
    except (TimeoutError,OverflowError)as error:out.update(success=False,resource_failure=str(error),error_type=type(error).__name__)
    out['counts']=budget.counts()
    return out

def native_proposal(model,*,deadline,max_operations=190000000):
    budget=Budget(deadline,max_operations);start=time.monotonic();state=dict(attempted=False,options=dict(presolve=False,maxiter=100,threads=1,time_limit=None))
    try:return _native_proposal(model,budget,deadline,state)
    except Exception as error:
        return dict(success=False,status=None,message=str(error)or type(error).__name__,error_type=type(error).__name__,resource_failure=str(error),iterations=None,scaled_vector=None,elapsed_seconds=time.monotonic()-start,counts=budget.counts(),policy=LP_POLICY,options=state['options'],attempted=state['attempted'])

def exact_support_solve(columns,target,width,support,budget):
    """Solve once with sparse exact Gaussian elimination; free support values zero."""
    if type(support)is not list or len(support)>443 or support!=sorted(set(support))or any(type(j)is not int or not 0<=j<len(columns)for j in support):raise ValueError('bounded unique native support')
    k=len(support);equation_keys=sorted(set(target)|{i for j in support for i in columns[j]});source=[]
    for i in equation_keys:
        row={a:budget.q(columns[j].get(i,F(0)))for a,j in enumerate(support)if columns[j].get(i,F(0))};rhs=budget.q(target.get(i,F(0)))
        if rhs:row[k]=rhs
        source.append((i,row))
    basis={};source_cells=sum(len(r)for _,r in source);basis_cells=0;budget.cells(source_cells)
    for i,row in sorted(source,key=lambda item:(len(item[1]),item[0])):
        row=dict(row)
        while row:
            p=min(row)
            if p==k:raise ValueError('inconsistent exact native-support equations')
            if p not in basis:
                factor=row[p];basis[p]={j:budget.div(q,factor)for j,q in row.items()};basis_cells+=len(basis[p]);budget.cells(basis_cells+source_cells+len(row));break
            factor=row[p]
            for j,q in basis[p].items():
                value=budget.add(row.get(j,F(0)),-budget.mul(factor,q))
                if value:row[j]=value
                else:row.pop(j,None)
            budget.cells(basis_cells+source_cells+len(row))
    values=EXACT.back_substitute(basis,[F(0)]*k,k,budget)if k else []
    if any(q<0 for q in values):raise ValueError('negative exact reconstructed cone weight')
    full=[F(0)]*len(columns)
    for j,q in zip(support,values):full[j]=q
    for i in equation_keys:
        value=F(0)
        for j in support:
            if i in columns[j]:value=budget.add(value,budget.mul(columns[j][i],full[j]))
        if value!=target.get(i,F(0)):raise ValueError('all reduced exact support equations must hold')
    return full,dict(support=support,support_size=k,rank=len(basis),free_support_coordinates=[j for j in range(k)if j not in basis],free_rule='zero',complete=True)


def certify(rows,width,free,retained,rays,alpha,budget):
    if len(alpha)!=len(rays['records']):raise ValueError('complete alpha vector')
    alpha=[budget.q(q)for q in alpha]
    if any(q<0 for q in alpha):raise ValueError('nonnegative cone combination')
    scalar,C,P=geometry(retained);w={}
    for ray,a in zip(rays['records'],alpha):
        if not a:continue
        for j,q in ray_functional(ray,scalar,C,P,budget).items():w[j]=budget.add(w.get(j,F(0)),budget.mul(a,q))
    residual,t,multipliers=reduce_functional(rows,width,w,budget)
    if residual or t!=F(-1):raise ValueError('exact Farkas residual0 and pairing-1 required')
    pivots=sorted(rows);certificate=dict(schema=CERTIFICATE_SCHEMA,complete=True,width=width,pivot_columns=pivots,free_indices=free,rays=rays,alpha=list(map(str,alpha)),lambda_vector=[str(multipliers.get(p,F(0)))for p in pivots],pairing='-1',combined_functional=[str(w.get(j,F(0)))for j in range(width)],exact_identity_verified=True,**FLAGS)
    return certificate


def search(chart,endpoint,*,deadline,checkpoint=None):
    out=dict(schema=SCHEMA,status='UNKNOWN',certificate=None,ray_policy=RAY_POLICY,lp_policy=LP_POLICY,limits=LIMITS,stage_counts={},**FLAGS)
    def save(phase):
        if checkpoint:checkpoint(dict(phase=phase,status=out['status'],stage_counts=out['stage_counts'],**FLAGS))
    assembly_budget=Budget(deadline,100000000)
    try:
        save('assembly_started');rows,free,retained=decode_chart(chart,assembly_budget);rays=make_rays(retained,endpoint,assembly_budget);model=assemble(rows,1224,free,retained,rays,assembly_budget)
        out.update(assembly_stats=dict(rows=len(free)+1,columns=len(rays['records']),coordinate_functionals=model['coordinate_functionals'],nonzeros=sum(map(len,model['columns']))),rays=rays);out['stage_counts']['assembly']=assembly_budget.counts();save('assembly_complete')
        native=native_proposal(model,deadline=deadline);out['native']=native;out['stage_counts']['native']=native['counts'];save('native_returned')
        if not native['success']or native['scaled_vector']is None:out.update(status='UNKNOWN'if native.get('resource_failure')or native.get('status')==1 else'NONCERTIFIED',reason=native.get('resource_failure')or'native LP did not return a successful finite vector');return out
        support=[j for j,q in enumerate(native['scaled_vector'])if q>0]
        out['native_support']=support
        if len(support)>443:out.update(status='NONCERTIFIED',reason='all-positive native support exceeds443');return out
        restoration=Budget(deadline,60000000);restoration.resident_cells=2*sum(map(len,rows.values()))+sum(map(len,model['columns']))+20*len(rays['records']);save('restoration_started')
        try:
            alpha,stats=exact_support_solve(model['columns'],model['target'],1224,support,restoration);out['restoration_stats']=stats
            certificate=certify(rows,1224,free,retained,rays,alpha,restoration);restoration.charge(len(encoded(certificate)));out.update(status='CERTIFICATE_PROPOSED',certificate=certificate)
        except (ValueError,OverflowError,TimeoutError,MemoryError)as error:out.update(status='NONCERTIFIED'if isinstance(error,ValueError)else'UNKNOWN',reason=str(error),error_type=type(error).__name__)
        out['stage_counts']['restoration']=restoration.counts();save('restoration_returned')
    except Exception as error:out.update(status='UNKNOWN',reason=str(error)or type(error).__name__,error_type=type(error).__name__)
    finally:
        out['stage_counts'].setdefault('assembly',assembly_budget.counts())
    if len(encoded(out))>8388608:raise OverflowError('bounded dual outcome bytes')
    return out
