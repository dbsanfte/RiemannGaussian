"""Bounded numerical proposals only; exact admission must use original equations.

No numerical rank truncation or cone/column transformation is performed.
"""
from fractions import Fraction as F
import hashlib
import json
import math
import time
import warnings


def _digest(value):
    return hashlib.sha256(json.dumps(value,sort_keys=True,separators=(',',':')).encode()).hexdigest()


def compress_rows(rows,rhs,n_variables,*,deadline,max_operations=200000000,max_cells=4000000,max_coefficient_bits=4096):
    """Remove exactly zero/proportional augmented rows, in original order.

    Original row i = multiplier[i] * retained row representative[i], including
    its target. None representatives denote the identically zero equation.
    A positive exact scale divides each retained row before float conversion.
    """
    if type(deadline) not in (int,float) or not math.isfinite(deadline):raise ValueError('finite deadline')
    if any(type(x)is not int or x<1 for x in (n_variables,max_operations,max_cells,max_coefficient_bits)):raise ValueError('positive strict limits')
    if type(rows)is not list or type(rhs)is not list or len(rows)!=len(rhs):raise ValueError('row/target schema')
    operations=0;cells=0;clean=[];targets=[];retained=[];representatives=[];multipliers=[];scales=[];seen={};inconsistent=[]
    def charge(amount):
        nonlocal operations
        operations+=amount
        if operations>max_operations:raise OverflowError('compression operation cap')
        if time.monotonic()>deadline:raise TimeoutError('compression deadline')
    def rational(x):
        if type(x) not in (int,F):raise ValueError('exact rational coefficients required')
        q=F(x)
        if max(abs(q.numerator).bit_length(),q.denominator.bit_length())>max_coefficient_bits:raise OverflowError('compression coefficient bits')
        return q
    for i,(row,b) in enumerate(zip(rows,rhs)):
        if type(row)is not dict or any(type(j)is not int or not 0<=j<n_variables for j in row):raise ValueError('sparse row schema')
        charge(1+len(row));cells+=len(row)+1
        if cells>max_cells:raise OverflowError('compression cell cap')
        exact={j:rational(q) for j,q in sorted(row.items())}
        p={j:q for j,q in exact.items() if q};b=rational(b)
        if not p and b:inconsistent.append(i)
        pivot=next(iter(p.values()),b)
        if not pivot:
            representatives.append(None);multipliers.append('0');continue
        canonical=tuple((j,str(rational(q/pivot))) for j,q in p.items())+((n_variables,str(rational(b/pivot))),)
        charge(len(p)+1)
        if canonical in seen:
            k,first_pivot=seen[canonical];representatives.append(k);multipliers.append(str(rational(pivot/first_pivot)))
        else:
            k=len(clean);seen[canonical]=(k,pivot);clean.append(p);targets.append(b);retained.append(i)
            representatives.append(k);multipliers.append('1');scales.append(max([abs(b)]+[abs(q) for q in p.values()]))
    encoded=[[[j,str(q)] for j,q in sorted(row.items())] for row in rows]
    receipt=dict(schema='primitive-state-exact-row-compression-v1',original_hash=_digest(dict(rows=encoded,rhs=list(map(str,rhs)),variables=n_variables)),
        original_rows=len(rows),variables=n_variables,retained_indices=retained,row_representative=representatives,
        row_multiplier=multipliers,row_scales=list(map(str,scales)),variable_mapping='identity',
        inconsistent_zero_rows=inconsistent,operations=operations,cells=cells,
        limits=dict(max_operations=max_operations,max_cells=max_cells,max_coefficient_bits=max_coefficient_bits))
    return clean,targets,receipt


def _matrix(rows,rhs,n_variables,receipt):
    import numpy as np
    from scipy.sparse import csc_matrix
    rr=[];cc=[];vv=[];bb=[]
    def number(q):
        x=float(q)
        if not math.isfinite(x) or (q and x==0):raise OverflowError('float coefficient overflow/underflow')
        return x
    for i,(row,b,s) in enumerate(zip(rows,rhs,receipt['row_scales'])):
        scale=F(s);bb.append(number(b/scale))
        for j,q in row.items():rr.append(i);cc.append(j);vv.append(number(q/scale))
    return csc_matrix((vv,(rr,cc)),shape=(len(rows),n_variables)),np.asarray(bb)


def _domain(columns,lhs,monomials):
    if type(columns)is not list or type(lhs)is not dict or type(monomials)is not list or len(set(monomials))!=len(monomials):raise ValueError('proposal domain')
    if set(monomials)!=set(lhs)|{m for p in columns for m in p}:raise ValueError('complete monomial domain')


def support_proposal(columns,lhs,monomials,nonnegative,relations,*,deadline,max_rows,max_variables,max_work,max_cells=4000000,max_coefficient_bits=4096):
    """LP support in original y+/y-/slack order; signed rows compress exactly."""
    import numpy as np
    from scipy.optimize import linprog,OptimizeWarning
    _domain(columns,lhs,monomials)
    if any(type(v)is not int or v<1 for v in (max_rows,max_variables,max_work,max_cells,max_coefficient_bits)):raise ValueError('positive strict proposal limits')
    ids=nonnegative+relations
    if any(type(i)is not int or not 0<=i<len(columns) for i in ids) or len(set(ids))!=len(ids) or set(ids)!=set(range(len(columns))):raise ValueError('complete classifications')
    M=len(monomials);variables=2*M+len(nonnegative);selected=relations+nonnegative
    if len(selected)+1>max_rows or variables>max_variables or (len(selected)+1)*variables>max_work:raise OverflowError('dual dimensions/work')
    if 2*sum(len(columns[i]) for i in selected)+len(nonnegative)+2*len(lhs)+len(selected)+1>max_cells:raise OverflowError('dual assembly cell cap')
    lookup={m:j for j,m in enumerate(monomials)};rows=[]
    for i in selected:
        row={}
        for m,q in columns[i].items():j=lookup[m];row[j]=q;row[M+j]=-q
        rows.append(row)
    for j in range(len(nonnegative)):rows[len(relations)+j][2*M+j]=F(-1)
    rows.append({j:q for m,q in lhs.items() for j,q in ((lookup[m],q),(M+lookup[m],-q))})
    rhs=[F(0)]*len(selected)+[F(-1)]
    compressed,targets,receipt=compress_rows(rows,rhs,variables,deadline=deadline,max_operations=max_work,max_cells=max_cells,max_coefficient_bits=max_coefficient_bits)
    diagnostics=dict(transformation_receipt=receipt,threads=1,parallel=False,attempts=[],equation_rows=len(rows),variables=variables)
    if receipt['inconsistent_zero_rows']:
        diagnostics.update(solver_status=None,solver_message='inconsistent exact zero row; no solver called');return None,diagnostics
    A,b=_matrix(compressed,targets,variables,receipt);left=deadline-time.monotonic()
    if left<=0:raise TimeoutError('LP preparation deadline')
    with warnings.catch_warnings():
        warnings.simplefilter('ignore',OptimizeWarning)
        try:result=linprog(np.ones(variables),A_eq=A,b_eq=b,bounds=(0,None),method='highs',options={'time_limit':left,'threads':1,'parallel':False})
        except Exception as e:
            diagnostics.update(solver_status=None,solver_message=str(e));diagnostics['attempts'].append(dict(solver='highs',error=str(e)));return None,diagnostics
    attempt=dict(solver='highs',status=int(result.status),message=str(result.message));diagnostics['attempts'].append(attempt)
    diagnostics.update(solver_status=attempt['status'],solver_message=attempt['message'])
    if not result.success or result.x is None:return None,diagnostics
    if time.monotonic()>deadline:
        diagnostics['deadline_exceeded']=True;return None,diagnostics
    values=np.asarray(result.x).reshape(-1)
    if len(values)!=variables or not np.all(np.isfinite(values)):
        diagnostics['invalid_values']=True;return None,diagnostics
    support=[int(j) for j,x in enumerate(values) if x>1e-8]
    diagnostics.update(support=support,support_threshold='1e-8',support_size=len(support))
    return support,diagnostics


def primal_proposal(columns,lhs,monomials,shape,offset,specs,*,deadline,max_operations=200000000,max_cells=4000000,max_coefficient_bits=4096):
    """SDP vector in original scalar/upper-triangle order, identity PSD map."""
    import cvxpy as cp
    import numpy as np
    _domain(columns,lhs,monomials)
    if type(offset)is not int or not 0<=offset<=len(columns) or len(shape)!=2 or any(type(n)is not int or n<0 for n in shape):raise ValueError('primal layout')
    if any(type(n)is not int or n<1 for n in specs.values()) or offset+sum(n*(n+1)//2 for n in specs.values())!=len(columns) or shape[0]+2*shape[1]>offset:raise ValueError('complete PSD layout')
    if sum(map(len,columns))+len(monomials)>max_cells:raise OverflowError('SDP assembly cell cap')
    if sum(map(len,columns))+len(monomials)>max_operations:raise OverflowError('SDP assembly operation cap')
    lookup={m:i for i,m in enumerate(monomials)};rows=[{} for m in monomials]
    for j,p in enumerate(columns):
        for m,q in p.items():rows[lookup[m]][j]=q
    compressed,targets,receipt=compress_rows(rows,[lhs.get(m,F(0)) for m in monomials],len(columns),deadline=deadline,max_operations=max_operations,max_cells=max_cells,max_coefficient_bits=max_coefficient_bits)
    diagnostics=dict(transformation_receipt=receipt,numerical_threads=1,attempts=[],optimality_claim=False)
    if receipt['inconsistent_zero_rows']:diagnostics['reason']='inconsistent exact zero row';return None,diagnostics
    A,b=_matrix(compressed,targets,len(columns),receipt)
    scalar=cp.Variable(offset,nonneg=True) if offset else None
    matrices={r:cp.Variable((n,n),symmetric=True) for r,n in specs.items()}
    entries=([scalar] if offset else [])+[matrices[r][a,b] for r,n in specs.items() for a in range(n) for b in range(a,n)]
    vector=cp.hstack(entries)
    objective=(cp.sum(scalar[:shape[0]+2*shape[1]]) if shape[0]+2*shape[1] else 0)+sum(cp.trace(v) for v in matrices.values())
    constraints=([A@vector==b] if compressed else [])+[v>>0 for v in matrices.values()]
    problem=cp.Problem(cp.Minimize(objective),constraints);left=deadline-time.monotonic()
    if left<=0:raise TimeoutError('SDP preparation deadline')
    error=None
    try:problem.solve(solver='CLARABEL',time_limit=left,max_threads=1)
    except cp.error.SolverError as e:error=str(e)
    diagnostics['attempts'].append(dict(solver='CLARABEL',status=problem.status,error=error))
    diagnostics.update(sdp_status=problem.status,solver_error=error)
    if vector.value is None:return None,diagnostics
    values=np.asarray(vector.value).reshape(-1)
    if len(values)!=len(columns) or not np.all(np.isfinite(values)):
        diagnostics['invalid_values']=True;return None,diagnostics
    diagnostics['support']=[j for j in range(offset) if values[j]>1e-7]+list(range(offset,len(columns)))
    if error or problem.status not in ('optimal','optimal_inaccurate') or time.monotonic()>deadline:
        diagnostics['unaccepted_vector']=values.tolist();return None,diagnostics
    return values,diagnostics
