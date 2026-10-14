"""CSC support proposal, native exact reconstruction, independent full-Gram admission.
Offdiagonal dual moments are restricted to zero: failure is not infeasibility.
Native RREF is not interruptible; an enclosing worker must enforce hard deadlines.
"""
import math
import time
import warnings
from fractions import Fraction as F
import cancellation_gram_synthesis as S
import cancellation_gram_language as L
import check_cancellation_gram as I
import native_exact_support as N
FLAGS = dict(global_bound_proved=False, RH_proved=False)

def support_proposal(columns,lhs,monomials,nonnegative,relations,*,deadline,max_rows,max_variables,max_work):
    """Same y+/y-/slack equation and variable order as native reconstruction."""
    import numpy as np
    from scipy.sparse import csc_matrix
    from scipy.optimize import linprog, OptimizeWarning
    if type(deadline) not in (int,float) or not math.isfinite(deadline):
        raise ValueError('finite deadline')
    if any(type(v)is not int or v<1 for v in (max_rows,max_variables,max_work)):
        raise ValueError('positive integer proposal limits')
    if deadline<=time.monotonic():raise TimeoutError('expired proposal deadline')
    if type(columns)is not list or type(lhs)is not dict or type(monomials)is not list or len(set(monomials))!=len(monomials):
        raise ValueError('proposal domain schema')
    ids=nonnegative+relations
    if any(type(i)is not int or not 0<=i<len(columns)for i in ids) or len(set(ids))!=len(ids) or set(ids)!=set(range(len(columns))):
        raise ValueError('complete unique proposal classifications')
    if set(monomials)!=set(lhs)|{m for p in columns for m in p}:raise ValueError('complete proposal monomial domain')
    selected=relations+nonnegative; rows=len(selected)+1; M=len(monomials)
    variables=2*M+len(nonnegative)
    if rows>max_rows or variables>max_variables or rows*variables>max_work:
        raise OverflowError('dual proposal dimensions/work')
    lookup={m:j for j,m in enumerate(monomials)}; rr=[];cc=[];vv=[]
    def insert(r,j,q):
        v=float(q)
        if not math.isfinite(v) or (q and not v):raise OverflowError('float coefficient overflow/underflow')
        if q:rr.append(r);cc.append(j);vv.append(v)
    for r,i in enumerate(selected):
        for m,q in columns[i].items():
            j=lookup[m];insert(r,j,q);insert(r,M+j,-q)
    for m,q in lhs.items():
        j=lookup[m];insert(rows-1,j,q);insert(rows-1,M+j,-q)
    for j in range(len(nonnegative)):insert(len(relations)+j,2*M+j,-1)
    A=csc_matrix((vv,(rr,cc)),shape=(rows,variables));b=np.zeros(rows);b[-1]=-1
    left=deadline-time.monotonic()
    if left<=0:raise TimeoutError('dual proposal preparation deadline')
    # Explicit native HiGHS thread controls; SciPy forwards these options.
    with warnings.catch_warnings():
        warnings.filterwarnings('ignore',category=OptimizeWarning,
            message=r"Unrecognized options detected: \{'threads': 1, 'parallel': False\}\. These will be passed to HiGHS verbatim\.")
        result=linprog(np.ones(variables),A_eq=A,b_eq=b,bounds=(0,None),method='highs',
                       options={'time_limit':left,'threads':1,'parallel':False})
    diagnostics=dict(solver_status=int(result.status),solver_message=str(result.message),
        threads=1,parallel=False,equation_rows=rows,variables=variables,nonzeros=len(vv),
        objective=float(result.fun) if result.fun is not None and math.isfinite(float(result.fun)) else None)
    if not result.success:return None,diagnostics
    if result.x is None or not np.all(np.isfinite(result.x)):raise ValueError('nonfinite LP support')
    support=[int(j) for j,v in enumerate(result.x) if v>1e-8]
    diagnostics.update(support=support,support_threshold='1e-8',support_size=len(support))
    return support,diagnostics

def propose(instances,scales,*,time_limit=180,max_rows=1500,max_variables=60000,
            max_work=400000000,max_cells=2000000,max_denominator=2**4096,
            max_coefficient_bits=4096,max_columns=1024,max_monomials=30000,
            max_operations=200000000,max_horizon=80,max_degree=12):
    start=time.monotonic();diagnostics={}
    try:
        if type(time_limit) not in (int,float) or not math.isfinite(time_limit) or time_limit<=0:
            raise ValueError('positive finite time limit')
        if any(type(v)is not int or v<1 for v in (max_rows,max_variables,max_work,max_cells,max_denominator,max_coefficient_bits,max_columns,max_monomials,max_operations,max_horizon,max_degree)):
            raise ValueError('positive integer resource limits')
        deadline=start+time_limit
        prepared,lhs,ms,(ns,nr),offset,blocks=S.prepare(instances,scales,deadline=deadline,
            max_columns=max_columns,max_monomials=max_monomials,max_operations=max_operations,
            max_coefficient_bits=max_coefficient_bits,max_horizon=max_horizon,max_degree=max_degree)
        crosses=[j for j,(a,b) in enumerate(S.UPPER) if a<b]
        columns=prepared[:offset]+[{m:q/2 for m,q in prepared[offset+15*k+j].items()}
                                    for k in range(2) for j in crosses]
        monomials=sorted(set(lhs)|{m for p in columns for m in p})
        nonnegative=list(range(ns))+list(range(ns+2*nr,offset))
        relations=list(range(ns,ns+2*nr))+list(range(offset,len(columns)))
        support,diagnostics=support_proposal(columns,lhs,monomials,nonnegative,relations,
             deadline=deadline,max_rows=max_rows,max_variables=max_variables,max_work=max_work)
        if support is None:
            return dict(status='missing_resource' if diagnostics['solver_status']==1 else 'uncertified',
                certified=False,reason='floating solver did not propose support; no exact infeasibility conclusion',diagnostics=diagnostics,**FLAGS)
        left=deadline-time.monotonic()
        if left<=0:raise TimeoutError('native reconstruction deadline')
        out=N.reconstruct_dual_fixed_support(columns,lhs,monomials,nonnegative,relations,support,
            time_limit=left,max_rows=max_rows,max_variables=max_variables,max_work=max_work,
            max_cells=max_cells,max_denominator=max_denominator,max_coefficient_bits=max_coefficient_bits)
        out['proposal_diagnostics']=diagnostics
        if not out.get('certified'):return out
        y=dict(zip(monomials,map(F,out['weights'])));grams={}
        for k,region in enumerate(S.REGIONS):
            H=[[F(0) for _ in range(5)]for _ in range(5)]
            for j,(a,b) in enumerate(S.UPPER):
                value=sum((q*y[m]for m,q in prepared[offset+15*k+j].items()),F(0))
                H[a][b]=H[b][a]=value if a==b else value/2
            if any(H[a][b]for a in range(5)for b in range(5)if a!=b):raise ValueError('restricted cross moment nonzero')
            matrix=[[str(q)for q in row]for row in H]
            grams[region]=dict(matrix=matrix,PSD_certificate=L.ldlt_psd(matrix))
        out.update(monomials=[dict(instance=m[0],m=list(m[1:]))for m in monomials],
            extra_cross_dots=out['columns_dot_y'][offset:],columns_dot_y=out['columns_dot_y'][:offset],
            gram_duals=grams,ordinary_constant_coordinates=[str(y.get((i,),F(0)))for i in range(len(scales))],
            all_C_q_extension_requires_zero_constant_coordinates=all(y.get((i,),F(0))==0 for i in range(len(scales))),
            restricted_dual_search='offdiagonal moments zero; successful witness separates full declared PSD cone',**FLAGS)
        out['independent_check']=I.verify_dual(instances,scales,out)
        if time.monotonic()>deadline:raise TimeoutError('independent verification deadline')
        out['diagnostics']['elapsed_total_seconds']=time.monotonic()-start
        out['independent_full_Gram_check_passed']=True
        return out
    except (OverflowError,TimeoutError,MemoryError,ImportError)as e:
        return dict(status='missing_resource',certified=False,reason=str(e),diagnostics=diagnostics,**FLAGS)
    except (ValueError,TypeError,KeyError,ZeroDivisionError,RuntimeError)as e:
        return dict(status='uncertified',certified=False,reason=str(e),diagnostics=diagnostics,**FLAGS)
