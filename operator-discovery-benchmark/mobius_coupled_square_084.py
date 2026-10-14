"""Invent coupled residual operators and exact rational square majorants.

SCS proposals are never certificates. A dyadic factor L proves positivity
of L L^T exactly; its complete Boolean price is independently recomputed.
SCS settings: https://www.cvxgrp.org/scs/api/settings.html
"""
from copy import deepcopy
from fractions import Fraction as Q
import time
import warnings
import numpy as np
import cvxpy as cp
from flint import fmpq,fmpq_mat
import mobius_coupled_completion_083 as B
import mobius_coupled_remainder_083 as R
import mobius_coupled_outer_control_083 as O

MAX_DIMENSION=512
FACTOR_BITS=24


def theta_equalities(program):
    system=O.equality_constraints(program)
    if system['status']!='OUTER_EQUALITY_SYSTEM':raise ValueError('outer proof family: '+str(system))
    t=len(program['coupled_terms']);gram=list(map(Q,program['gram_weights']))
    return dict(rows=[row[:t]for row in system['rows']],
                rhs=[str(Q(rhs)-sum((Q(a)*w for a,w in zip(row[t:],gram)),Q(0)))for row,rhs in zip(system['rows'],system['rhs'])])


def _gate(model,templates=0):
    n=model['price_dimension'];g=model['squarefree_count']
    if n>MAX_DIMENSION:raise B.ResourceLimit('square completion whole effective dimension exceeds512')
    B._basis_budget(model,extra=g*g*1024+n*n*(4096+64*templates)+64*1024**2)


def _zero_outer(model,matrix):
    indices=[i for i,v in enumerate(model['coordinates'])if model['u']<5*int(v) and 4*int(v)<=model['u']]
    if isinstance(matrix,np.ndarray):matrix[np.ix_(indices,indices)]=0
    else:
        for i in indices:
            for j in indices:matrix[i,j]=0
    return matrix


def native_template(model,index):
    _gate(model)
    numerator,den=B.coupled_basis(model,index)
    # A copy is needed: cached integer columns remain reusable.
    z=_zero_outer(model,numerator.copy())
    return B.project_native(model,fmpq_mat(z.tolist())/fmpq(den))


def native_base(model):
    raw=deepcopy(model['raw'])
    for term in raw['coupled_terms']:term['theta']='0'
    zero=dict(model,raw=raw,program=B.parse_program(raw))
    return B.project_native(zero,R.raw_remainder(zero))


def float_basis(model):
    t=len(model['cuts']);_gate(model,t);n=model['price_dimension']
    base=native_base(model);base=np.array([[float(base[i,j])for j in range(n)]for i in range(n)])
    basis=np.empty((n*n,t))
    for j in range(t):
        numerator,den=B.coupled_basis(model,j)
        matrix=B.project_float(model,_zero_outer(model,numerator.astype(float)))/den
        basis[:,j]=matrix.reshape(-1,order='F')
    model['meter'].charge(max(1,t)*model['squarefree_count']**2*8)
    return base,basis


def factor_from_psd(matrix,bits=FACTOR_BITS,unit_rows=False,meter=None):
    if type(bits)is not int or bits<1 or bits>48 or not isinstance(matrix,np.ndarray)or matrix.ndim!=2 or matrix.shape[0]!=matrix.shape[1]:raise ValueError('square factor shape/precision')
    n=matrix.shape[0]
    if n>MAX_DIMENSION:raise B.ResourceLimit('factor eigensolver dimension exceeds512 before allocation')
    meter=meter or B.Meter();meter.reserve(64*1024**2+n*n*2048);meter.charge(20*n**3)
    if not np.isfinite(matrix).all():raise ValueError('finite factor proposal')
    if not n:return 1,[]
    values,vectors=np.linalg.eigh((matrix+matrix.T)/2)
    active=values>0
    L=vectors[:,active]*np.sqrt(np.maximum(values[active],0))[None,:]
    if unit_rows:
        norms=np.linalg.norm(L,axis=1)
        L=L/(np.maximum(1,norms)[:,None])*(1-2**-20)
    den=1<<bits
    rows=[[int(round(float(v)*den))for v in row]for row in L]
    if any(abs(v).bit_length()>128 for row in rows for v in row):raise B.ResourceLimit('factor numerator128bit gate')
    if unit_rows:
        for row in rows:
            # Exact contraction, rarely needed after the strict numeric margin.
            while sum(v*v for v in row)>den*den:
                row[:]=[v//2 for v in row]
    return den,rows


def _gram(rows,den):
    n=len(rows);rank=len(rows[0])if n else 0
    if not rank:return fmpq_mat(n,n)
    L=fmpq_mat(rows)
    return L*L.transpose()/fmpq(den*den)


def _price(matrix):
    rows=[]
    for i in range(matrix.nrows()):
        rows.append(B.OLD.as_q(matrix[i,i])+sum((abs(B.OLD.as_q(matrix[i,j]))for j in range(matrix.ncols())if i!=j),Q(0)))
    return rows,sum(rows,Q(0))


def _factor_gate(model,den,rows):
    _gate(model);n=model['price_dimension']
    if len(rows)!=n or any(len(row)!=(len(rows[0])if n else 0)for row in rows):raise ValueError('factor complete coordinate shape')
    if type(den)is not int or den<1 or den>(1<<48)or den&(den-1):raise ValueError('dyadic factor denominator')
    if (len(rows[0])if n else 0)>n or any(type(v)is not int or abs(v).bit_length()>128 for row in rows for v in row):raise ValueError('factor rank/numerator gate')


def certificate(model,den,rows):
    _factor_gate(model,den,rows);n=model['price_dimension']
    raw=B.project_native(model,R.raw_remainder(model));gram=_gram(rows,den);completed=raw+gram
    prices,total=_price(completed);_,baseline=_price(raw)
    model['meter'].charge(n*n*max(1,len(rows[0])if n else 0)*4)
    return dict(squarefree_count=model['squarefree_count'],factor_denominator=str(den),
                factor_numerators=[[str(v)for v in row]for row in rows],price=str(total),row_prices=list(map(str,prices))),dict(
                old_residual_price=str(baseline),factor_trace=str(sum((B.OLD.as_q(gram[i,i])for i in range(n)),Q(0))),
                rank=len(rows[0])if n else 0,effective_dimension=n)


def dual_certificate(model,den,rows,multipliers):
    _factor_gate(model,den,rows);n=model['price_dimension'];t=len(model['cuts']);eq=theta_equalities(model['raw'])
    if len(rows)!=n or any(sum(v*v for v in row)>den*den for row in rows):raise ValueError('dual row norm<=1 required')
    if len(multipliers)!=len(eq['rows']):raise ValueError('all exact equality multipliers required')
    for q in multipliers:B.OLD.rational(str(q))
    B.OLD.rational_budget(multipliers,model['meter'],terms=max(1,t*len(multipliers)))
    X=_gram(rows,den)
    for i in range(n):X[i,i]=1
    base=native_base(model)
    right=fmpq_mat([[X[i,j]]for i in range(n)for j in range(n)])
    def contraction(A):
        if not n:return Q(0)
        return B.OLD.as_q((fmpq_mat([[A[i,j]for i in range(n)for j in range(n)]])*right)[0,0])
    base_value=contraction(base);values=[]
    for k in range(t):values.append(contraction(native_template(model,k)))
    modified=[v+sum((lam*Q(row[k])for lam,row in zip(multipliers,eq['rows'])),Q(0))for k,v in enumerate(values)]
    lower=base_value-sum((lam*Q(rhs)for lam,rhs in zip(multipliers,eq['rhs'])),Q(0))-16*sum(map(abs,modified))
    model['meter'].charge((t+1)*n*n*16)
    return dict(squarefree_count=model['squarefree_count'],factor_denominator=str(den),
                factor_numerators=[[str(v)for v in row]for row in rows],
                equality_multipliers=list(map(str,multipliers)),lower_bound=str(lower))


def solve(program,u,optimize_operator=True,time_limit=180):
    started=time.monotonic();model=B.build_model(program,u);n=model['price_dimension'];t=len(model['cuts']);_gate(model,t)
    if not n:
        cert,diag=certificate(model,1,[])
        return dict(status='EXACT_EMPTY_GEOMETRY',program=deepcopy(program),certificate=cert,diagnostics=diag)
    scale=float(u);d=cp.Variable(n);eq=theta_equalities(program);constraints=[];eq_constraint=None
    if optimize_operator:
        base,basis=float_basis(model);theta=cp.Variable(t)
        target=(base+cp.reshape(basis@theta,(n,n),order='F'))/scale
        constraints += [theta>=-16,theta<=16]
        if eq['rows']:
            eq_constraint=np.array([[float(Q(v))for v in row]for row in eq['rows']])@theta==np.array([float(Q(v))for v in eq['rhs']])
            constraints.append(eq_constraint)
    else:
        raw=B.project_native(model,R.raw_remainder(model))
        target=np.array([[float(raw[i,j])/scale for j in range(n)]for i in range(n)])
    psd=cp.diag(d)-target>>0;constraints.append(psd);problem=cp.Problem(cp.Minimize(cp.sum(d)),constraints)
    with warnings.catch_warnings(record=True)as caught:
        warnings.simplefilter('always')
        problem.solve(solver='SCS',eps_abs=1e-6,eps_rel=1e-6,max_iters=20000,time_limit_secs=time_limit,
                      acceleration_lookback=10,verbose=False)
    report=dict(status='SCS_NO_PROPOSAL',solver_status=str(problem.status),solver_iterations=problem.solver_stats.num_iters,
                solver_seconds=problem.solver_stats.solve_time,warnings=[str(w.message)for w in caught],
                u=u,effective_dimension=n,squarefree_count=model['squarefree_count'],operator_optimized=optimize_operator,
                auxiliary_factor_synthesized_at_this_geometry=True,unknown_composite_signs_used=False,
                observed_full_source_values_used=False,uniform_remaining_bound_proved=False,RH_proved=False)
    if d.value is None or not np.isfinite(d.value).all():return report
    diagonal=np.asarray(d.value).copy()
    dual_matrix=np.asarray(psd.dual_value).copy()if psd.dual_value is not None else None
    equality_dual=np.asarray(eq_constraint.dual_value).copy()if eq_constraint is not None else None
    float_objective=float(problem.value)
    theta_values=np.asarray(theta.value).copy()if optimize_operator and theta.value is not None else None
    # Release full SDP and basis expressions before exact native factor work.
    del problem,target,constraints,psd,eq_constraint,d
    if optimize_operator:del base,basis,theta
    model['extra_resident_bytes']+=n*n*128+t*1024
    proposal=deepcopy(program)
    if optimize_operator:
        if theta_values is None or not np.isfinite(theta_values).all():return report
        values,attempts=B.reconstruct_parameters(list(theta_values),eq,[(-16,16)]*t,model['meter'])
        report['equality_reconstruction']=attempts
        if values is None:
            report['status']='EXACT_AFFINE_RECONSTRUCTION_FAILED';return report
        for term,value in zip(proposal['coupled_terms'],values):term['theta']=str(value)
    fitted=dict(model,raw=proposal,program=B.parse_program(proposal))
    outer=O.synthesize(proposal)
    if outer['status']!='PROPOSED_UNIFORM_WHOLE_OUTER_CONTROL':raise ValueError('reconstructed outer family '+str(outer))
    exact=B.project_native(fitted,R.raw_remainder(fitted));floating=np.array([[float(exact[i,j])for j in range(n)]for i in range(n)])
    denominator,factor=factor_from_psd(np.diag(diagonal*scale)-floating,meter=model['meter'])
    cert,diag=certificate(fitted,denominator,factor)
    # The zero square is a sound fallback, retained explicitly as an ablation.
    if Q(cert['price'])>Q(diag['old_residual_price']):
        report['rejected_square_price']=cert['price'];cert,diag=certificate(fitted,1,[[]for _ in range(n)])
        report['factor_fallback']='ZERO_SQUARE_HAS_SMALLER_EXACT_PRICE'
    report.update(status='EXACT_SQUARE_PROPOSAL',program=proposal,outer_certificate=outer['certificate'],
                  certificate=cert,diagnostics=diag,float_objective_over_u=float_objective)
    if optimize_operator and dual_matrix is not None and np.isfinite(dual_matrix).all():
        dual_den,U=factor_from_psd(dual_matrix,unit_rows=True,meter=model['meter'])
        multipliers=[B.OLD.rounded(float(v)*scale)for v in equality_dual]if equality_dual is not None else[]
        dual=dual_certificate(model,dual_den,U,multipliers)
        if Q(dual['lower_bound'])>Q(cert['price']):raise ArithmeticError('exact square primal/dual gap')
        report.update(dual=dual,exact_gap=str(Q(cert['price'])-Q(dual['lower_bound'])),
                      dual_scope='All theta boxes with exact outer equations, fixed energy/Gram and same complete coupled roster; finite u only')
    report.update(elapsed_seconds=time.monotonic()-started,ops=model['meter'].ops,prospective_peak_bytes=model['meter'].peak_bytes)
    return report
