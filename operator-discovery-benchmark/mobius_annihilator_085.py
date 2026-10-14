"""Synthesize signed products of exact annihilators and positive square bounds."""
from fractions import Fraction as Q
import time
import warnings
import numpy as np
import cvxpy as cp
from flint import fmpq_mat
import mobius_coupled_square_084 as SQUARE

B=SQUARE.B
MAX_BANK=16


def parse_bank(bank):
    if type(bank)is not list or len(bank)>MAX_BANK:raise ValueError('annihilator bank<=16')
    result=[]
    for d in bank:
        if type(d)is not dict or set(d)!={'scale','u_exponent','complement','unit_balance'}:raise ValueError('exact annihilator descriptor')
        a,e=B.OLD.rational(d['scale']),B.OLD.rational(d['u_exponent'])
        if a<=0 or type(d['complement'])is not bool or type(d['unit_balance'])is not bool:raise ValueError('positive scale and strict flags')
        result.append(dict(scale=a,u_exponent=e,complement=d['complement'],unit_balance=d['unit_balance']))
    return result


def identity_integer_column(model,descriptor):
    SQUARE._gate(model)
    d=parse_bank([descriptor])[0];N=model['N'];n=model['coordinates']
    cut=dict(d,n_exponent=Q(0));K=B.cut_value(1,model['u'],N,cut,model['meter'])
    raw=K//n-(n==1)*(K>0);den=1
    if d['unit_balance']and N>=2:
        den=N-1;raw=den*raw-max(K-1,0)*(N//n-(n==1))
    if not model['program']['prime_anchor']:raise ValueError('joint unit/prime anchor required')
    if not len(n):return [],den,K
    column=[int(model['known_signs']@raw)]+[int(raw[i])for i in model['composite_indices']]
    model['meter'].charge(8*len(n))
    return column,den,K


def identity_vectors(model,bank):
    parse_bank(bank);n=model['price_dimension'];m=len(bank);SQUARE._gate(model)
    model['meter'].reserve(model['resident_bytes']+model['extra_resident_bytes']+(model['squarefree_count']+n)*max(1,m)*2048+n*n*8192)
    cols=[identity_integer_column(model,d)for d in bank]
    matrix=fmpq_mat([[str(Q(col[i],den))for col,den,_ in cols]for i in range(n)])if n and m else fmpq_mat(n,m)
    return matrix,[c[2]for c in cols]


def correction(model,V,identity_matrix):
    n=model['price_dimension'];m=V.ncols()
    if len(identity_matrix)!=m or any(len(row)!=m for row in identity_matrix):raise ValueError('complete signed identity matrix')
    values=[[B.OLD.rational(str(v))for v in row]for row in identity_matrix]
    if any(values[i][j]!=values[j][i]for i in range(m)for j in range(i)):raise ValueError('symmetric exact identity matrix')
    bits=B.OLD.rational_budget([v for row in values for v in row],model['meter'],terms=max(1,n*n*m))
    B._basis_budget(model,extra=n*n*(8192+4*bits)+(n+m)*max(1,m)*(1024+bits))
    model['meter'].charge(n*n*max(1,m)*16)
    if not m:return fmpq_mat(n,n)
    H=fmpq_mat([[str(v)for v in row]for row in values])
    return V*H*V.transpose()


def certificate(model,bank,identity_matrix,den,rows):
    SQUARE._factor_gate(model,den,rows);n=model['price_dimension'];V,cuts=identity_vectors(model,bank)
    base=B.project_native(model,SQUARE.R.raw_remainder(model));Z=correction(model,V,identity_matrix)
    gram=SQUARE._gram(rows,den);prices,total=SQUARE._price(base+Z+gram)
    _,original=SQUARE._price(base);_,identity_only=SQUARE._price(base+Z)
    model['meter'].charge(n*n*max(1,len(rows[0])if n else 0)*4)
    cert=dict(squarefree_count=model['squarefree_count'],identity_matrix=[[str(v)for v in row]for row in identity_matrix],
              factor_denominator=str(den),factor_numerators=[[str(v)for v in row]for row in rows],price=str(total),row_prices=list(map(str,prices)))
    diagnostics=dict(cuts=cuts,effective_dimension=n,bank_size=len(bank),rank=len(rows[0])if n else 0,
                     original_entrywise_price=str(original),identity_only_entrywise_price=str(identity_only),
                     identity_trace=str(sum((B.OLD.as_q(Z[i,i])for i in range(n)),Q(0))),
                     factor_trace=str(sum((B.OLD.as_q(gram[i,i])for i in range(n)),Q(0))))
    return cert,diagnostics


def solve(program,bank,u,time_limit=90):
    started=time.monotonic();parse_bank(bank);model=B.build_model(program,u);n=model['price_dimension'];m=len(bank)
    SQUARE._gate(model,m*m)
    if not n:raise ValueError('nonempty geometry required')
    V,cuts=identity_vectors(model,bank);native=B.project_native(model,SQUARE.R.raw_remainder(model))
    reduced,rank=V.rref()if m else (V,0)
    active=[next(j for j in range(m)if reduced[i,j])for i in range(rank)]
    model['meter'].charge(n*max(1,m)**3*64)
    A=np.array([[float(native[i,j])/u for j in range(n)]for i in range(n)])
    normalizers=[max([Q(1)]+[abs(B.OLD.as_q(V[i,j]))for i in range(n)])for j in active]
    W=np.array([[float(B.OLD.as_q(V[i,j])/normalizers[k])for k,j in enumerate(active)]for i in range(n)])
    d=cp.Variable(n);H=cp.Variable((rank,rank),symmetric=True)if rank else None
    target=A+W@H@W.T if rank else A
    psd=cp.diag(d)-target>>0;problem=cp.Problem(cp.Minimize(cp.sum(d)),[psd])
    with warnings.catch_warnings(record=True)as caught:
        warnings.simplefilter('always')
        problem.solve(solver='SCS',eps_abs=1e-6,eps_rel=1e-6,max_iters=20000,time_limit_secs=time_limit,acceleration_lookback=10,verbose=False)
    report=dict(status='NO_ANNIHILATOR_PROPOSAL',u=u,bank=bank,cuts=cuts,effective_dimension=n,
                active_identity_columns=active,identity_rank=rank,
                solver_status=str(problem.status),solver_seconds=problem.solver_stats.solve_time,solver_iterations=problem.solver_stats.num_iters,
                warnings=[str(w.message)for w in caught],arithmetic_operator_coefficients_frozen=True,
                new_identity_matrix_and_positive_factor=True,unknown_composite_signs_used=False,
                uniform_remaining_bound_proved=False,RH_proved=False)
    if d.value is None or not np.isfinite(d.value).all():return report
    diagonal=np.asarray(d.value).copy();objective=float(problem.value)
    h=np.asarray(H.value).copy()if rank and H.value is not None else np.zeros((rank,rank))
    if not np.isfinite(h).all():return report
    del problem,psd,target,d,H,A,W
    model['extra_resident_bytes']+=n*n*256+m*m*1024
    identity=[[Q(0)for _ in range(m)]for _ in range(m)]
    for i in range(rank):
        for j in range(i,rank):
            value=Q(round(float((h[i,j]+h[j,i])/2)*(1<<24)),1<<24)*u/(normalizers[i]*normalizers[j])
            identity[active[i]][active[j]]=identity[active[j]][active[i]]=value
    Z=correction(model,V,identity);corrected=native+Z
    floating=np.array([[float(corrected[i,j])for j in range(n)]for i in range(n)])
    denominator,rows=SQUARE.factor_from_psd(np.diag(diagonal*u)-floating,meter=model['meter'])
    cert,diag=certificate(model,bank,identity,denominator,rows)
    if Q(cert['price'])>Q(diag['identity_only_entrywise_price']):
        report['rejected_square_price']=cert['price'];cert,diag=certificate(model,bank,identity,1,[[]for _ in range(n)])
        report['factor_fallback']='ZERO_POSITIVE_FACTOR_HAS_SMALLER_EXACT_PRICE'
    report.update(status='EXACT_ANNIHILATOR_SQUARE_PROPOSAL',certificate=cert,diagnostics=diag,
                  float_objective_over_u=objective,price_over_u=str(Q(cert['price'])/u),
                  elapsed_seconds=time.monotonic()-started,ops=model['meter'].ops,prospective_peak_bytes=model['meter'].peak_bytes)
    return report
