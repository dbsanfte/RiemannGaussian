"""Exact complete mixed-zero certificates in the original Boolean coordinates.

The caller supplies V and must independently establish V^T y0=0 for the
actual original Boolean vector. For any rational partner W, the half-sum
Z=(VW^T+WV^T)/2 evaluates to zero. A rational factor proves Q=LL^T>=0
without accepting any floating PSD assertion. Pricing R+Z+Q then proves the
finite upper bound using y0_i^2=1, retaining every physical and anchor pair.

Unrestricted mixed controls and 085's V S V^T have the same ideal SDP
infimum for the same R,V. This representation adds no arithmetic constraint;
finite attainment and coefficient conditioning may change. Nothing here
proves a uniform bound or RH. See frozen 085 uniform target sections F--H.
"""
from fractions import Fraction as Q
import math
import time
import warnings

import cvxpy as cp
import numpy as np
from flint import fmpq, fmpq_mat

import mobius_coupled_square_084 as SQUARE

B = SQUARE.B
MAX_BANK = 16
MAX_DIMENSION = 512
PARTNER_BITS = 24


def build_model(program, u, meter=None):
    """Retain the fixed original y0 coordinates; never move to null coordinates."""
    model = B.build_model(program, u, meter=meter)
    _gate(model)
    return model


def _gate(model, m=0, bits=64, extra=0, work=0):
    n = model['price_dimension']
    if type(n) is not int or not 0 <= n <= MAX_DIMENSION:
        raise B.ResourceLimit('mixed-zero complete original dimension exceeds512')
    if type(m) is not int or not 0 <= m <= MAX_BANK:
        raise ValueError('mixed-zero bank dimension must be <=16')
    if bits > B.OLD.MAX_BITS:
        raise B.ResourceLimit('mixed-zero prospective cumulative bit budget')
    # Full physical reconstruction remains resident even with a fixed anchor.
    B._basis_budget(model, extra=64*1024**2 + n*n*(4096+8*bits)
                    + n*max(1,m)*(2048+8*bits) + extra)
    model['meter'].charge(work)


def _rows(matrix):
    return [[str(matrix[i,j]) for j in range(matrix.ncols())]
            for i in range(matrix.nrows())]


def parse_vectors(model, vectors, columns=None):
    """Accept a complete E-by-m canonical rational array or exact native matrix."""
    _gate(model)
    n = model['price_dimension']
    if isinstance(vectors, fmpq_mat):
        if vectors.nrows() != n:
            raise ValueError('complete original-coordinate vector rows required')
        m = vectors.ncols()
        _gate(model, m)
        rows = _rows(vectors)
    else:
        if type(vectors) is not list or len(vectors) != n:
            raise ValueError('complete original-coordinate vector rows required')
        m = len(vectors[0]) if n and type(vectors[0]) is list else (columns or 0)
        _gate(model, m)
        if any(type(row) is not list or len(row) != m for row in vectors):
            raise ValueError('rectangular complete exact vector matrix required')
        rows = vectors
    if columns is not None and m != columns:
        raise ValueError('partner must have every original bank column')
    values = [[B.OLD.rational(v) for v in row] for row in rows]
    bits = B.OLD.rational_budget([q for row in values for q in row],
                                model['meter'], terms=max(1,n*m))
    _gate(model, m, bits)
    return fmpq_mat([[str(q) for q in row] for row in values]) if n and m else fmpq_mat(n,m)


def _budget_matrices(model, *matrices, power=1, terms=1, work=0):
    values = [B.OLD.as_q(matrix[i,j]) for matrix in matrices
              for i in range(matrix.nrows()) for j in range(matrix.ncols())]
    bits = B.OLD.rational_budget(values, model['meter'], power=power, terms=max(1,terms))
    _gate(model, max((min(MAX_BANK,a.ncols()) for a in matrices),default=0), bits,work=work)
    return bits


def original_remainder(model):
    """The frozen full remainder in the existing y0 basis, including all pairs.

    project_native is only the already established unit/prime anchor mapping.
    No Pi, rank reduction, cut masking, or new coordinate projection occurs.
    """
    _gate(model)
    matrix = B.project_native(model, SQUARE.R.raw_remainder(model))
    _budget_matrices(model, matrix)
    return matrix


def independent_columns(model, vectors):
    V = parse_vectors(model, vectors)
    n,m = V.nrows(),V.ncols()
    if not n or not m:
        return V, []
    bits = _budget_matrices(model,V)
    # Fraction-free elimination determinants have degree at most m. This is
    # a conservative bound before native rank work, rather than post hoc caps.
    _gate(model,m,m*(bits+max(1,n.bit_length()))+32,work=64*n*m*m*m)
    reduced,rank = V.rref()
    active = [next(j for j in range(m) if reduced[i,j]) for i in range(rank)]
    return V, active


def correction(model, vectors, partner_matrix):
    V = parse_vectors(model,vectors)
    W = parse_vectors(model,partner_matrix,columns=V.ncols())
    n,m = V.nrows(),V.ncols()
    _budget_matrices(model,V,W,power=2,terms=max(1,2*m),work=8*n*n*max(1,m))
    return (V*W.transpose()+W*V.transpose())/fmpq(2) if m else fmpq_mat(n,n)


def _factor_gate(model, den, rows):
    _gate(model)
    SQUARE._factor_gate(model,den,rows)
    n = model['price_dimension']
    rank = len(rows[0]) if n else 0
    # All factor entries share one denominator; cost is charged before Gram.
    bits = 2*(128+den.bit_length())+max(1,rank.bit_length())+32
    _gate(model,bits=bits,work=8*n*n*max(1,rank))


def _certificate(model, vectors, partner_matrix, den, rows, remainder):
    """Internal exact certification against the already frozen R cache."""
    _factor_gate(model,den,rows)
    V = parse_vectors(model,vectors)
    W = parse_vectors(model,partner_matrix,columns=V.ncols())
    R = remainder
    n = model['price_dimension']
    if not isinstance(R,fmpq_mat) or (R.nrows(),R.ncols()) != (n,n) or R != R.transpose():
        raise ValueError('complete symmetric original remainder required')
    Z = correction(model,V,W)
    gram = SQUARE._gram(rows,den)
    # Gate sums with cumulative denominators before exact completed allocation.
    _budget_matrices(model,R,Z,gram,power=1,terms=3,work=8*n*n)
    prices,total = SQUARE._price(R+Z+gram)
    _,baseline = SQUARE._price(R)
    _,zero_only = SQUARE._price(R+Z)
    cert = dict(squarefree_count=model['squarefree_count'],partner_matrix=_rows(W),
                factor_denominator=str(den),factor_numerators=[[str(v) for v in row] for row in rows],
                price=str(total),row_prices=list(map(str,prices)))
    diagnostics = dict(effective_dimension=n,bank_size=V.ncols(),
                       rank=len(rows[0]) if n else 0,
                       original_entrywise_price=str(baseline),mixed_only_entrywise_price=str(zero_only),
                       mixed_trace=str(sum((B.OLD.as_q(Z[i,i]) for i in range(n)),Q(0))),
                       factor_trace=str(sum((B.OLD.as_q(gram[i,i]) for i in range(n)),Q(0))),
                       max_abs_partner=str(max((abs(B.OLD.as_q(W[i,j])) for i in range(n)
                                                for j in range(V.ncols())),default=Q(0))))
    return cert,diagnostics


def certificate(model, vectors, partner_matrix, den, rows):
    """Produce an exact certificate for the fixed full original remainder."""
    return _certificate(model,vectors,partner_matrix,den,rows,original_remainder(model))


def _projection_partner(model, vectors, remainder):
    """Exact Pi R Pi ablation, priced on the same original Boolean coordinates.

    With active U and M=(U^T U)^-1, W=-2 R U M+U M U^T R U M.
    Thus sym(U W^T)=Pi R Pi-R; omitted dependent columns get zero partners.
    The Gram inverse receives degree-based bit, memory and work gates first.
    """
    V,active = independent_columns(model,vectors)
    n,m,r = V.nrows(),V.ncols(),len(active)
    W = fmpq_mat(n,m)
    if not r:
        return W,dict(active_identity_columns=active,identity_rank=0,gram_inverse_used=False)
    R = remainder
    U = fmpq_mat([[V[i,j] for j in active] for i in range(n)])
    bits = _budget_matrices(model,U,power=2,terms=max(1,n),work=8*n*r*r)
    _gate(model,m,r*(bits+max(1,r.bit_length()))+32,
          extra=r*r*(4096+16*r*bits),work=64*r*r*r)
    gram = U.transpose()*U
    _budget_matrices(model,gram,power=max(1,r),terms=max(1,r*r))
    inverse = gram.inv()
    _budget_matrices(model,U,inverse,R,power=5,terms=max(1,n*r*r),work=16*n*n*r+16*n*r*r)
    K = U*inverse
    partner = -2*(R*K)+K*(U.transpose()*R*K)
    _budget_matrices(model,partner)
    for k,j in enumerate(active):
        for i in range(n):W[i,j] = partner[i,k]
    return W,dict(active_identity_columns=active,identity_rank=r,gram_inverse_used=True)


def projection_partner(model, vectors):
    """Produce the exact Pi R Pi partner for the frozen full remainder."""
    return _projection_partner(model,vectors,original_remainder(model))


def _rounded_partner(model, V, active, normalizers, floating, u, bits):
    if type(bits) is not int or not 1 <= bits <= 48:
        raise ValueError('partner dyadic precision1..48 required')
    n,m = V.nrows(),V.ncols()
    if floating.shape != (n,len(active)) or not np.isfinite(floating).all():
        raise ValueError('finite complete numerical partner proposal required')
    scaling_bits = B.OLD.rational_budget(list(normalizers)+[Q(u)],model['meter'],
                                        power=2,terms=max(1,n*m))
    _gate(model,m,scaling_bits,work=16*n*max(1,m))
    for normalizer in normalizers:
        if max(128+u.bit_length()+normalizer.denominator.bit_length(),
               bits+normalizer.numerator.bit_length()) > 4096:
            raise B.ResourceLimit('mixed-zero exact partner unscaling prospective4096bit gate')
    den = 1 << bits
    W = fmpq_mat(n,m)
    for k,j in enumerate(active):
        for i in range(n):
            value = float(floating[i,k])*den
            if not math.isfinite(value) or abs(value) >= 2**128:
                raise B.ResourceLimit('mixed-zero dyadic partner numerator128bit gate')
            # target uses normalized V and R/u; undo both scalings exactly.
            q = Q(round(value),den)*Q(u)/normalizers[k]
            B.OLD.rational(str(q))
            W[i,j] = fmpq(q.numerator,q.denominator)
    _budget_matrices(model,W)
    return W


def solve_model(model, vectors, time_limit=90, projection=True, partner_bits=PARTNER_BITS):
    """SCS proposes only auxiliaries; retain every failure and the exact baseline."""
    started = time.monotonic()
    if not math.isfinite(time_limit) or time_limit <= 0:
        raise ValueError('positive finite solver time limit required')
    if type(partner_bits) is not int or not 1 <= partner_bits <= 48:
        raise ValueError('partner dyadic precision1..48 required')
    V = parse_vectors(model,vectors)
    n,m = V.nrows(),V.ncols()
    R = original_remainder(model)
    zero = fmpq_mat(n,m)
    empty_factor = [[] for _ in range(n)]
    cert,diag = _certificate(model,V,zero,1,empty_factor,R)
    best_cert,best_diag,best_name = cert,diag,'ZERO_CONTROL_ZERO_FACTOR'
    attempts = [dict(name=best_name,status='EXACT_CERTIFICATE',certificate=cert,diagnostics=diag)]
    report = dict(u=model['u'],effective_dimension=n,bank_size=m,
                  arithmetic_operator_coefficients_frozen=True,original_boolean_coordinates_retained=True,
                  unknown_composite_signs_used=False,uniform_remaining_bound_proved=False,RH_proved=False,
                  same_bank_ideal_sdp_infimum_as_085=True,attempts=attempts)

    def admit(name,partner,den,rows,**details):
        nonlocal best_cert,best_diag,best_name
        candidate,diagnostics = _certificate(model,V,partner,den,rows,R)
        attempts.append(dict(name=name,status='EXACT_CERTIFICATE',certificate=candidate,
                             diagnostics=diagnostics,**details))
        if Q(candidate['price']) < Q(best_cert['price']):
            best_cert,best_diag,best_name = candidate,diagnostics,name

    def failure(name,exc):
        attempts.append(dict(name=name,status='RESOURCE_LIMIT' if isinstance(exc,B.ResourceLimit) else 'PROPOSAL_FAILURE',
                             error_type=type(exc).__name__,reason=str(exc)))

    if projection and n:
        try:
            partner,projection_diag = _projection_partner(model,V,R)
            admit('EXACT_PI_R_PI',partner,1,empty_factor,projection=projection_diag)
        except (ValueError,ArithmeticError,OverflowError) as exc:
            failure('EXACT_PI_R_PI',exc)
    try:
        V,active = independent_columns(model,V)
        r = len(active)
        report.update(active_identity_columns=active,identity_rank=r)
        if n:
            # Prospective full SDP workspace includes dense cones and partner.
            _gate(model,m,extra=n*n*8192+n*max(1,r)*1024,work=32*n*n*max(1,r))
            # SCS projects a full PSD cone each iteration. Budget the dense
            # eigensolver and partner applications prospectively, retaining
            # half of remaining work for exact reconstruction and reporting.
            per_iteration = 20*n**3+32*n*n*max(1,r)
            remaining_work = model['meter'].limit-model['meter'].ops
            max_iters = min(20000,max(0,remaining_work//(2*per_iteration)))
            report.update(solver_max_iters=max_iters,solver_work_per_iteration=per_iteration)
            if max_iters < 100:
                raise B.ResourceLimit('mixed-zero prospective solver work leaves fewer than100iterations')
            _gate(model,m,extra=n*n*8192+n*max(1,r)*1024,work=max_iters*per_iteration)
            scale = model['u']
            A = np.array([[float(R[i,j])/scale for j in range(n)] for i in range(n)])
            normalizers = [max([Q(1)]+[abs(B.OLD.as_q(V[i,j])) for i in range(n)]) for j in active]
            normalized = np.array([[float(B.OLD.as_q(V[i,j])/normalizers[k]) for k,j in enumerate(active)] for i in range(n)])
            d = cp.Variable(n)
            variable = cp.Variable((n,r)) if r else None
            target = A+(normalized@variable.T+variable@normalized.T)/2 if r else A
            psd = cp.diag(d)-target >> 0
            problem = cp.Problem(cp.Minimize(cp.sum(d)),[psd])
            with warnings.catch_warnings(record=True) as caught:
                warnings.simplefilter('always')
                problem.solve(solver='SCS',eps_abs=1e-6,eps_rel=1e-6,max_iters=max_iters,
                              time_limit_secs=time_limit,acceleration_lookback=10,verbose=False)
            report.update(solver_status=str(problem.status),solver_seconds=problem.solver_stats.solve_time,
                          solver_iterations=problem.solver_stats.num_iters,warnings=[str(w.message) for w in caught])
            if d.value is None or not np.isfinite(d.value).all():
                raise ValueError('no finite numerical diagonal proposal')
            diagonal = np.asarray(d.value).copy()
            numerical = np.asarray(variable.value).copy() if r and variable.value is not None else np.zeros((n,r))
            if r and variable.value is None:
                raise ValueError('no complete numerical partner proposal')
            objective = float(problem.value)
            if not math.isfinite(objective):
                raise ValueError('no finite numerical objective proposal')
            del problem,psd,target,d,variable,A,normalized
            report['float_objective_over_u'] = objective
            partner = _rounded_partner(model,V,active,normalizers,numerical,scale,partner_bits)
            admit('SCS_MIXED_ZERO_FACTOR',partner,1,empty_factor)
            try:
                Z = correction(model,V,partner)
                _budget_matrices(model,R,Z,terms=2)
                corrected = R+Z
                _gate(model,m,extra=n*n*4096,work=8*n*n)
                floating = np.array([[float(corrected[i,j]) for j in range(n)] for i in range(n)])
                den,rows = SQUARE.factor_from_psd(np.diag(diagonal*scale)-floating,meter=model['meter'])
                admit('SCS_MIXED_POSITIVE_FACTOR',partner,den,rows)
            except (ValueError,ArithmeticError,OverflowError,np.linalg.LinAlgError) as exc:
                failure('SCS_MIXED_POSITIVE_FACTOR',exc)
    except (ValueError,ArithmeticError,OverflowError,cp.error.SolverError,np.linalg.LinAlgError) as exc:
        failure('SCS_MIXED_PROPOSAL',exc)
    report.update(status='EXACT_MIXED_ZERO_SQUARE_PROPOSAL',certificate=best_cert,diagnostics=best_diag,
                  selected_attempt=best_name,price_over_u=str(Q(best_cert['price'])/model['u']),
                  elapsed_seconds=time.monotonic()-started,ops=model['meter'].ops,
                  prospective_peak_bytes=model['meter'].peak_bytes)
    return report


def solve(program, vectors, u, time_limit=90, projection=True, partner_bits=PARTNER_BITS, meter=None):
    return solve_model(build_model(program,u,meter=meter),vectors,time_limit=time_limit,
                       projection=projection,partner_bits=partner_bits)
