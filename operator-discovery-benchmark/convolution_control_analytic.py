"""Exact actual c=mu*lambda component identities, not an ordinary energy proof."""
from fractions import Fraction as Q
from math import isqrt


def integer(n,minimum=0):
    if type(n) is not int or n<minimum:
        raise ValueError('integer outside domain')
    return n


def factor(n):
    integer(n,1)
    result=[];p=2
    while p*p<=n:
        k=0
        while n%p==0:n//=p;k+=1
        if k:result.append((p,k))
        p=3 if p==2 else p+2
    if n>1:result.append((n,1))
    return result


def actual_coefficients(N):
    integer(N,1)
    mu=[0]*(N+1);lam=[0]*(N+1);c=[0]*(N+1);h=[0]*(N+1);tau=[0]*(N+1)
    for n in range(1,N+1):
        fs=factor(n);omega=len(fs);Omega=sum(k for p,k in fs)
        mu[n]=0 if any(k>1 for p,k in fs) else (-1)**omega
        lam[n]=(-1)**Omega;c[n]=lam[n]*(1<<omega);h[n]=1<<omega
        tau[n]=1
        for p,k in fs:tau[n]*=k+1
    return {'mu':mu,'lambda':lam,'c':c,'h':h,'tau':tau,'arithmetic_origin':'complete independent integer factorization','ordinary_signed_energy_bound_proved':False}


def convolution(left,right):
    if len(left)!=len(right):raise ValueError('equal complete coefficient horizons required')
    N=len(left)-1;out=[0]*(N+1)
    for d in range(1,N+1):
        for m in range(1,N//d+1):out[d*m]+=left[d]*right[m]
    return out


def sampled_prefix_certificate(N):
    integer(N,1)
    coefficients=actual_coefficients(3*N);c=coefficients['c'];C=[0]
    for value in c[1:]:C.append(C[-1]+value)
    T=[0]
    for m in range(1,N+1):T.append(T[-1]+c[3*m])
    sampled=[0]+[c[3*(n-1)] if n>1 else 0 for n in range(1,N+1)]
    S=[0]
    for value in sampled[1:]:S.append(S[-1]+value)
    valid=all(T[x]==-2*C[x]+T[x//3] for x in range(N+1)) and all(S[n]==T[n-1] for n in range(1,N+1))
    if not valid:raise RuntimeError('actual sampling identity failure')
    return {'N':N,'sampled_zero_index_convention':'c(0)=0, a(1)=0','exact_identity_verified_through_N':True,'C':C[:N+1],'T':T,'S':S,'global_identity':'T(x)=-2C(x)+T(floor(x/3)), S(n)=T(n-1)','conditional_ordinary_zeta_bridge':'all dyadic sampled block energies Oq(X^(2+1/q)) for every q>=q0 imply critical C energy and ordinary zeta zero exclusion','ordinary_signed_energy_bound_proved':False,'RH_proved':False}


def square_divisor_certificate(x):
    integer(x,0)
    if x==0:return {'x':0,'signed_filtered_sum':0,'unsigned_charge':0,'squarefloor':0,'ordinary_signed_energy_bound_proved':False}
    coeff=actual_coefficients(x);c=coeff['c'];h=coeff['h'];tau=coeff['tau']
    D=[0]
    for value in tau[1:]:D.append(D[-1]+value)
    signed=sum(c[d]*D[x//d] for d in range(1,x+1))
    unsigned=sum(h[d]*D[x//d] for d in range(1,x+1))
    if signed!=isqrt(x):raise RuntimeError('actual c*tau square identity failure')
    return {'x':x,'signed_filtered_sum':signed,'unsigned_charge':unsigned,'squarefloor':isqrt(x),'global_identity':'c*tau=IndicatorSquares; Prefix(c*tau,x)=floor(sqrt(x))','actual_prime_power_origin':'c(p^j)=2*(-1)^j, tau(p^j)=j+1','ordinary_signed_energy_bound_proved':False,'RH_proved':False}


def primepower_box_certificate(prime_exponents):
    pairs=list(prime_exponents)
    if len({p for p,k in pairs})!=len(pairs):raise ValueError('distinct primes required')
    signed=1;unsigned=1
    for p,k in pairs:
        integer(p,2);integer(k)
        if factor(p)!=[(p,1)]:raise ValueError('prime required')
        local=1+sum(2*(-1)**j for j in range(1,k+1))
        if local!=(-1)**k:raise RuntimeError('local alternating sum failure')
        signed*=local;unsigned*=1+2*k
    return {'prime_exponents':pairs,'signed_box_sum':signed,'unsigned_box_charge':unsigned,'all_scale_signed_box_bound':1,'scope':'complete rectangular exponent box only, not n<=x prefix','ordinary_signed_energy_bound_proved':False,'RH_proved':False}


def powered_two_countermodel(k,A=2):
    integer(k);integer(A,1)
    N=1<<k;value=1+sum(2*(-A)**j for j in range(1,k+1))
    # Complete support on powers2; prefix constant on [2^k,2^(k+1)).
    return {'A':A,'dyadic_X':N,'prefix_at_X':value,'exact_block_energy':N*value*value,'local_positive_inverse':'h2(z)=(1+A*z)/(1-A*z)','local_signed_inverse':'c2(z)=(1-A*z)/(1+A*z)','h_equals_abs_c':True,'sign_involution':True,'complete_inverse_identity':True,'actual_prime_power_constraint_at_2_satisfied':A==1,'all_actual_prime_power_constraints_satisfied':False,'actual_h_at_2_required':2,'countermodel_h_at_2':2*A,'scope':'generic positive-inverse/involution countermodel, not actual mu*lambda','sampled_at_3_all_zero':True}


def nonnegative_potential_bridge_certificate():
    return {'schema':1,'base':'A_C(X)=sum_(n=X)^(2X-1)C(n)^2, E_C=A_C/X^2','potential_hypothesis':'V(X) is finite and nonnegative at every dyadic X>=1, with exact child reevaluation','innovation_premise':'exists q0>=1; every integer q>=q0 has finite Cq>=0 independent of X; every dyadic X>=1: E_C(2X)+V(2X)-E_C(X)-V(X)<=Cq ceil(X^(1/q))','conditional_normalized_bound':'E_C(X)<=E_C(1)+V(1)+2Cq*(X^(1/q)-1)/(2^(1/q)-1)','ordinary_zeta_bridge':'the full premise implies critical C energy, hence ordinary zeta zero exclusion and RH','conditional_bridge_valid':True,'premise_proved':False,'RH_proved':False,'moving_index_rule':'every selector d(X) is reevaluated as d(2X) in V(2X), including floors, max and normalizers; every auxiliary truncation/complement is retained'}


def diagonal_potential_certificate(X):
    """Actual finite check of root's COMPLETE diagonal feature semantics."""
    integer(X,1)
    data=actual_coefficients(2*X-1);c=data['c'];h=data['h'];tau=data['tau'];C=[0]
    for value in c[1:]:C.append(C[-1]+value)
    A=sum(C[t]**2 for t in range(X,2*X));Sh=0;Stau=0
    for t in range(X,2*X):
        hs=0;ts=0
        for d in range(1,t+1):
            v=C[t//d];Sh+=h[d]**2*v*v;Stau+=tau[d]**2*v*v
            hs+=h[d]*v;ts+=tau[d]*v
        if hs!=1 or ts!=isqrt(t):raise RuntimeError('complete row forcing mismatch')
    Rh=Sh-A;difference=Stau-Sh
    if Rh<0 or difference<0:raise RuntimeError('diagonal nonnegativity failure')
    lower={}
    if X>=2 and X&(X-1)==0:
        previous=sum(C[t]**2 for t in range(X//2,X))
        if Rh<8*previous:raise RuntimeError('diagonal h lower bound')
        lower['Rh_ge_8A_C_X_over_2']=8*previous
    if X>=4 and X&(X-1)==0:
        previous=sum(C[t]**2 for t in range(X//4,X//2))
        if difference<20*previous:raise RuntimeError('diagonal difference lower bound')
        lower['Rdiff_ge_20A_C_X_over_4']=20*previous
    return {'X':X,'A_C':A,'S_h':Sh,'S_tau':Stau,'R_h':Rh,'R_diff':difference,'nonnegative_global_identity':'Rh=sum_(t inblock)sum_(d>=2)h(d)^2 C(floor(t/d))^2; Rdiff=sum_(t inblock)sum_d(tau(d)^2-h(d)^2)C(floor(t/d))^2','unconditional_upper_envelope':'S_tau<=64X^3(1+log(2X))^2','lower_energy_comparisons':lower,'full_row_forcing_not_diagonal_bound':True,'ordinary_signed_energy_bound_proved':False,'RH_proved':False}


def potential_family_audit(family, eta=Q(0), root_order=2, k=Q(1)):
    """Critical-boundness types, not fitted-candidate decisions."""
    eta=Q(eta);k=Q(k);integer(root_order,1)
    if eta<0:raise ValueError('nonnegative eta required')
    if family in ('diagonal_R_h','diagonal_R_diff'):
        power=Q(1)-eta;degree=2
        description='nonnegative complete diagonal; critical-energy-comparable at eta0, weakened comparison when eta>0'
    elif family in ('mixed_square_fixed','mixed_square_moving','three_square'):
        power=Q(1);degree=2
        description='nonnegative square retaining the unthinned C(t); no unconditional critical estimate; moving quotient must be reevaluated at child'
    elif family=='pure_root_thinning':
        power=Q(-1)+Q(2,root_order);degree=2
        description='ordinary exponent2 test is too weak for k>=2; correct critical raw-energy exponent1+1/k'
    else:raise ValueError('unknown potential family')
    classification='bounded with a finite parameter-dependent constant' if power<0 else 'globally subpower upper envelope' if power==0 else 'only polynomial weak upper envelope; not certified critical-bounded'
    return {'family':family,'eta':str(eta),'root_order':root_order,'mixed_coefficient':str(k),'upper_power_after_normalization_X2':str(power),'polylog_degree':degree,'unconditional_classification':classification,'mechanism':description,'ordinary_zeta_bridge_from_feature_alone_proved':False,'RH_proved':False}
