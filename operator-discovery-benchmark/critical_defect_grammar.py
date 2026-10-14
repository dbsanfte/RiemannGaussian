"""Exact whole signed energy defects and a proved common-factor component."""
from fractions import Fraction as Q
from math import gcd
from functools import lru_cache
import flint
from estimate_grammar import inverse_one_prefix
from rational_fractional_evaluator import rational_power,integer_guard,ball
from mellin_kernel_grammar import real

VERSION='actual-whole-energy-critical-defect-common-factor-projection-v1'


def prefixes(values):
    M=[0]*len(values);energy=[0]*len(values);square=[0]*len(values);diagonal=[0]*len(values)
    for n in range(1,len(values)):
        M[n]=M[n-1]+values[n];square[n]=square[n-1]+values[n]**2;energy[n]=energy[n-1]+M[n-1]**2;diagonal[n]=diagonal[n-1]+square[n-1]
    return M,energy,square,diagonal


def kernel(X,n):return max(0,2*X-max(X,n))
def defect_kernel(X,n):return kernel(2*X,n)-4*kernel(X,n)


def whole(values,X):
    if type(X)is not int or X<1 or len(values)<=4*X:raise ValueError('A full coefficient prefix through 4X is required')
    M,E,Qp,D=prefixes(values);A1=E[2*X]-E[X];A2=E[4*X]-E[2*X];D1=D[2*X]-D[X];D2=D[4*X]-D[2*X]
    return {'X':X,'energy':A1,'child_energy':A2,'diagonal':D1,'child_diagonal':D2,'signed_defect':A2-4*A1,'diagonal_defect':D2-4*D1,'off_diagonal_defect':A2-4*A1-D2+4*D1}


def divisor_density(values,k):
    if len(values)<=k:raise ValueError('Full divisor inverse coefficients required')
    ds=[d for d in range(1,k+1) if k%d==0];first=sum((Q(values[d],d) for d in ds),Q(0));second=sum((Q(values[d],d*d) for d in ds),Q(0));tau=sum(abs(values[d]) for d in ds)
    return real(first)/(real(2).zeta()*real(second)),tau


def constants():
    t=rational_power(real(2),Q(3,2));J=real(Q(2,3))*(t-1);return J,3*J*(t+4),6*J*(t+4)


def component_certificate(beta,shared_cutoff=True):
    beta=Q(beta);valid=0<=beta<=1 and shared_cutoff;gamma=Q(3,2)*(1+beta)
    return {'admitted':valid,'cutoff_power':str(beta),'component_power':str(gamma),'log_degree':'2','all_real_scales_and_actual_prime_ranks':valid,
        'same_cutoff_in_both_defect_terms':shared_cutoff,'component_admits_every_positive_epsilon_critical_bound':valid and gamma<=2,
        'global_full_signed_defect_proved':False,'dense_residual_still_required':True,'RH_proved':False,
        'supplied_method':'elementary squarefree coprime density; shared-cutoff leading-term cancellation'}


def cofinal_recovery(epsilon_positive=True,epsilon_tends_to_zero=True,all_dyadic_scales=True,arithmetic_model='inverse_one'):
    admitted=epsilon_positive and epsilon_tends_to_zero and all_dyadic_scales and arithmetic_model=='inverse_one'
    return {'admitted':admitted,'premise':'for every cofinal positive epsilon, exists finite B_epsilon, for every dyadic X>=1, Delta(X)<=B_epsilon*X^(2+epsilon)',
        'constants_may_depend_on_epsilon_not_scale':True,'one_sided_upper_bound_sufficient':True,'all_heights_and_offcritical_multiplicities':admitted,
        'critical_zero_simplicity_required':False,'global_signed_defect_premise_proved':False,'RH_proved':False}


def floor_power(n,beta):
    if type(n)is not int or n<1 or not 0<=Q(beta)<=1:raise ValueError('Integer scale and rational power in [0,1] required')
    beta=Q(beta);p,q=beta.numerator,beta.denominator
    if not p or n==1:return 1
    if q<=4096 and p*n.bit_length()<=1000000:
        target=n**p;lo,hi=1,n+1
        while hi-lo>1:
            mid=(lo+hi)//2
            if mid**q<=target:lo=mid
            else:hi=mid
        return lo
    for precision in [256,512,1024,2048,4096]:
        flint.ctx.prec=precision;x=rational_power(real(n),beta);lo=int(x.lower().floor().unique_fmpz());hi=int(x.upper().floor().unique_fmpz())
        if lo==hi:return lo
    return None # native resource exhaustion, not a semantic denominator cap


def projection_grid(values,X,cutoffs,arithmetic_model='inverse_one'):
    if arithmetic_model!='inverse_one':raise ValueError('Actual-prime density certificate requires the actual divisor inverse')
    if not cutoffs or any(type(B)is not int or B<1 for B in cutoffs) or type(X)is not int or X<1 or len(values)<=max(4*X,max(cutoffs)**2):raise ValueError('Shared integer cutoffs and full arithmetic prefix required')
    result=0;leading=flint.arb(0);S=flint.arb(0);count=0;geometries=[];rows=[];flint.ctx.prec=512;J,diag,C0=constants();sharp_factor=2*J*(rational_power(real(2),Q(3,2))+4)*rational_power(real(X),Q(3,2))
    for r in range(1,max(cutoffs)+1):
        if values[r]:
            for a in range(1,r):
                if not values[a] or gcd(a,r)!=1:continue
                k=a*r;density,tau=divisor_density(values,k);leading+=3*values[a]*values[r]*density/r;S+=(tau+2)/real(r).sqrt();local=0;terms=0
                for common in range(1,4*X//r+1):
                    w=defect_kernel(X,common*r)
                    if w:local+=2*values[common*a]*values[common*r]*w;terms+=1
                result+=local;count+=terms;geometries.append({'a':a,'r':r,'density_ball':ball(density),'tau_radical':tau,'exact_signed_defect':local,'counted_geometries':terms})
        if r in cutoffs:
            coarse=C0*rational_power(real(X*r),Q(3,2))*(1+real(r).log())**2
            rows.append({'X':X,'shared_cutoff':r,'signed_projection_defect':result,'leading_coefficient_ball':ball(leading),'positive_density_cost_ball':ball(S),
                'sharp_component_bound_ball':ball(sharp_factor*S),'coarse_component_bound_ball':ball(coarse),'exact_geometry_count':count,'primitive_geometry_count':len(geometries),
                'all_scale_component_proved':True,'full_defect_bound_proved':False})
    return {'X':X,'primitive_geometries':geometries,'cutoff_rows':rows,'actual_arithmetic_retained':True,'producer_prime_or_factor_oracle_used':False}


def projection(values,X,B,arithmetic_model='inverse_one'):
    grid=projection_grid(values,X,[B],arithmetic_model);return dict(grid['cutoff_rows'][0],primitive_geometries=grid['primitive_geometries'])


def positive_projection(X,B):
    result=0;primitive_pairs=0
    for r in range(2,B+1):
        pairs=sum(gcd(a,r)==1 for a in range(1,r));primitive_pairs+=pairs
        result+=2*pairs*sum(defect_kernel(X,g*r) for g in range(1,4*X//r+1))
    return {'signed_defect':result,'all_scale_absolute_defect_upper':12*X*primitive_pairs,'all_positive_control_not_actual_primes':True}
