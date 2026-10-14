#!/usr/bin/env python3
"""Exact recovery benchmark for the QRH manuscripts' finite arithmetic spine.

This calibrates identities and grammar coverage, not the manuscripts' global
mean-square bounds. No upstream executable code is run.
"""

from fractions import Fraction as Q
from itertools import product
from math import isqrt
from pathlib import Path
import json
import random
import time

BASE=Path(__file__).resolve().parent
DEST=BASE/'qrh-results'


def ea(u,v):return (u[0]+v[0],u[1]+v[1])
def en(u):return (-u[0],-u[1])
def em(u,v):
    # omega^2=-1-omega.
    a,b=u;c,d=v;return (a*c-b*d,a*d+b*c-b*d)
def ec(u):return (u[0]-u[1],-u[1])
def ep(u,k):
    out=(1,0)
    for _ in range(k):out=em(out,u)
    return out


ROOTS=[ep((1,1),k) for k in range(6)]  # exp(pi*i/3)=1+omega.
ZERO=(0,0)


def canonical(values,p):
    last=values[p-1]
    return tuple(ea(v,en(last)) for v in values[:p-1])


def scale(v,a):return tuple(em(x,a) for x in v)


def multiply(u,v,p):
    ans=[ZERO]*p
    for i,a in enumerate(u):
        if a==ZERO:continue
        for j,b in enumerate(v):
            if b!=ZERO:ans[(i+j)%p]=ea(ans[(i+j)%p],em(a,b))
    return canonical(ans,p)


def primary(p):
    bound=2*isqrt(p)+3
    return next((a,b) for b in range(3,bound,3) for a in range(-bound,bound)
                if a%3==1 and a*a-a*b+b*b==p)


def character(p,pi):
    a,b=pi;omega_mod=(-a*pow(b,-1,p))%p;z=(1+omega_mod)%p
    lookup={pow(z,k,p):k for k in range(6)};assert len(lookup)==6
    return [None]+[lookup[pow(x,(p-1)//6,p)] for x in range(1,p)]


def gauss(p,pi,j,k=1,wrong_nonunit=False):
    chi=character(p,pi);out=[ZERO]*p
    if wrong_nonunit:out[0]=(1,0)
    for x in range(1,p):
        index=(-pi[1]*k*x)%p
        out[index]=ea(out[index],ROOTS[(j*chi[x])%6])
    return canonical(out,p)


def recover_gauss():
    # Search g_-1*g_3 = unit * pi_or_conjugate * chi(-1)^a *
    # chi(4)^b * g_j. The source TeX predicts unit=-1,a=1,b=1,j=2,
    # with the conjugated generator. PDF text extraction loses its overbars.
    models=list(product(range(6),(0,1),range(3),range(6),('pi','conjugate_pi')))
    rows=[];trained=models
    for p in (7,13,19,31,37,43,61):
        pi=primary(p);chi=character(p,pi);gs=[gauss(p,pi,j) for j in range(6)]
        target=multiply(gs[5],gs[3],p)
        survivors=[]
        for unit,a,b,j,orientation in trained:
            coefficient=pi if orientation=='pi' else ec(pi)
            coefficient=em(coefficient,ROOTS[(unit+a*chi[p-1]+b*chi[4])%6])
            if scale(gs[j],coefficient)==target:survivors.append((unit,a,b,j,orientation))
        trained=survivors
        rows.append({'prime_norm':p,'primary_generator':list(pi),'programs_remaining':len(trained),
                     'training':p in (7,13),'all_passed':bool(trained)})
    assert trained==[(3,1,1,2,'conjugate_pi')],trained
    return {'programs_scored':len(models),'training_prime_norms':[7,13],
            'held_out_prime_norms':[19,31,37,43,61],'records':rows,
            'survivors':[{'unit_power':3,'chi_minus_one_power':1,'chi_four_power':1,
                          'gauss_character_power':2,'generator_orientation':'conjugate_pi'}],
            'identity':'-g_-1(pi)*g_3(pi)*conjugate(chi_pi(4))=chi_pi(-1)*conjugate(pi)*g_2(pi)',
            'exact_coefficient_field':'Q(omega,zeta_p), reduced modulo Phi_p over Q(omega)',
            'known_identity_recovery':True,'all_passed':True}


def phases_and_masks():
    checks=0;wrong=[];models=list(range(1,13));power_models=models
    for p in (7,13,19,31,37,43,61):
        pi=primary(p);chi=character(p,pi)
        power_models=[k for k in power_models if all((0 if x==0 else (k*chi[x])%6)==0 for x in range(p))]
        for k in range(1,p):
            for j in (1,2,3,5):
                lhs=gauss(p,pi,j,k);rhs=scale(gauss(p,pi,j),ROOTS[(-j*chi[k])%6])
                assert lhs==rhs;checks+=1
        assert gauss(p,pi,1,0)==tuple([ZERO]*(p-1))
        # At a nonunit, sixth-power and inverse-character identities need zero
        # masks. For x=0 a character cannot be replaced by its unit value 1.
        wrong.append({'prime_norm':p,'row':0,'chi_zero_sixth_power':0,
                      'unqualified_sixth_power_prediction':1,'rejected':True})
        assert gauss(p,pi,1,0,True)!=gauss(p,pi,1,0)
    assert power_models==[6,12]
    # The minimal positive power is selected, with 12 an equivalent multiple.
    return {'finite_Fourier_covariance_identities_checked':checks,
            'annihilating_powers_found':power_models,'minimal_character_annihilator':6,
            'sixth_power_identity':'chi_pi(v**6)=1[pi does not divide v]',
            'sextic_to_quadratic_power_identity':'chi^-1*chi^-2=chi^-3=chi^3 on units; both sides zero on nonunits when the full masks are retained',
            'wrong_nonunit_controls':wrong,'all_passed':True}


def mu(n):
    sign=1;p=2
    while p*p<=n:
        if n%p==0:
            n//=p;sign=-sign
            if n%p==0:return 0
        p+=1
    return -sign if n>1 else sign


def cube_inverse():
    rng=random.Random(2026100703);N=4096
    # Rational-integer proxy for the universal divisor composition. The
    # theorem works on ideals too; this is not a theta-reflection test.
    P=[Q(0)]+[Q(rng.randrange(-2,3),rng.randrange(1,7)) for _ in range(N)]
    def transform(values,inverse):
        result=[Q(0)]*len(values)
        for b in range(1,isqrt(N)+1):
            if b**3>N:break
            w=Q(mu(b) if inverse else 1,b)
            if w:
                for n in range(1,N//b**3+1):result[n*b**3]+=w*values[n]
        return result
    T=transform(P,False);assert transform(T,True)==P
    assert transform(transform(P,True),False)==P
    wrong=T[8];assert wrong!=P[8]
    return {'coefficient_cutoff':N,'two_universal_inverse_laws_verified':True,
            'law':'T(X)=sum_b w(b)/N(b)*P(X/N(b)**3); P(X)=sum_d mu(d)w(d)/N(d)*T(X/N(d)**3)',
            'scope':'Exact integer proxy for the divisor identity with completely multiplicative w; not the number-field theta energy estimate',
            'discard_cube_terms_is_inverse_rejected':True,'all_passed':True}


def compensation():
    # Act on arbitrary finite completed-index coefficients and rational scale
    # weights. Integer proxy isolates the whole-index mask and scale algebra.
    terms=[(c,n,Q((c+2*n)%7-3,5)) for c in (1,2,3,5,7) for n in (1,2,3,5)]
    def probe(X,Y,Z,marked):
        return sum((a*(X+c)*(Y+n)*(Z+c*n**3) for c,n,a in terms
                    if all((c*n**3)%p==0 for p in marked)),Q(0))
    slots=(2,3,5);norms={p:p*p for p in slots}  # Q^-3/2 is rational.
    def composed(index,X,Y,Z,marked):
        if index==len(slots):return probe(X,Y,Z,marked)
        p=slots[index];q=norms[p]
        return composed(index+1,X,Y,Z*q,marked+(p,))-Q(1,p**3)*composed(index+1,X/q,Y/q,Z,marked)
    X,Y,Z=Q(11),Q(17),Q(23);expanded=Q(0)
    for bits in product((0,1),repeat=len(slots)):
        J=[p for p,b in zip(slots,bits) if b];marked=tuple(p for p,b in zip(slots,bits) if not b)
        qJ=1;qM=1;weight=Q((-1)**len(J))
        for p in J:qJ*=norms[p];weight/=p**3
        for p in marked:qM*=norms[p]
        expanded+=weight*probe(X/qJ,Y/qJ,Z*qM,marked)
    assert expanded==composed(0,X,Y,Z,())
    assert (1*2**3)%2==0 and 1%2!=0  # Marking c alone loses a cube contribution.
    assert (2*1**3)%2==0 and 1%2!=0  # Marking n alone loses a c contribution.
    # Rational local algebra from section 16, valid even at P=0.
    A,V,W,D,Pstar=Q(3,2),Q(1,5),Q(2,7),Q(1,11),Q(5,13)
    P=Pstar+1/(1-V)+W/(1-W)
    G=((A-W)*(1-V)*(1-W)*Pstar-W*(1-V*W))/(1-D)
    assert A*Pstar-W*P==(1-D)*G/((1-V)*(1-W))
    Pstar=-1/(1-V)-W/(1-W);P=Q(0)
    G=((A-W)*(1-V)*(1-W)*Pstar-W*(1-V*W))/(1-D)
    assert A*Pstar-W*P==(1-D)*G/((1-V)*(1-W))
    return {'prime_slots':list(slots),'subset_expansion_terms':2**len(slots),
            'one_prime_operator':'conjugate(eta(p))*Mark_p I(X,Y,Z*Np) - Np**(-3/2)*I(X/Np,Y/Np,Z)',
            'whole_completed_index_mask_required':True,
            'squarefree_part_only_divisibility_counterexample':{'c':1,'n':2,'p':2},
            'cube_part_only_divisibility_counterexample':{'c':2,'n':1,'p':2},
            'fixed_slot_subset_composition_verified':True,
            'local_replacement_identity_verified_at_raw_factor_zero':True,
            'scope':'Universal mask/scale algebra and principal-row local rational replacement (W=Q^-w); coefficient tables are integer proxies, not full cubic-theta probes',
            'all_passed':True}


def main():
    start=time.monotonic();g=recover_gauss();phase=phases_and_masks();cube=cube_inverse();comp=compensation()
    commit=json.loads((DEST/'reference/upstream_commit.json').read_text())
    out={'source_commit':commit,'Gauss_conversion_recovery':g,'character_Fourier_and_mask_controls':phase,
         'cube_completion_inverse_control':cube,'prime_compensation_control':comp,
         'current_integer_only_grammar_can_express_full_QRH_construction':False,
         'new_finite_character_grammar_recovers_tested_Gauss_identity':True,
         'full_theta_reflection_implemented':False,'global_mean_square_bounds_independently_verified':False,
         'entire_QRH_proof_independently_verified':False,'historically_new_operator_established':False,
         'all_passed':g['all_passed'] and phase['all_passed'] and cube['all_passed'] and comp['all_passed'],
         'seconds':time.monotonic()-start}
    (DEST/'qrh_operator_benchmark.json').write_text(json.dumps(out,indent=2)+'\n')
    print('QRH finite arithmetic benchmark',out['all_passed'],'programs',g['programs_scored'],
          'Fourier identities',phase['finite_Fourier_covariance_identities_checked'],'seconds',out['seconds'],flush=True)


if __name__=='__main__':main()
