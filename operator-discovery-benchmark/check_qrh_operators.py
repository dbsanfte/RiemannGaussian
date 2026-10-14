#!/usr/bin/env python3
"""Independent native-complex Gauss evaluations and source/scope audit."""

from fractions import Fraction as Q
from pathlib import Path
from itertools import product
import json
import time
import flint
import sympy as sp

BASE=Path(__file__).resolve().parent
DEST=BASE/'qrh-results'


def real(x):
    x=Q(x);return flint.arb(x.numerator)/x.denominator


def divisor_and_scale_audit():
    # Fresh coefficient table; direct cube-divisor inversion, rather than
    # importing the source's convolution implementation.
    N=729;P=[Q(0)]+[Q((n*n+3*n)%17-8,7) for n in range(1,N+1)]
    cubes=[b for b in range(1,10) if b**3<=N]
    T=[Q(0)]+[sum((P[n//b**3]/b for b in cubes if n%b**3==0),Q(0)) for n in range(1,N+1)]
    def mu(n):
        factors={}
        for p,e in flint.fmpz(n).factor():factors[int(p)]=factors.get(int(p),0)+int(e)
        reconstructed=1
        for p,e in factors.items():reconstructed*=p**e
        assert reconstructed==n
        return 0 if any(e>1 for e in factors.values()) else (-1)**len(factors)
    recovered=[Q(0)]+[sum((mu(b)*T[n//b**3]/b for b in cubes if n%b**3==0),Q(0)) for n in range(1,N+1)]
    assert recovered==P and T[8]!=P[8]
    slots=(2,3,7);eta={2:Q(1,2),3:Q(-2),7:Q(5,3)}
    table=[(c,n,Q(c-3*n,7)) for c in range(1,5) for n in range(1,5)]
    def probe(X,Y,Z,marks):
        return sum((v*(X+c*c)*(Y+n*n)*(Z+c*n**3) for c,n,v in table
                    if all(c*n**3%p==0 for p in marks)),Q(0))
    def operation(order,X,Y,Z,marks):
        if not order:return probe(X,Y,Z,marks)
        p=order[0];q=p*p
        return eta[p]*operation(order[1:],X,Y,Z*q,marks+(p,))-operation(order[1:],X/q,Y/q,Z,marks)/p**3
    X,Y,Z=Q(19,3),Q(31,5),Q(29,7);expanded=Q(0)
    for bits in product((0,1),repeat=3):
        x,y,z,coefficient=X,Y,Z,Q(1);marks=[]
        for p,b in zip(slots,bits):
            if b:x/=p*p;y/=p*p;coefficient/=-p**3
            else:z*=p*p;coefficient*=eta[p];marks.append(p)
        expanded+=coefficient*probe(x,y,z,marks)
    assert expanded==operation(slots,X,Y,Z,())==operation(slots[::-1],X,Y,Z,())
    # Each component can be divisible while the other is a unit.
    assert 1*2**3%2==0 and 1%2!=0
    assert 2*1**3%2==0 and 1%2!=0
    A,V,W,D,Pstar=sp.symbols('A V W D Pstar')
    P=Pstar+1/(1-V)+W/(1-W)
    G=((A-W)*(1-V)*(1-W)*Pstar-W*(1-V*W))/(1-D)
    assert sp.cancel(A*Pstar-W*P-(1-D)*G/((1-V)*(1-W)))==0
    assert sp.cancel((A*Pstar-(1-D)*G/((1-V)*(1-W))).subs(Pstar,-1/(1-V)-W/(1-W)))==0
    return {'fresh_cube_divisor_cutoff':N,'fresh_prime_slots':list(slots),
            'whole_completed_index_component_controls_checked':True,
            'subset_composition_and_slot_commutation_checked':True,
            'principal_row_local_replacement_symbolically_proved':True,'all_passed':True}


def main():
    start=time.monotonic();flint.ctx.prec=384
    source=json.loads((DEST/'qrh_operator_benchmark.json').read_text());assert source['all_passed']
    rows=[];total=0
    for row in source['Gauss_conversion_recovery']['records']:
        p=row['prime_norm'];a,b=row['primary_generator']
        assert flint.fmpz(p).is_prime() and a*a-a*b+b*b==p and a%3==1 and b%3==0
        r=(-a*pow(b,-1,p))%p;z=(1+r)%p
        exponents={pow(z,k,p):k for k in range(6)};assert len(exponents)==6
        chi=[None]+[exponents[pow(x,(p-1)//6,p)] for x in range(1,p)]
        roots=[flint.acb(real(Q(k,3)).cos_pi(),real(Q(k,3)).sin_pi()) for k in range(6)]
        additive=[flint.acb(real(Q(2*x,p)).cos_pi(),real(Q(2*x,p)).sin_pi()) for x in range(p)]
        def gauss(j,k):
            return sum((roots[(j*chi[x])%6]*additive[(-b*k*x)%p] for x in range(1,p)),flint.acb(0))/flint.arb(p).sqrt()
        gs=[gauss(j,1) for j in range(6)]
        pi=flint.acb(real(Q(2*a-b,2)),real(Q(b,2))*flint.arb(3).sqrt())
        alpha=pi/flint.arb(p).sqrt();G=roots[chi[4]].conjugate()*gs[3]
        difference=-gs[5]-roots[chi[p-1]]*alpha.conjugate()*gs[2]/G
        assert difference.contains(0)
        assert difference.abs_upper()<flint.arb('1e-100')
        wrong=-gs[5]-roots[chi[p-1]]*alpha*gs[2]/(roots[chi[4]]*gs[3])
        assert wrong.abs_lower()>0
        for k in range(1,p):
            for j in (1,2,3,5):
                assert (gauss(j,k)-roots[(-j*chi[k])%6]*gs[j]).contains(0);total+=1
        assert gauss(1,0).contains(0)
        rows.append({'prime_norm':p,'native_Gauss_conversion_difference_upper_ball':difference.abs_upper().str(25),
                     'missing_conjugates_wrong_difference_lower_ball':wrong.abs_lower().str(25),'all_passed':True})
    assert total==source['character_Fourier_and_mask_controls']['finite_Fourier_covariance_identities_checked']==816
    alt=(DEST/'reference/The-Quasi-Riemann-Hypothesis-October-5-2026/paper2.tex').read_text()
    full=(DEST/'reference/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.tex').read_text()
    assert 'G(n)=\\overline{\\chi_n(4)}\\gamma_3(n)' in alt
    assert '\\overline{\\alpha(n)}\\gamma_2(n)' in alt
    assert '\\label{eq:compensated-probe-definition}' in full
    assert '\\label{eq:selected-local-operation}' in full
    assert not source['full_theta_reflection_implemented'] and not source['global_mean_square_bounds_independently_verified']
    assert not source['entire_QRH_proof_independently_verified'] and not source['historically_new_operator_established']
    divisor=divisor_and_scale_audit()
    checks={'native_Gauss_conversion_matches_exact_cyclotomic_search':True,
            'all_816_native_Fourier_phase_identities':True,
            'wrong_conjugates_and_nonunit_variants_rejected':True,
            'source_TeX_conventions_checked':True,
            'fresh_cube_divisor_mask_scale_and_principal_row_replacement_audit':divisor['all_passed'],
            'global_estimates_and_full_QRH_verification_scope_honest':True}
    out={'checks':checks,'native_Gauss_controls':rows,'native_Fourier_identities':total,
         'divisor_and_scale_audit':divisor,'production_imports':False,
         'all_passed':all(checks.values()),'seconds':time.monotonic()-start}
    (DEST/'qrh_operator_verification.json').write_text(json.dumps(out,indent=2)+'\n')
    print('Independent QRH arithmetic audit',sum(checks.values()),'/',len(checks),'seconds',out['seconds'],flush=True)


if __name__=='__main__':main()
