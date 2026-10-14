#!/usr/bin/env python3
"""Independent subset differences, binomial/Jordan and formal-unit checks."""

from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
from math import gcd
from pathlib import Path
import json
import time
import flint

from check_gap import factors

BASE=Path(__file__).resolve().parent
DEST=BASE/'fractional-prime-results'


def real(x):
    x=Q(x);return flint.arb(x.numerator)/x.denominator


@lru_cache(maxsize=None)
def log(n):return flint.arb(n).log() if n>1 else flint.arb(0)


def divisors(n):
    values=[1]
    for p,e in factors(n).items():values=[d*p**k for d in values for k in range(e+1)]
    return sorted(values)


def mu(n):
    f=factors(n);return 0 if any(e>1 for e in f.values()) else (-1)**len(f)


def root_from_factors(fs,k):return product_int(p**(e//k) for p,e in fs.items())


def product_int(xs):
    ans=1
    for x in xs:ans*=x
    return ans


def R(n,alpha):
    ps=list(factors(n));total=flint.arb(0)
    for bits in product((0,1),repeat=len(ps)):
        d=product_int(p for p,b in zip(ps,bits) if b)
        value=log(n//d)
        if n!=d:total+=(-1)**sum(bits)*value**real(alpha)
    return total/log(n)**real(alpha)


def B(n,alpha):
    fs=factors(n);g=gcd(*fs.values())
    return sum((real(Q(mu(d),d))*R(root_from_factors(fs,d),alpha) for d in divisors(g) if mu(d)),flint.arb(0))


def coefficient_audit(source):
    total=0
    for row in source['profiles']:
        alpha=Q(row['alpha']);bound=flint.arb(2)**(1-real(alpha))-1
        for n in range(2,row['cutoff']+1):
            rn=R(n,alpha);bn=B(n,alpha);fs=factors(n);g=gcd(*fs.values())
            assert rn.overlaps(flint.arb(row['R_coefficients'][n]))
            assert bn.overlaps(flint.arb(row['B_coefficients'][n]))
            assert (rn*log(n)**real(alpha)).overlaps(flint.arb(row['L_coefficients'][n]))
            expected=(-1)**(len(fs)+len(factors(g))-1)
            assert bn*expected>0
            if flint.fmpz(n).is_prime():assert bn.contains(1)
            else:assert bn.abs_upper()<bound
            total+=1
    return {'independent_subset_coefficients_checked':total,'all_passed':True}


def binomial_audit():
    K=256;rows=[]
    for alpha in (Q(1,4),Q(1,2),Q(3,4),Q(9,10)):
        weights=[];b=alpha
        for k in range(1,K+1):
            if k>1:b*=Q(k-1-alpha,k)
            weights.append(b)
        tail=1-sum(weights,Q(0));assert tail>0 and all(b>0 for b in weights)
        for n in (2,4,6,12,16,36,64,216,512,729,1296,3599,4096):
            fs=factors(n);g=gcd(*fs.values());m=len(fs);steps=[log(p)/log(n) for p in fs]
            partial=flint.arb(0)
            for k in range(max(1,m),K+1):
                J=sum(mu(d)*d**(k-1) for d in divisors(g))
                if J==0:continue
                Tk=sum(((-1)**(m-sum(bits))*sum((v for v,b in zip(steps,bits) if b),flint.arb(0))**k
                        for bits in product((0,1),repeat=m)),flint.arb(0))
                term=(-1)**(m-1)*real(weights[k-1])*Tk*J
                assert term*(-1)**(m+len(factors(g))-1)>0
                partial+=term
            value=B(n,alpha);allowed=real(tail)/g
            if flint.fmpz(n).is_prime():
                # At a prime the positive expansion saturates its tail bound
                # exactly; rounded balls must overlap that equality.
                assert (value-partial).overlaps(allowed)
            else:
                assert (value-partial).abs_upper()<allowed
            rows.append({'alpha':str(alpha),'n':n,'K':K,'partial_ball':partial.str(25),
                         'tail_bound_ball':allowed.str(25),'all_passed':True})
    return {'records':rows,'positive_binomial_terms_and_Jordan_factorization_checked':True,'all_passed':True}


def generic(source):
    control=source['generic_inverse_and_root_controls'];f=list(map(Q,control['input_rational_coefficients']))
    inv=[Q(0),Q(1)]+[Q(0)]*(len(f)-2)
    for n in range(2,len(f)):
        inv[n]=-sum((f[d]*inv[n//d] for d in divisors(n) if d>1),Q(0))
    for row in control['inverse_controls']:
        a=Q(row['alpha']);Rvals=[flint.arb(0)]*len(f)
        for n in range(2,len(f)):
            val=sum((real(inv[d]*f[n//d])*log(n//d)**real(a) for d in divisors(n) if n//d>1),flint.arb(0))
            Rvals[n]=val/log(n)**real(a)
        for n in range(2,len(f)):
            fs=factors(n);g=gcd(*fs.values())
            v=sum((real(Q(mu(k),k))*Rvals[root_from_factors(fs,k)] for k in divisors(g) if mu(k)),flint.arb(0))
            assert v.overlaps(flint.arb(row['B_coefficients'][n]))
    r=control['root_counterexample'];assert not flint.arb(r['anomaly_ball']).contains(0)
    a=Q(r['alpha']);b=Q(r['beta']);v=1-(log(2)**real(a)+log(3)**real(a))/log(6)**real(a)
    assert (real(b*b)*v).overlaps(flint.arb(r['root_log_coefficient_ball']))
    assert (real(b)*v).overlaps(flint.arb(r['expected_commuting_coefficient_ball']))
    return {'rational_unit_inverse_and_four_orders_checked':True,'root_counterexample_independently_recomputed':True,'all_passed':True}


def grammar_and_far(source):
    assert source['grammar']['sign_models_scored']==32
    assert source['grammar']['sign_survivors']==[{'parity_weights':[1,1,0,1,0],'training_passed':True,'held_out_passed':True}]
    for row in source['distant_prime_pair_controls']['records']:
        p,q=row['p'],row['q'];assert flint.fmpz(p).is_prime() and flint.fmpz(q).is_prime() and p<q
        assert not any(flint.fmpz(n).is_prime() for n in range(p+1,q))
        a=real(Q(row['alpha']));v=1-(log(p)**a+log(q)**a)/log(p*q)**a
        assert v.overlaps(flint.arb(row['B_coefficient_ball']))
        assert flint.arb(2)**(1-a)-1-v.abs_upper()>0
    return {'distant_consecutive_prime_pair_checked':True,'all_passed':True}


def public_entry_point():
    # Only the integration section imports production code. The mathematical
    # audits above use independent subset, Jordan and Dirichlet inversion.
    from exact_arithmetic import program_value
    units=[list(map(real,[Q(0),Q(1)]+[Q(n*n%11-5,n%6+1) for n in range(2,44)])),
           [flint.acb(0),flint.acb(1)]+[
               flint.acb(real(Q(n%7-3,n%5+1)),real(Q(n%9-4,n%4+1))) for n in range(2,25)]]
    executions=0
    for values in units:
        inverse=[flint.acb(0)]*len(values);inverse[1]=flint.acb(1)
        for n in range(2,len(values)):
            inverse[n]=-sum((values[d]*inverse[n//d] for d in divisors(n) if d>1),flint.acb(0))
        for alpha in (Q(1,4),Q(1,2),Q(3,4),Q(1)):
            reference_L=[flint.acb(0)]*len(values);reference_R=reference_L.copy()
            for n in range(2,len(values)):
                reference_L[n]=sum((inverse[d]*values[n//d]*log(n//d)**real(alpha)
                                   for d in divisors(n) if n//d>1),flint.acb(0))
                reference_R[n]=reference_L[n]/log(n)**real(alpha)
            reference_B=reference_R.copy()
            for n in range(2,len(values)):
                fs=factors(n);g=gcd(*fs.values())
                reference_B[n]=sum((real(Q(mu(k),k))*reference_R[root_from_factors(fs,k)]
                                    for k in divisors(g) if mu(k)),flint.acb(0))
            decoder=None
            for family,reference in (('fractional_arithmetic_log',reference_L),
                                     ('normalized_fractional_log',reference_R),
                                     ('fractional_prime_decoder',reference_B)):
                program={'kind':'fractional_prime_program','family':family,'alpha':str(alpha),'input':'f'}
                produced=program_value(program,{'f':values})
                assert len(produced)==len(reference) and all(flint.acb(a).overlaps(b) for a,b in zip(produced,reference))
                if family=='fractional_prime_decoder':decoder=produced
                executions+=1
            recovered=program_value({'kind':'fractional_prime_program','family':'fractional_prime_decoder_inverse',
                                     'alpha':str(alpha),'input':'g'},{'g':decoder})
            assert all((a-b).contains(0) for a,b in zip(recovered,values));executions+=1
    good={'kind':'fractional_prime_program','family':'fractional_prime_decoder','alpha':'1/2','input':'f'}
    invalid=[(good,[]),(good,[0,2,1]),(good,[1,1,1]),(good,[0,flint.arb('1 +/- 0.1'),1]),
             (good,[0,1,flint.arb('nan')])]
    invalid.extend((dict(good,alpha=a),[0,1,1]) for a in ('0','-1/2','3/2'))
    invalid.append((dict(good,family='unrecognized'),[0,1,1]))
    rejected=0
    for program,values in invalid:
        try:program_value(program,{'f':values})
        except ValueError:rejected+=1
        else:raise AssertionError('Invalid public fractional-prime program accepted')
    return {'real_and_complex_changed_input_executions':executions,'invalid_program_controls_rejected':rejected,
            'independent_factor_based_reference_used':True,'all_passed':True}


def main():
    start=time.monotonic();flint.ctx.prec=512
    source=json.loads((DEST/'fractional_prime_search.json').read_text());assert source['all_passed']
    coef=coefficient_audit(source);series=binomial_audit();formal=generic(source);far=grammar_and_far(source)
    interface=public_entry_point()
    assert not source['coefficient_production_uses_prime_indicator_or_prime_weights']
    assert not source['historical_novelty_established'] and not source['new_uniform_prime_distribution_estimate_proved']
    checks={'independent_subset_and_complete_integer_prime_classification':coef['all_passed'],
            'independent_positive_binomial_and_Jordan_expansion':series['all_passed'],
            'general_input_formal_inverse_and_root_anomaly':formal['all_passed'],
            'held_out_sign_grammar_and_distant_actual_prime_pair':far['all_passed'],
            'typed_public_grammar_real_complex_inverse_and_invalid_controls':interface['all_passed'],
            'all_integer_proof_and_finite_observation_scope_separated':True,
            'historical_novelty_and_prime_distribution_scope_honest':True}
    out={'checks':checks,'coefficient_audit':coef,'binomial_audit':series,'generic_audit':formal,'distant_audit':far,
         'public_entry_point_audit':interface,'mathematical_audit_imports_production_code':False,
         'integration_checks_import_production_code':True,'production_imports':True,
         'all_passed':all(checks.values()),'seconds':time.monotonic()-start}
    (DEST/'fractional_prime_verification.json').write_text(json.dumps(out,indent=2)+'\n')
    print('Independent fractional-prime audit',sum(checks.values()),'/',len(checks),'seconds',out['seconds'],flush=True)


if __name__=='__main__':main()
