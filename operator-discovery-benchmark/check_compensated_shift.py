#!/usr/bin/env python3
"""Independent signed coefficient, symbolic, inverse and public-contract audits."""
from fractions import Fraction as Q
from itertools import product
from math import gcd
from pathlib import Path
import hashlib
import json
import time
import flint
import sympy as sp

# Reuse only a previously independent subset backend; never production math.
from check_shift_ratio import B, R, factors, divisors, mu, log, real

BASE=Path(__file__).resolve().parent
DEST=BASE/'compensated-shift-results'


def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()


def weights(u,v):
    a,b=1/u-u,1/v-v
    return ((-b/(a-b),u),(a/(a-b),v))


def value(n,A): return sum((real(w)*B(n,v) for w,v in A),flint.arb(0))


def rational_factors(q):
    result={}
    for p,e in factors(q.numerator).items(): result[p]=e
    for p,e in factors(q.denominator).items(): result[p]=result.get(p,0)-e
    return {p:e for p,e in result.items() if e}


def canceled_order(u,v):
    base,target=rational_factors(v/u),rational_factors((1/u-u)/(1/v-v))
    if any(p not in base for p in target): return None
    ratios={Q(target.get(p,0),e) for p,e in base.items()}
    if len(ratios)!=1: return None
    order=next(iter(ratios))
    return int(order) if order.denominator==1 and order>=1 else None


def coefficient_audit(source):
    shifts=[Q(r['v']) for r in source['atomic_pair_models']]; N=source['coefficient_cutoff']
    atomic={v:[flint.arb(0),flint.arb(0)]+[B(n,v) for n in range(2,N+1)] for v in shifts}
    checked=0
    for row in source['pair_compensators']:
        u,v=Q(row['left']),Q(row['right']); A=weights(u,v)
        assert tuple(str(w) for w,a in A)==tuple(row['learned_weights'])
        coarse=max(abs(w)*(1-a)/(1+a) for w,a in A)
        assert str(coarse)==row['certificate']['universal_composite_upper']
        for n in range(2,N+1):
            b=sum((real(w)*atomic[a][n] for w,a in A),flint.arb(0))
            if flint.fmpz(n).is_prime(): assert b.contains(1)
            else:
                assert b.abs_upper()<real(coarse)
                signs=[(-1)**(len(factors(n))+len(factors(gcd(*factors(n).values())))-1)*atomic[a][n] for w,a in A]
                assert all(x>0 for x in signs)
            if 'B_coefficients' in row: assert b.overlaps(flint.arb(row['B_coefficients'][n]))
            checked+=1
    return {'independent_full_prefix_coefficients_checked':checked,'atomic_profiles':len(atomic),'cutoff':N,'all_passed':True}


def symbolic_audit(source):
    t,u,v=sp.symbols('t u v',positive=True)
    def hv(x,a): return x/(a+(1-a)*x)
    atomic=sp.factor(1-hv(t,v)-hv(1-t,v)); z=t*(1-t)
    a=lambda q:1/q-q
    b=lambda q:q+1/q-2
    assert sp.cancel(atomic+a(v)*z/(1+b(v)*z))==0
    wu,wv=-a(v)/(a(u)-a(v)),a(u)/(a(u)-a(v))
    signed=wu*(1-hv(t,u)-hv(1-t,u))+wv*atomic
    K=a(u)*a(v)*(b(u)-b(v))/(a(u)-a(v))
    assert sp.cancel(signed+K*z*z/((1+b(u)*z)*(1+b(v)*z)))==0
    assert sp.cancel(wu+wv-1)==0 and sp.cancel(wu*a(u)+wv*a(v))==0
    for row in source['atomic_pair_models']:
        q=Q(row['v']); first=1/q-q; second=q+1/q-2
        assert Q(row['learned_reciprocal_affine_intercept'])==1/first
        assert Q(row['learned_reciprocal_affine_slope'])==second/first
        assert Q(row['inferred_unbalanced_pair_first_order'])==first
    fit=source['first_order_feature_search']
    for row in source['atomic_pair_models']:
        q=Q(row['v']); assert sum((Q(c)*q**j for j,c in zip(fit['basis_exponents'],fit['learned_coefficients'])),Q(0))==1/q-q
    return {'generic_rational_identities_checked':4,'affine_pair_models_checked':len(source['atomic_pair_models']),
            'parameter_feature_formula_proved_by_exact_identity':True,'all_passed':True}


def zero_order_audit(source):
    rows=[]
    for row in source['pair_compensators']:
        u,v=Q(row['left']),Q(row['right']); order=canceled_order(u,v)
        cert=row['certificate']['root_signature_certificate']
        assert cert['zero_leading_signature_orders']==([] if order is None else [order])
        assert cert['nonzero_leading_signature_every_positive_integer_order_proved']==(order is None)
        assert not cert['finite_order_testing_substituted_for_all_order_proof']
        assert not cert['zero_leading_coefficient_means_whole_branch_erased_claimed']
        if order is not None: assert sum(w/a**order for w,a in weights(u,v))==0
        rows.append({'left':str(u),'right':str(v),'possible_canceled_leading_order':order,'all_integer_orders_decided_by_valuations':True})
    assert sum(r['possible_canceled_leading_order'] is not None for r in rows)==1
    return {'records':rows,'finite_order_samples_substituted_for_proof':False,'all_passed':True}


def forward(values,A):
    N=len(values)-1; inverse=[flint.acb(0)]*(N+1); inverse[1]=flint.acb(1)
    result=[flint.acb(0)]*(N+1)
    for n in range(2,N+1):
        ds=divisors(n)
        inverse[n]=-sum((flint.acb(values[d])*inverse[n//d] for d in ds if d>1),flint.acb(0))
        result[n]=sum((inverse[d]*values[n//d]*sum((real(w)*log(n//d)/(log(n//d)+real(v)*log(d)) for w,v in A),flint.arb(0))
                       for d in ds if n//d>1),flint.acb(0))
    return result


def strip(values):
    out=[flint.acb(0)]*len(values)
    for n in range(2,len(values)):
        fs=factors(n); g=gcd(*fs.values())
        for k in divisors(g):
            root=1
            for p,e in fs.items(): root*=p**(e//k)
            out[n]+=real(Q(mu(k),k))*values[root]
    return out


def generic_audit(source):
    raw=[real(Q(x)) for x in source['generic_inverse_controls']['rational_input']]; total=0
    for row in source['generic_inverse_controls']['records']:
        A=weights(Q(row['left']),Q(row['right'])); expected=strip(forward(raw,A))
        for a,b in zip(expected,row['decoder_coefficients']): assert a.overlaps(flint.acb(flint.arb(b))); total+=1
    return {'generic_nonmultiplicative_coefficients_checked':total,'all_passed':True}


def false_controls(source):
    A=weights(Q(1,3),Q(2,3)); selected=source['selected_operator']; n=selected['incorrect_universal_square_envelope_first_counterexample']
    K=Q(selected['certificate']['two_prime_least_prime_square_envelope_constant'])
    p=min(factors(n)); assert value(n,A).abs_lower()>real(K)*(log(p)/log(n))*(log(p)/log(n))
    control=source['large_actual_prime_three_factor_control']; p,q=control['p'],control['q']
    assert flint.fmpz(p).is_prime() and flint.fmpz(q).is_prime() and p!=q
    # Sparse actual-prime control, not a complete-prefix claim.
    primes=[2,p,q]; ln=sum((log(a) for a in primes),flint.arb(0)); actual=flint.arb(0)
    for bits in product((0,1),repeat=3):
        t=1-sum((log(p) for p,b in zip(primes,bits) if b),flint.arb(0))/ln
        actual+=(-1)**sum(bits)*sum((real(w)*t/(real(v)+real(1-v)*t) for w,v in A),flint.arb(0))
    ratio=log(2)/ln
    assert actual.overlaps(flint.arb(control['complete_one_coefficient_ball']))
    assert actual.abs_lower()>real(K)*ratio*ratio
    t=sp.Symbol('t'); h=sum(sp.Rational(w.numerator,w.denominator)*t/(sp.Rational(v.numerator,v.denominator)+(1-sp.Rational(v.numerator,v.denominator))*t) for w,v in A)
    hp=sp.diff(h,t); D=sp.simplify(hp.subs(t,0)+hp.subs(t,1)-2*hp.subs(t,sp.Rational(1,2)))
    assert D==sp.Rational(control['triple_linear_asymptotic_coefficient']) and D!=0
    assert not control['full_prefix_at_large_index_claimed']
    return {'first_false_global_square_envelope_counterexample':n,'actual_large_prime_triple':[2,p,q],
            'nonzero_triple_linear_asymptotic_coefficient':str(D),'all_passed':True}


def public_audit():
    from compensated_operator import program_value
    from shift_ratio_grammar import mixture_parameters
    counts=0
    inputs=[[flint.acb(0),flint.acb(1)]+[flint.acb(real(Q(n%11-5,n%7+1)),real(Q(n%9-4,n%5+1))) for n in range(2,37)],
            [real(x) for x in [Q(0),Q(1)]+[Q(n*n%17-8,n%9+1) for n in range(2,43)]]]
    for values in inputs:
        for u,v in ((Q(1,3),Q(2,3)),(Q(1,5),Q(4,5)),(Q(3,7),Q(5,7))):
            p={'kind':'compensated_shift_program','left':str(u),'right':str(v),'input':'f'}
            rr=forward(values,weights(u,v)); bb=strip(rr)
            for family,reference in [('compensated_arithmetic_log',rr),('compensated_prime_decoder',bb)]:
                actual=program_value({**p,'family':family},{'f':values}); counts+=1
                assert all(flint.acb(a).overlaps(b) for a,b in zip(actual,reference))
            recovered=program_value({**p,'family':'compensated_decoder_inverse'},{'f':bb}); counts+=1
            assert all(flint.acb(a).overlaps(b) for a,b in zip(recovered,values))
    cert={'kind':'compensated_shift_program','left':'1/3','right':'2/3','family':'certified_global_composite_gap'}
    assert program_value(cert,{})==Q(7,110); counts+=1
    separation=program_value({**cert,'family':'certified_global_prime_separation_certificate'},{}); counts+=1
    assert separation['prime_coefficient']==1 and separation['composite_absolute_bound']==Q(7,110)
    bad=[]
    p={**cert,'family':'compensated_prime_decoder','input':'f'}
    for u,v in [('0','2/3'),('1/3','1'),('2/3','1/3'),('1/3','1/3'),('-1/3','2/3')]: bad.append(({**p,'left':u,'right':v},{'f':inputs[0]}))
    bad.extend([({**p,'kind':'other'},{'f':inputs[0]}),({**p,'family':'other'},{'f':inputs[0]}),
                ({**cert,'left':'1/5'},{}),
                (p,{'f':[real(0),flint.arb(1,real(Q(1,10)))]+inputs[0][2:]}),
                (p,{'f':[real(1),real(1)]+inputs[0][2:]}),
                (p,{'f':[real(0),real(1),flint.arb('nan')]}),
                ({**p,'family':'compensated_decoder_inverse'},{'f':inputs[0]})])
    for program,values in bad:
        try: program_value(program,values)
        except ValueError: pass
        else: raise AssertionError('invalid contract accepted')
    try: mixture_parameters([{'weight':Q(-5,11),'v':Q(1,3)},{'weight':Q(16,11),'v':Q(2,3)}])
    except ValueError: pass
    else: raise AssertionError('positive-mixture sort accepted signed weights')
    return {'public_executions':counts,'invalid_contracts_rejected':len(bad)+1,
            'old_positive_sort_preserved':True,'all_passed':True}


def main():
    started=time.monotonic(); flint.ctx.prec=512
    path=DEST/'compensated_shift_search.json'; source=json.loads(path.read_text())
    for key,name in [('producer_code_sha256','compensated_shift_search.py'),('grammar_code_sha256','compensated_shift_grammar.py'),('proof_sha256','compensated_shift_proof.txt')]:
        assert source[key]==sha(BASE/name)
    cofs=coefficient_audit(source); symbols=symbolic_audit(source); signatures=zero_order_audit(source)
    generic=generic_audit(source); controls=false_controls(source); public=public_audit()
    gap_path=DEST/'gap-certificates/global_gap_verification.json'; gap=json.loads(gap_path.read_text())
    assert gap['all_passed'] and gap['source_arithmetic_sha256']==sha(path)
    assert gap['checker_code_sha256']==sha(BASE/'check_compensated_global_gap.py')
    assert gap['proof_sha256']==sha(BASE/'compensated_global_gap_proof.txt')
    assert not source['historical_novelty_established'] and not source['new_RH_estimate_proved']
    assert source['verified_new_operators']==[] and not source['coefficient_operator_uses_prime_or_factor_oracle']
    checks={'independent_complete_signed_prefix_and_shared_atomic_signs':cofs['all_passed'],
            'learned_pair_feature_and_signed_cancellation_exact_rational_identities':symbols['all_passed'],
            'all_integer_zero_orders_by_independent_valuation_test':signatures['all_passed'],
            'generic_nonmultiplicative_input_coefficients_and_inverses':generic['all_passed'],
            'false_global_square_envelopes_and_actual_large_prime_control':controls['all_passed'],
            'standalone_public_programs_and_invalid_contracts':public['all_passed'],
            'independently_verified_sharp_global_composite_gap':gap['all_passed'],
            'coefficient_oracle_analytic_estimate_and_historical_scope':True}
    out={'all_passed':all(checks.values()),'checks':checks,'coefficient_audit':cofs,'symbolic_audit':symbols,
         'all_order_signature_audit':signatures,'generic_input_audit':generic,'false_bound_controls':controls,
         'public_entry_point_audit':public,'global_gap_verification_sha256':sha(gap_path),
         'source_artifact_sha256':sha(path),'checker_code_sha256':sha(Path(__file__)),
         'independent_subset_backend_code_sha256':sha(BASE/'check_shift_ratio.py'),
         'public_entry_code_sha256':sha(BASE/'compensated_operator.py'),
         'mathematical_audit_imports_production_code':False,'public_integration_audit_imports_production_code':True,
         'universal_composite_bound_proved':'7/110','historical_novelty_established':False,'verified_new_operators':[],
         'seconds':time.monotonic()-started}
    (DEST/'compensated_shift_verification.json').write_text(json.dumps(out,indent=2)+'\n')
    print('Signed arithmetic audit',len(checks),'/',len(checks),'coefficients',cofs['independent_full_prefix_coefficients_checked'],'seconds',out['seconds'],flush=True)


if __name__=='__main__': main()
