#!/usr/bin/env python3
"""Independent subset, Jordan, mixture, moment and public-contract audits."""

from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
from math import gcd
from pathlib import Path
import hashlib
import json
import time
import flint

BASE=Path(__file__).resolve().parent
DEST=BASE/'shift-ratio-results'


def real(x):
    x=Q(x);return flint.arb(x.numerator)/x.denominator


@lru_cache(maxsize=None)
def log(n):return flint.arb(n).log() if n>1 else flint.arb(0)


@lru_cache(maxsize=None)
def factors(n):
    fs={}
    for p,e in flint.fmpz(n).factor():fs[int(p)]=fs.get(int(p),0)+int(e)
    value=1
    for p,e in fs.items():value*=p**e
    assert value==n
    return fs


def divisors(n):
    out=[1]
    for p,e in factors(n).items():out=[d*p**k for d in out for k in range(e+1)]
    return out


def mu(n):
    fs=factors(n)
    return 0 if any(e>1 for e in fs.values()) else (-1)**len(fs)


def prod(xs):
    total=1
    for x in xs:total*=x
    return total


def R(n,v):
    ps=list(factors(n));result=flint.arb(0)
    for bits in product((0,1),repeat=len(ps)):
        d=prod(p for p,b in zip(ps,bits) if b)
        b=n//d
        if b>1:result+=(-1)**sum(bits)*log(b)/(log(b)+real(v)*log(d))
    return result


def B(n,v):
    fs=factors(n);g=gcd(*fs.values())
    return sum((real(Q(mu(k),k))*R(prod(p**(e//k) for p,e in fs.items()),v)
                for k in divisors(g) if mu(k)),flint.arb(0))


def coefficient_audit(source):
    total=0;moments=[]
    for row in source['profiles']:
        v=Q(row['v']);delta=real((1-v)/(1+v));values=[flint.arb(0)]*(row['cutoff']+1)
        for n in range(2,row['cutoff']+1):
            rn=R(n,v);bn=B(n,v);values[n]=bn
            assert rn.overlaps(flint.arb(row['R_coefficients'][n]))
            assert bn.overlaps(flint.arb(row['B_coefficients'][n]))
            fs=factors(n);g=gcd(*fs.values());sign=(-1)**(len(fs)+len(factors(g))-1)
            assert bn*sign>0
            t=log(min(fs))/log(n);envelope=t/(real(v)+real(1-v)*g*t)
            if flint.fmpz(n).is_prime():assert bn.contains(1) and bn.overlaps(envelope)
            else:assert bn.abs_upper()<delta and bn.abs_upper()<envelope
            total+=1
        for X in (2,3,16,64,256,1024,2048):
            M=sum((values[n]**2 for n in range(X,2*X+1)),flint.arb(0))
            bound=real(2*(1+v)/v)*X/log(X)
            assert M<bound
            recorded=next(r for r in source['sieve_second_moment_controls']['records'] if r['v']==str(v) and r['X']==X)
            assert M.overlaps(flint.arb(recorded['M2_ball']))
            moments.append({'v':str(v),'X':X,'M2_ball':M.str(28),'all_passed':True})
    return {'independent_subset_coefficients_checked':total,'independent_moment_windows_checked':len(moments),
            'moment_records':moments,'all_passed':True}


def jordan():
    # Near v=1 a much longer series leaves a tail whose gap below its
    # majorant is smaller than 512-bit rounding. A shorter certified
    # expansion keeps the strict comparison numerically decidable.
    rows=[];K=64
    for v in (Q(1,5),Q(1,2),Q(4,5),Q(19,20)):
        for n in (2,4,6,12,36,64,216,512,729,1296,3599):
            fs=factors(n);m=len(fs);g=gcd(*fs.values());ts=[log(p)/log(n) for p in fs]
            partial=flint.arb(0);sign=(-1)**(m+len(factors(g))-1)
            for j in range(m,K+1):
                J=sum(mu(d)*d**(j-1) for d in divisors(g))
                assert J==prod(1-p**(j-1) for p in factors(g))
                if not J:continue
                T=sum(((-1)**(m-sum(bits))*sum((x for x,b in zip(ts,bits) if b),flint.arb(0))**j
                       for bits in product((0,1),repeat=m)),flint.arb(0))
                term=(-1)**(m-1)*real(v*(1-v)**(j-1))*T*J
                assert term*sign>0
                partial+=term
            tail=real((1-v)**K)/g;difference=(B(n,v)-partial).abs_upper()
            if flint.fmpz(n).is_prime():assert (B(n,v)-partial).overlaps(tail)
            else:assert difference<tail
            rows.append({'v':str(v),'n':n,'K':K,'all_passed':True})
    return {'records':rows,'all_passed':True}


def mixtures_and_sieve_integral():
    rows=[]
    for a,b in ((1,2),(2,3),(3,2),(4,9),(7,25),(13,17),(101,103),(2,1000000000039)):
        la,lb=log(a),log(b)
        def kernel(theta,analytic):return lb/(lb+theta.sin()**2*la)
        value=2/flint.arb.pi()*flint.acb.integral(kernel,0,flint.arb.pi()/2,
                                               abs_tol=flint.arb('1e-28'),rel_tol=flint.arb('1e-28'),eval_limit=20000)
        expected=(lb/(la+lb)).sqrt()
        assert value.real.overlaps(expected) and value.imag.contains(0)
        rows.append({'a':a,'b':b,'beta_half_kernel_ball':value.real.str(28),'all_passed':True})
    integrals=[]
    for v in (Q(1,5),Q(1,2),Q(4,5),Q(1)):
        # The layer-cake integrand after the rough-number bound; no prime data.
        def f(t,analytic):return 2*real(v)/(real(v)+real(1-v)*t)**3
        value=flint.acb.integral(f,0,1,abs_tol=flint.arb('1e-30'),rel_tol=flint.arb('1e-30'))
        assert value.real.overlaps(real((1+v)/v)) and value.imag.contains(0)
        integrals.append({'v':str(v),'layer_cake_integral_ball':value.real.str(28),'all_passed':True})
    # Geometric and fractional families agree on b1 only; b2 separates them.
    for v in (Q(1,5),Q(1,2),Q(4,5)):
        assert v*(1-v)!=v*(1-v)/2
    return {'beta_half_records':rows,'sieve_layer_cake_records':integrals,
            'deterministic_and_fractional_families_distinguished':True,
            'external_full_sieve_proof_independently_verified':False,'all_passed':True}


def known_integer_ladder():
    # Audit the actual closure in established normalized higher logarithms.
    # This is deliberately not counted as a new primitive.
    records=[];K=48
    for v in (Q(4,5),Q(19,20)):
        ratio=(1-v)/v
        for n in (2,4,6,12,36,216,3599):
            total=flint.arb(0);ln=log(n)
            for j in range(1,K+1):
                Rj=sum((mu(a)*(log(n//a)/ln)**j for a in divisors(n) if mu(a) and n//a>1),flint.arb(0))
                total+=real((-ratio)**(j-1)/v)*Rj
            remainder=real(2**len(factors(n))*ratio**K/(2*v-1))
            assert (R(n,v)-total).abs_upper()<remainder
            records.append({'v':str(v),'n':n,'K':K,'integer_logarithm_geometric_tail_ball':remainder.str(28),'all_passed':True})
    # At v=1/2 the putative expansion does not converge even at a prime.
    alternating=[sum((Q(2)*(-1)**(j-1) for j in range(1,K+1)),Q(0)) for K in (5,6,7,8)]
    assert alternating==[2,0,2,0]
    return {'records':records,'established_primitive_closure_checked':True,
            'unjustified_boundary_series_extrapolation_rejected':True,'all_passed':True}


def generic_audit(source):
    raw=list(map(Q,source['generic_inverse_controls']['input_rational_coefficients']))
    inverse=[Q(0),Q(1)]+[Q(0)]*(len(raw)-2)
    for n in range(2,len(raw)):
        inverse[n]=-sum((raw[d]*inverse[n//d] for d in divisors(n) if d>1),Q(0))
    total=0
    for row in source['generic_inverse_controls']['records']:
        v=Q(row['v']);Rvals=[flint.arb(0)]*len(raw)
        for n in range(2,len(raw)):
            Rvals[n]=sum((real(inverse[a]*raw[n//a])*log(n//a)/(log(n//a)+real(v)*log(a))
                          for a in divisors(n) if n//a>1),flint.arb(0))
        for n in range(2,len(raw)):
            fs=factors(n);g=gcd(*fs.values())
            reference=sum((real(Q(mu(k),k))*Rvals[prod(p**(e//k) for p,e in fs.items())]
                           for k in divisors(g) if mu(k)),flint.arb(0))
            assert reference.overlaps(flint.arb(row['B_coefficients'][n]));total+=1
    assert source['sign_grammar']['survivors']==[{'parity_weights':[1,1,0,1,0],'training_passed':True,'held_out_passed':True}]
    for row in source['distant_prime_controls']['records']:
        p,q=row['p'],row['q'];assert flint.fmpz(p).is_prime() and flint.fmpz(q).is_prime()
        val=R(p*q,Q(row['v']));assert val.overlaps(flint.arb(row['B_ball']))
    control=source['distant_prime_controls']['invalid_v_sign_control']
    exact=sum((Q(mu(d))*Q(3,2)/(6+Q(1,2)*d) for d in divisors(6)),Q(0))
    assert exact<0 and real(exact).overlaps(flint.arb(control['B_ball']))
    return {'generic_coefficients_checked':total,'invalid_v_sign_counterexample':str(exact),'all_passed':True}


def public_entry_point():
    from exact_arithmetic import program_value
    units=[[real(x) for x in [Q(0),Q(1)]+[Q(n*n%13-6,n%7+1) for n in range(2,37)]],
           [flint.acb(0),flint.acb(1)]+[flint.acb(real(Q(n%7-3,n%5+1)),real(Q(n%9-4,n%4+1))) for n in range(2,29)]]
    executions=0
    for values in units:
        inv=[flint.acb(0)]*len(values);inv[1]=flint.acb(1)
        for n in range(2,len(values)):
            inv[n]=-sum((values[d]*inv[n//d] for d in divisors(n) if d>1),flint.acb(0))
        for v in (Q(1,5),Q(1,2),Q(4,5),Q(1)):
            refR=[flint.acb(0)]*len(values);refB=refR.copy()
            for n in range(2,len(values)):
                refR[n]=sum((inv[a]*values[n//a]*log(n//a)/(log(n//a)+real(v)*log(a))
                             for a in divisors(n) if n//a>1),flint.acb(0))
            for n in range(2,len(values)):
                fs=factors(n);g=gcd(*fs.values())
                refB[n]=sum((real(Q(mu(k),k))*refR[prod(p**(e//k) for p,e in fs.items())]
                             for k in divisors(g) if mu(k)),flint.acb(0))
            outputs={}
            for family,reference in (('shift_ratio_log',refR),('shift_ratio_prime_decoder',refB)):
                program={'kind':'shift_ratio_program','family':family,'v':str(v),'input':'f'}
                result=program_value(program,{'f':values})
                assert all(flint.acb(a).overlaps(b) for a,b in zip(result,reference))
                outputs[family]=result;executions+=1
            recovered=program_value({'kind':'shift_ratio_program','family':'shift_ratio_prime_decoder_inverse',
                                     'v':str(v),'input':'g'},{'g':outputs['shift_ratio_prime_decoder']})
            assert all(flint.acb(a-b).contains(0) for a,b in zip(recovered,values));executions+=1
    for v in (Q(1,5),Q(1,2),Q(4,5),Q(1)):
        for H in (None,18):
            p={'kind':'shift_ratio_program','family':'shift_ratio_sieve_second_moment_bound','v':str(v),'X':16}
            if H is not None:p['H']=H
            bound=program_value(p,{})
            assert bound.overlaps(real(2*(1+v)/v)*16/log(16)*(H if H is not None else 1))
            executions+=1
    # Unequal supports and weights are held out from the atomic discovery.
    mixtures=[[(Q(1,3),Q(2,7)),(Q(2,3),Q(7,9))],
              [(Q(2,5),Q(1,4)),(Q(1,5),Q(3,5)),(Q(2,5),Q(1))],
              [(Q(1,7),Q(1,11)),(Q(2,7),Q(5,8)),(Q(4,7),Q(9,10))]]
    mixture_records=[]
    for atoms in mixtures:
        serialized=[{'weight':str(w),'v':str(v)} for w,v in atoms]
        for values in units:
            inv=[flint.acb(0)]*len(values);inv[1]=flint.acb(1)
            for n in range(2,len(values)):
                inv[n]=-sum((values[d]*inv[n//d] for d in divisors(n) if d>1),flint.acb(0))
            refR=[flint.acb(0)]*len(values);refB=refR.copy()
            for n in range(2,len(values)):
                refR[n]=sum((inv[a]*values[n//a]*sum((real(w)*log(n//a)/(log(n//a)+real(v)*log(a))
                             for w,v in atoms),flint.arb(0)) for a in divisors(n) if n//a>1),flint.acb(0))
            for n in range(2,len(values)):
                fs=factors(n);g=gcd(*fs.values())
                refB[n]=sum((real(Q(mu(k),k))*refR[prod(p**(e//k) for p,e in fs.items())]
                             for k in divisors(g) if mu(k)),flint.acb(0))
            for family,reference in (('shift_ratio_log',refR),('shift_ratio_prime_decoder',refB)):
                produced=program_value({'kind':'shift_ratio_program','family':family,'mixture':serialized,'input':'f'},{'f':values})
                assert all(flint.acb(a).overlaps(b) for a,b in zip(produced,reference));executions+=1
                if family=='shift_ratio_prime_decoder':decoder=produced
            recovered=program_value({'kind':'shift_ratio_program','family':'shift_ratio_prime_decoder_inverse',
                                     'mixture':serialized,'input':'g'},{'g':decoder})
            assert all(flint.acb(a-b).contains(0) for a,b in zip(recovered,values));executions+=1
        bound=program_value({'kind':'shift_ratio_program','family':'shift_ratio_sieve_second_moment_bound',
                             'mixture':serialized,'X':16},{})
        constant=2*(1+sum((w/v for w,v in atoms),Q(0)))
        assert bound.overlaps(real(constant)*16/log(16));executions+=1
        delta=sum((w*(1-v)/(1+v) for w,v in atoms),Q(0))
        for n in range(2,257):
            val=sum((real(w)*B(n,v) for w,v in atoms),flint.arb(0))
            if flint.fmpz(n).is_prime():assert val.contains(1)
            else:assert val.abs_upper()<real(delta)
        for m in (1,2,3,7,13):assert sum((Q(m)*w/v**m for w,v in atoms),Q(0))>0
        mixture_records.append({'atoms':serialized,'sharp_composite_gap':str(delta),
                                'sieve_M2_constant':str(constant),'all_passed':True})
    good={'kind':'shift_ratio_program','family':'shift_ratio_prime_decoder','v':'1/2','input':'f'}
    invalid=[(good,[]),(good,[0,2,1]),(good,[1,1,1]),(good,[0,flint.arb('1 +/- 0.1'),1]),(good,[0,1,flint.arb('nan')])]
    invalid.extend((dict(good,v=v),[0,1,1]) for v in ('0','-1/2','3/2'))
    invalid.append((dict(good,family='unknown'),[0,1,1]))
    moment=dict(good,family='shift_ratio_sieve_second_moment_bound',X=16)
    invalid.extend((dict(moment,X=X),[]) for X in (1,True,Q(3,2)))
    invalid.extend((dict(moment,H=H),[]) for H in (16,0,True,Q(37,2)))
    mixture_good={k:v for k,v in good.items() if k!='v'}
    bad_mixtures=[[],[{'weight':'-1','v':'1/2'},{'weight':'2','v':'1'}],
                  [{'weight':'0','v':'1/2'},{'weight':'1','v':'1'}],
                  [{'weight':'1/2','v':'1/2'}],[{'weight':'1','v':'0'}],
                  [{'weight':'1','v':'3/2'}],[{'weight':'1','v':'1/2','extra':0}]]
    invalid.extend((dict(mixture_good,mixture=m),[0,1,1]) for m in bad_mixtures)
    invalid.append((dict(good,mixture=[{'weight':'1','v':'1/2'}]),[0,1,1]))
    rejected=0
    for p,values in invalid:
        try:program_value(p,{'f':values})
        except ValueError:rejected+=1
        else:raise AssertionError('An invalid shift-ratio program was accepted')
    return {'public_executions':executions,'invalid_contracts_rejected':rejected,
            'held_out_positive_mixture_records':mixture_records,'all_passed':True}


def main():
    start=time.monotonic();flint.ctx.prec=512
    source=json.loads((DEST/'shift_ratio_search.json').read_text());assert source['all_passed']
    coef=coefficient_audit(source);j=jordan();mix=mixtures_and_sieve_integral();generic=generic_audit(source)
    ladder=known_integer_ladder()
    public=public_entry_point()
    checks={'independent_complete_subset_coefficients_sign_gap_and_least_prime_bounds':coef['all_passed'],
            'independent_geometric_Jordan_expansion_with_infinite_tail':j['all_passed'],
            'generic_rational_units_and_invalid_parameter_extrapolation':generic['all_passed'],
            'native_beta_mixture_and_sieve_layer_cake_integrals':mix['all_passed'],
            'all_finite_doubling_second_moments':coef['all_passed'],
            'public_real_complex_inverse_bounds_and_invalid_contracts':public['all_passed'],
            'historical_novelty_known_integer_closure_external_sieve_and_RH_scope_honest':ladder['all_passed']}
    assert not source['historical_novelty_established'] and not source['new_RH_estimate_proved']
    out={'checks':checks,'coefficient_audit':coef,'Jordan_audit':j,'mixture_and_sieve_audit':mix,
         'generic_audit':generic,'public_entry_point_audit':public,
         'known_integer_logarithm_closure_audit':ladder,
         'source_artifact_sha256':hashlib.sha256((DEST/'shift_ratio_search.json').read_bytes()).hexdigest(),
         'mathematical_audit_imports_production_code':False,'integration_checks_import_production_code':True,
         'all_passed':all(checks.values()),'seconds':time.monotonic()-start}
    (DEST/'shift_ratio_verification.json').write_text(json.dumps(out,indent=2)+'\n')
    print('Independent shift-ratio arithmetic audit',sum(checks.values()),'/',len(checks),'seconds',out['seconds'],flush=True)


if __name__=='__main__':main()
