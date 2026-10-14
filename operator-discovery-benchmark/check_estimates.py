#!/usr/bin/env python3
"""Independent factorizations, exact certificate replay and native integrals.

Mathematical checks import no production code. The final interface audit
deliberately calls the public dispatcher to test the actual entry point.
"""

from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
from math import comb, gcd
from pathlib import Path
import hashlib
import json
import time
import flint
import sympy as sp

BASE = Path(__file__).resolve().parent
DEST = BASE/'estimate-results'


def real(x):
    x = Q(x)
    return flint.arb(x.numerator)/x.denominator


@lru_cache(maxsize=None)
def factors(n):
    fs = {}
    for p,e in flint.fmpz(n).factor():
        p,e = int(p),int(e)
        assert flint.fmpz(p).is_prime()
        fs[p] = fs.get(p,0)+e
    assert product_int(p**e for p,e in fs.items()) == n
    return fs


def product_int(xs):
    out = 1
    for x in xs:
        out *= x
    return out


def integer_power_ball(x, exponent):
    # arb's general real-power route rejects zero-crossing intervals even
    # at integer exponents. Polynomial multiplication has the right domain.
    result = flint.arb(1)
    for _ in range(exponent):
        result *= x
    return result


def mu(n):
    fs = factors(n)
    return 0 if any(e>1 for e in fs.values()) else (-1)**len(fs)


def evaluate_expression(expr, symbol=None, value=None):
    if expr==symbol:
        return value
    if expr.is_Rational:
        return real(Q(int(expr.p),int(expr.q)))
    if expr.func==sp.Add:
        return sum((evaluate_expression(a,symbol,value) for a in expr.args),flint.arb(0))
    if expr.func==sp.Mul:
        out = flint.arb(1)
        for a in expr.args:
            out *= evaluate_expression(a,symbol,value)
        return out
    if expr.func==sp.Pow and expr.args[1].is_Integer:
        return evaluate_expression(expr.args[0],symbol,value)**int(expr.args[1])
    if expr.func==sp.Pow and expr.args[1].is_Rational:
        base = evaluate_expression(expr.args[0],symbol,value)
        if not base>0:
            raise AssertionError('A rational real power needs a positive base')
        return (base.log()*evaluate_expression(expr.args[1],symbol,value)).exp()
    if expr.func==sp.log:
        return evaluate_expression(expr.args[0],symbol,value).log()
    raise AssertionError('Uncertified expression type: '+str(expr))


def arithmetic_and_fit_audit(source):
    N = source['coefficient_cutoff']
    values = [0]+[mu(n) for n in range(1,N+1)]
    assert hashlib.sha256(bytes(a+1 for a in values)).hexdigest()==source['inverse_coefficients_sha256']
    d = source['cancellation_estimate_search']
    scales = d['training_scales']+d['held_out_scales']
    # Compute each observation from fresh independent factorization moments,
    # instead of the production's incremental running-moment implementation.
    sums = {X:[sum(values[n]*n**j for n in range(1,X+1)) for j in range(5)] for X in scales}
    observations = {}
    s = sp.Symbol('s')
    mellin_count = 0
    for row in d['records']:
        c = list(map(Q,row['kernel']))
        assert c[0]==1 and sum(c)==0
        for observation in row['observations']:
            X = observation['X']
            expected = sum((a*Q(sums[X][j],X**j) for j,a in enumerate(c)),Q(0))
            assert expected==Q(observation['exact_smoothed_sum'])
            observations[row['id'],X] = expected
        transform = sum(sp.Rational(a.numerator,a.denominator)/(s+j) for j,a in enumerate(c))
        cert = row['Mellin_certificate']
        assert sp.cancel(transform-sp.sympify(cert['transform']))==0
        num,den = sp.fraction(sp.cancel(transform))
        assert list(map(str,sp.Poly(num,s).all_coeffs()))==cert['numerator_coefficients_descending']
        assert list(map(str,sp.Poly(den,s).all_coeffs()))==cert['denominator_coefficients_descending']
        # Independent Routh array checks the sufficient Hurwitz gate.
        a = sp.Poly(num,s).all_coeffs()
        if a[0]<0:
            a = [-x for x in a]
        degree = len(a)-1
        if degree==0:
            stable = True
        else:
            width = (degree+2)//2
            routh = [a[0::2]+[0]*width,a[1::2]+[0]*width]
            routh = [r[:width] for r in routh]
            stable = all(x>0 for x in a)
            for j in range(2,degree+1):
                pivot = routh[-1][0]
                if pivot==0:
                    stable = False
                    break
                row_r = [(routh[-1][0]*routh[-2][k+1]-routh[-2][0]*routh[-1][k+1])/pivot
                         for k in range(width-1)]+[0]
                routh.append(row_r)
            stable = stable and len(routh)==degree+1 and all(r[0]>0 for r in routh)
        assert bool(stable)==cert['nonvanishing_Re_s_ge_zero_certified']
        weak = row['available_weak_all_scale_certificate']
        degree = len(c)-1
        bern = [sum((c[j]*Q(comb(k,j),comb(degree,j)) for j in range(k+1)),Q(0))
                for k in range(degree+1)]
        assert list(map(str,bern))==weak['Bernstein_coefficients']
        assert max(map(abs,bern))==Q(weak['constant'])
        mellin_count += 1
    failed = survived_impossible = 0
    for row in d['candidate_estimates']:
        theta,b,C = Q(row['theta']),int(row['log_power']),Q(row['constant'])
        def norm(X):
            return real(X)**real(theta)*real(X).log()**b
        ratios = [real(abs(observations[row['kernel_id'],X]))/norm(X)*real(Q(5,4))
                  for X in d['training_scales']]
        assert all(r<=real(C) for r in ratios)
        # At an exact dyadic boundary a native logarithmic power may still
        # have a tiny outward radius. Certified upper rounding can retain
        # one extra quantum; neither equality nor an overlap proves >.
        assert any(r>real(C-Q(2,1024)) for r in ratios)
        failures = [X for X in d['held_out_scales'] if not real(abs(observations[row['kernel_id'],X]))<=real(C)*norm(X)]
        assert failures==row['held_out_failure_scales']
        assert bool(not failures)==row['held_out_passed']
        failed += bool(failures)
        expected_obstruction = theta<Q(1,2) or (theta==Q(1,2) and b<0)
        assert row['post_fit_known_zero_obstruction']==expected_obstruction
        if expected_obstruction:
            assert row['status']=='ruled_out_all_scale_by_known_zero'
            survived_impossible += not failures
        elif failures:
            assert row['status']=='falsified_on_held_out_scales'
        elif row['status']=='proved_all_scale_by_absolute_sum':
            weak = d['records'][row['kernel_id']]['available_weak_all_scale_certificate']
            assert theta>=1 and b>=0
            assert real(C)*real(2)**real(theta-1)*real(2).log()**b >=real(Q(weak['constant']))
        else:
            assert row['status']=='numerical_conjecture_missing_uniform_cancellation_certificate'
            assert row['obligations']
    plateau = d['finite_survivor_but_mathematically_impossible_control']
    assert plateau['kernel_id']==3 and plateau['held_out_passed']
    assert plateau['theta']=='0' and plateau['log_power']=='0' and plateau['post_fit_known_zero_obstruction']
    return values,{'independently_factored_inverse_coefficients':N,
        'exact_smoothed_observations':len(observations),'replayed_growth_proposals':len(d['candidate_estimates']),
        'Mellin_and_Bernstein_certificates':mellin_count,
        'held_out_failures':failed,'finite_survivors_ruled_out_by_known_zero':survived_impossible,
        'plateau_false_global_bound_rejected':True,'all_passed':True}


def zero_audit(source):
    zero = source['known_zero_obstruction_certificate']
    path = BASE/zero['dependency']
    assert hashlib.sha256(path.read_bytes()).hexdigest()==zero['dependency_sha256']
    dependency = json.loads(path.read_text())
    assert dependency['all_passed'] and dependency['source_artifact_sha256']==zero['source_sha256']
    assert hashlib.sha256((BASE/'shift-ratio-results/shift_ratio_analytic.json').read_bytes()).hexdigest()==zero['source_sha256']
    c = flint.acb(real(Q(1,2)),flint.arb(zero['centre'][1]))
    r = real(Q(zero['radius']))
    z = c+flint.acb(flint.arb(0,r),flint.arb(0,r))
    d1 = flint.acb_series([c,1],prec=2).zeta()[1]
    d2 = 2*flint.acb_series([z,1],prec=3).zeta()[2]
    assert d1.abs_lower()*r>c.zeta().abs_upper()+d2.abs_upper()*r*r/2
    records = []
    s = sp.Symbol('s')
    for row in source['cancellation_estimate_search']['records']:
        cert = row['Mellin_certificate']
        num,den = sp.fraction(sp.sympify(cert['transform']))
        numerator = sp.Poly(num,s).all_coeffs()
        denominator = sp.Poly(den,s).all_coeffs()
        def horner(a):
            out = flint.acb(0)
            for x in a:
                out = out*z+real(Q(str(x)))
            return out
        transform = horner(numerator)/horner(denominator)
        assert transform.is_finite() and transform.abs_lower()>0 and row['known_zero_visible']
        records.append({'kernel_id':row['id'],'independent_rational_Mellin_lower_ball':transform.abs_lower().str(35),
                        'known_zero_not_annihilated':True})
    return {'fresh_Rouche_one_zero_and_all_kernel_numerators':True,
            'reflection_uniqueness_argument_required_for_Re_half':True,'records':records,
            'sub_sqrt_and_sqrt_with_negative_log_cost_ruled_out':True,
            'no_RH_bound_inferred_from_finite_fit':True,'all_passed':True}


def dilation_audit(source, values):
    d = source['learned_cancellation_certificates']
    for row in d['learned_row_laws']:
        k,lam = row['multiplier'],row['lambda']
        assert all(values[k*n]==(lam*values[n] if gcd(k,n)==1 else 0)
                   for n in range(1,row['held_out_end']+1))
    for row in d['all_scale_certificates']:
        p = row['prime']
        assert flint.fmpz(p).is_prime() and row['lambda']==-1
        counts = [sum(n%p!=0 for n in range(X//p+1,X+1)) for X in range(1,3*p*p+1)]
        slope = Q(counts[p*p-1],p*p)
        boundary = max(Q(count)-slope*X for X,count in enumerate(counts,1))
        assert str(slope)==row['linear_constant'] and str(boundary)==row['boundary_cost']
        for X,count in enumerate(counts,1):
            assert count==X-2*(X//p)+X//(p*p)
            assert abs(sum(values[1:X+1]))<=count
        for X in (10**6+17,10**12+39,10**18+103):
            count = X-2*(X//p)+X//(p*p)
            assert Q(count)<=slope*X+boundary
    assert d['best_linear_bound']['linear_constant']=='1/4'
    # A valid composite row law leaves numbers divisible by only one of
    # its prime factors unaccounted for; it cannot serve as a two-row partition.
    assert values[6]==1 and values[2]!=0 and 2%6!=0 and gcd(2,6)>1
    return {'learned_dilation_rows':len(d['learned_row_laws']),
            'all_scale_classical_cancellation_certificates':len(d['all_scale_certificates']),
            'changed_scales_through_10_power_18_checked':True,
            'composite_full_partition_substitution_rejected':True,'all_passed':True}


@lru_cache(maxsize=None)
def decoder(n,v):
    # Independent prime-subset R followed by exponent-divisor stripping.
    fs = factors(n)
    g = gcd(*fs.values())
    out = flint.arb(0)
    for k in range(1,g+1):
        if g%k or not mu(k):
            continue
        m = product_int(p**(e//k) for p,e in fs.items())
        term = flint.arb(0)
        for bits in product((0,1),repeat=len(fs)):
            a = product_int(p for p,b in zip(fs,bits) if b)
            if a==m:
                continue
            b = m//a
            term += (-1)**sum(bits)*real(b).log()/(real(b).log()+real(v)*real(a).log())
        out += real(Q(mu(k),k))*term
    return out


def energy_audit(source):
    dependency = source['positive_energy_estimate_search']['score_envelope_proof_dependency']
    assert hashlib.sha256((BASE/'shift_ratio_proof.txt').read_bytes()).hexdigest()==dependency['proof_sha256']
    path = BASE/'shift-ratio-results/shift_ratio_verification.json'
    assert hashlib.sha256(path.read_bytes()).hexdigest()==dependency['verification_sha256']
    checked = json.loads(path.read_text())
    assert checked['all_passed'] and checked['source_artifact_sha256']==dependency['source_sha256']
    assert hashlib.sha256((BASE/'shift-ratio-results/shift_ratio_search.json').read_bytes()).hexdigest()==dependency['source_sha256']
    assert hashlib.sha256((BASE/'literature/roughness/fan_pomerance_rough_numbers.pdf').read_bytes()).hexdigest()==source['positive_energy_estimate_search']['imported_theorem_cached_primary_pdf_sha256']
    t = sp.Symbol('t',positive=True)
    controls = integrals = improvements = 0
    records = []
    for row in source['positive_energy_estimate_search']['records']:
        q = row['moment_order']
        if q==1:
            assert row['origin_valuation']==1 and 'not_certified' in row['status'] and row['obligations']
            continue
        A = [(Q(a['weight']),Q(a['v'])) for a in row['mixture']]
        assert all(w>0 and 0<v<=1 for w,v in A) and sum(w for w,v in A)==1
        h = sum(sp.Rational(w.numerator,w.denominator)*t/
                (sp.Rational(v.numerator,v.denominator)+(1-sp.Rational(v.numerator,v.denominator))*t)
                for w,v in A)
        assert sp.cancel(h-sp.sympify(row['envelope'],locals={'t':t}))==0
        integrand = sp.diff(h**q,t)/t
        given = sp.sympify(row['positive_integrand'],locals={'t':t})
        primitive = sp.sympify(row['antiderivative'],locals={'t':t})
        assert sp.cancel(integrand-given)==0 and sp.cancel(sp.diff(primitive,t)-integrand)==0
        expected_C = 2*(sp.limit(primitive,t,1,dir='-')-sp.limit(primitive,t,0,dir='+'))
        C_expr = sp.sympify(row['constant_expression'])
        assert sp.simplify(C_expr-expected_C)==0
        def transformed(u,analytic):
            a = sum((real(w)/(real(v)+real(1-v)*u*u) for w,v in A),flint.acb(0))
            derivative = sum((real(w*v)/(real(v)+real(1-v)*u*u)**2 for w,v in A),flint.acb(0))
            return 4*q*u**(2*q-3)*a**(q-1)*derivative
        native = flint.acb.integral(transformed,0,1,abs_tol=flint.arb('1e-40'),
                                    rel_tol=flint.arb('1e-40'),depth_limit=35,eval_limit=40000)
        assert native.is_finite() and native.imag.contains(0)
        assert native.real.overlaps(flint.arb(row['constant_native_integral_ball']))
        symbolic = evaluate_expression(C_expr)
        assert symbolic.overlaps(native.real)
        rounded = Q(row['constant_rational_upper'])
        if C_expr.is_Rational:
            # An exact constant can lie on the enclosure's boundary. The
            # antiderivative equality above, rather than overlap, proves it.
            assert Q(int(C_expr.p),int(C_expr.q))<=rounded
        else:
            assert native.real<=real(rounded)
        if q==2:
            jensen = 2*(1+sum((w/v for w,v in A),Q(0)))
            assert str(jensen)==row['existing_Jensen_constant']
            if len(A)>1:
                assert native.real.upper()<real(jensen) and row['strictly_improves_Jensen_for_this_mixture']
                improvements += 1
            else:
                assert sp.simplify(C_expr-sp.Rational(jensen.numerator,jensen.denominator))==0
        for X in (3,17,63,256):
            observed = flint.arb(0)
            for n in range(X,2*X+1):
                B = sum((real(w)*decoder(n,v) for w,v in A),flint.arb(0))
                P = min(factors(n))
                ratio = real(P).log()/real(n).log()
                envelope = sum((real(w)*ratio/(real(v)+real(1-v)*ratio) for w,v in A),flint.arb(0))
                if flint.fmpz(n).is_prime():
                    assert B.contains(1) and envelope.contains(1)
                else:
                    assert B.abs_upper()<envelope
                observed += integer_power_ball(B,q)
            assert observed<native.real*X/real(X).log()
            controls += 1
        assert row['imported_theorem']['id']=='Fan_Pomerance_Theorem_A'
        assert not row['imported_theorem']['external_full_sieve_proof_independently_verified']
        integrals += 1
        records.append({'moment_order':q,'mixture':row['mixture'],
            'changed_variable_native_constant_ball':native.real.str(35),
            'exact_antiderivative_and_positive_origin_certificate':True})
    return {'exact_and_changed_variable_integral_certificates':integrals,
            'complete_actual_arithmetic_doubling_moments':controls,
            'strict_improvements_over_supplied_Jensen_constants':improvements,
            'external_full_sieve_proof_independently_verified':False,
            'critical_divergence_is_envelope_limit_not_stronger_bound_disproof':True,
            'records':records,'all_passed':True}


def public_audit(values):
    from exact_arithmetic import program_value
    executions = 0
    for X in (19,83,509):
        c = [1,-3,3,-1]
        program = {'kind':'estimate_program','family':'smoothed_coefficient_sum','input':'a','kernel':c,'X':X}
        expected = sum((Q(values[n])*(1-Q(n,X))**3 for n in range(1,X+1)),Q(0))
        assert program_value(program,{'a':values})==expected
        executions += 1
    for p in (2,3,23,101):
        result = program_value({'kind':'estimate_program','family':'prime_dilation_cancellation_certificate','prime':p},{})
        assert Q(result['linear_constant'])==Q((p-1)**2,p*p)
        assert Q(result['boundary_cost'])==Q((2*p-1)*(p-1),p*p)
        executions += 1
    for degree in (1,2,3,4):
        c = [(-1)**j*comb(degree,j) for j in range(degree+1)]
        result = program_value({'kind':'estimate_program','family':'polynomial_Mellin_certificate','kernel':c},{})
        assert result['nonvanishing_Re_s_ge_zero_certified']
        executions += 1
    mixture = [{'weight':'2/5','v':'1/3'},{'weight':'3/5','v':'5/6'}]
    for order in (1,2):
        result = program_value({'kind':'estimate_program','family':'positive_envelope_moment_certificate',
            'mixture':mixture,'moment_order':order,'imported_theorem':'Fan_Pomerance_Theorem_A'},{})
        assert ('not_certified' in result['status'])==(order==1)
        executions += 1
    good = {'kind':'estimate_program','family':'candidate_growth_bound','constant':'3/7','theta':'1/2','log_power':'-1','X':101}
    assert program_value(good,{}).overlaps(real(Q(3,7))*real(101).sqrt()/real(101).log())
    executions += 1
    invalid = [(dict(good,**change),{}) for change in ({'constant':-1},{'theta':-1},{'X':1},{'X':True})]
    invalid += [({'kind':'estimate_program','family':'prime_dilation_cancellation_certificate','prime':p},{})
                for p in (1,6,30,True)]
    invalid += [({'kind':'estimate_program','family':'polynomial_Mellin_certificate','kernel':c},{})
                for c in ([],[1],[0,0],[1,1])]
    energy = {'kind':'estimate_program','family':'positive_envelope_moment_certificate',
              'mixture':mixture,'moment_order':2,'imported_theorem':'Fan_Pomerance_Theorem_A'}
    invalid += [(dict(energy,**change),{}) for change in ({'moment_order':0},{'moment_order':True},
                  {'imported_theorem':'numerical_training'},
                  {'mixture':[{'weight':'1','v':'0'}]},
                  {'mixture':[{'weight':'1/2','v':'1/2'}]},
                  {'mixture':[{'weight':'-1','v':'1/2'},{'weight':'2','v':'1/3'}]})]
    rejected = 0
    for program,data in invalid:
        try:
            program_value(program,data)
        except (ValueError,TypeError):
            rejected += 1
        else:
            raise AssertionError('Invalid estimate contract accepted: '+str(program))
    return {'public_executions':executions,'invalid_contracts_rejected':rejected,'all_passed':True}


def main():
    start = time.monotonic()
    flint.ctx.prec = 448
    path = DEST/'estimate_search.json'
    source = json.loads(path.read_text())
    assert source['all_passed'] and not source['production_coefficient_engine_uses_prime_or_factor_oracle']
    for key,name in (('producer_code_sha256','estimate_search.py'),
                     ('grammar_code_sha256','estimate_grammar.py'),('proof_sha256','estimate_proof.txt')):
        assert source[key]==hashlib.sha256((BASE/name).read_bytes()).hexdigest()
    values,arithmetic = arithmetic_and_fit_audit(source)
    zero = zero_audit(source)
    dilation = dilation_audit(source,values)
    energy = energy_audit(source)
    interface = public_audit(values)
    assert source['verified_new_operators']==[] and not source['new_RH_estimate_proved']
    assert not source['new_independent_prime_distribution_estimate_proved']
    checks = {'independent_actual_arithmetic_and_estimate_fits':arithmetic['all_passed'],
        'known_zero_visible_and_false_global_bounds_rejected':zero['all_passed'],
        'learned_cancellation_identities_have_universal_elementary_certificates':dilation['all_passed'],
        'synthesized_positive_energy_constants_have_exact_and_native_certificates':energy['all_passed'],
        'typed_public_estimate_entry_point_and_invalid_contracts':interface['all_passed'],
        'finite_fits_external_premises_RH_and_novelty_scopes_distinct':True}
    out = {'checks':checks,'arithmetic_and_fit_audit':arithmetic,'known_zero_audit':zero,
        'learned_dilation_audit':dilation,'positive_energy_audit':energy,'public_entry_point_audit':interface,
        'source_artifact_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
        'checker_code_sha256':hashlib.sha256((BASE/'check_estimates.py').read_bytes()).hexdigest(),
        'mathematical_audit_imports_production_code':False,'integration_checks_import_production_code':True,
        'all_passed':all(checks.values()),'seconds':time.monotonic()-start}
    (DEST/'estimate_verification.json').write_text(json.dumps(out,indent=2)+'\n')
    print('Independent estimate audit',sum(checks.values()),'/',len(checks),'seconds',out['seconds'],flush=True)


if __name__=='__main__':
    main()
