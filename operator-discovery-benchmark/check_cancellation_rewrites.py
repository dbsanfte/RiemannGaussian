#!/usr/bin/env python3
"""Independent factorization, polynomial expansion and estimate proof replay."""

from fractions import Fraction as Q
from functools import lru_cache
from math import gcd
from pathlib import Path
import hashlib
import json
import time
import flint
import sympy as sp

BASE = Path(__file__).resolve().parent
DEST = BASE/'estimate-results'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def real(x):
    x = Q(x)
    return flint.arb(x.numerator)/x.denominator


@lru_cache(maxsize=None)
def factors(n):
    out = {}
    for p,e in flint.fmpz(n).factor():
        p,e = int(p),int(e)
        assert flint.fmpz(p).is_prime()
        out[p] = out.get(p,0)+e
    product = 1
    for p,e in out.items():
        product *= p**e
    assert product==n
    return out


def mu(n):
    f = factors(n)
    return 0 if any(e>1 for e in f.values()) else (-1)**len(f)


def divisors(n):
    ds = [1]
    for p,e in factors(n).items():
        ds = [d*p**j for d in ds for j in range(e+1)]
    return sorted(ds)


def rational(x):
    x = Q(x)
    return sp.Rational(x.numerator,x.denominator)


def certificate_audit(source,values):
    u = sp.Symbol('u')
    coefficient_controls = 0
    observed = 0
    data_cache = {}
    for row in source['records']:
        cert = row['certificate']
        primes = cert['primes']
        P = 1
        delta = Q(1)
        for p in primes:
            P *= p
            delta *= Q(p-1,p)
        assert factors(P)=={p:1 for p in primes}
        ds = [(d,mu(d)) for d in divisors(P)]
        assert cert['divisors_with_sign']==list(map(list,ds))
        assert str(delta)==cert['rough_row_density']
        if P not in data_cache:
            for n in range(1,len(values)):
                d = gcd(n,P)
                rest = n//d
                right = mu(d)*values[rest] if gcd(rest,P)==1 else 0
                assert right==values[n]
                coefficient_controls += 1
            wanted = {o['X']//d for r in source['records'] if r['certificate']['primes']==primes
                      for o in r['changed_scale_identity_controls'] for d,sign in ds if o['X']//d}
            data_cache[P] = {Y: [sum(values[n]*n**j for n in range(1,Y+1) if gcd(n,P)==1)
                                for j in range(5)] for Y in wanted}
            for x in (Q(19,3),Q(31,7),Q(3*P+1,2),Q(10**12+39,11),Q(10**18+103,7)):
                count = sum(sign*(x.numerator//(x.denominator*d)) for d,sign in ds)
                assert abs(Q(count)-delta*x)<=2**(len(primes)-1)
                if x<4*P:
                    assert count==sum(gcd(n,P)==1 for n in range(1,x.numerator//x.denominator+1))
        c = list(map(Q,cert['kernel']))
        d0 = len(c)-1
        I = V = Q(0)
        previous = Q(0)
        for cell in cert['cells']:
            left,right = Q(cell['left']),Q(cell['right'])
            middle = (left+right)/2
            active = [(d,sign) for d,sign in ds if d*middle<1]
            assert cell['active_divisors_with_sign']==list(map(list,active))
            F = sum(sign*sum(rational(a)*(d*u)**j for j,a in enumerate(c)) for d,sign in active)
            given = sum(rational(a)*u**j for j,a in enumerate(cell['polynomial_coefficients']))
            assert sp.expand(F-given)==0
            bern = list(map(Q,cell['Bernstein_coefficients']))
            positive = list(map(Q,cell['positive_envelope_Bernstein_coefficients']))
            assert positive==list(map(abs,bern)) and positive[0]==previous
            previous = positive[-1]
            t = (u-rational(left))/rational(right-left)
            bases = [sp.binomial(d0,k)*t**k*(1-t)**(d0-k) for k in range(d0+1)]
            assert sp.expand(F-sum(rational(a)*B for a,B in zip(bern,bases)))==0
            U = sp.Poly(sp.expand(sum(rational(a)*B for a,B in zip(positive,bases))),u)
            integral = sum((Q(str(a))*(right**(j+1)-left**(j+1))/(j+1)
                            for (j,),a in U.terms()),Q(0))
            variation = sum(abs(b-a) for a,b in zip(positive,positive[1:]))
            assert str(integral)==cell['envelope_integral'] and str(variation)==cell['variation_upper']
            derivative_bound_expression = d0/rational(right-left)*sum(
                rational(positive[k+1]-positive[k])*sp.binomial(d0-1,k)*t**k*(1-t)**(d0-1-k)
                for k in range(d0))
            assert sp.expand(sp.diff(U.as_expr(),u)-derivative_bound_expression)==0
            I += integral
            V += variation
        assert previous==0
        assert str(I)==cert['envelope_integral'] and str(V)==cert['envelope_variation_upper']
        assert Q(cert['linear_constant'])==delta*I
        assert Q(cert['boundary_cost'])==2**(len(primes)-1)*V
        assert not cert['external_prime_distribution_theorem_used']
        assert cert['target']=='sum_(n<=X)mu(n)*W(n/X)' and 'Dirichlet inverse' in cert['coefficient_requirement']
        assert cert['arithmetic_target_preserved_exactly'] and cert['ordinary_zeta_Mellin_transform_preserved_exactly']
        for o in row['changed_scale_identity_controls']:
            X = o['X']
            raw = [sum(values[n]*n**j for n in range(1,X+1)) for j in range(5)]
            expected = sum((a*Q(raw[j],X**j) for j,a in enumerate(c)),Q(0))
            rewritten = sum((sign*sum((a*Q(d**j*data_cache[P][X//d][j],X**j)
                                      for j,a in enumerate(c)),Q(0))
                             for d,sign in ds if X//d),Q(0))
            assert expected==rewritten==Q(o['exact_rewritten_target'])
            assert abs(expected)<=delta*I*X+2**(len(primes)-1)*V
            observed += 1
    return {'exact_piecewise_Bernstein_and_discrepancy_certificates':len(source['records']),
            'independent_coefficient_partition_controls':coefficient_controls,
            'changed_scale_exact_rewrite_controls':observed,
            'finite_sieve_discrepancy_changed_scales_through_10_power_18':True,
            'Mellin_zero_fidelity_preserved_by_exact_identity':True,'all_passed':True}


def feedback_audit(source,estimates,values):
    targets = {r['id']:r for r in estimates['cancellation_estimate_search']['candidate_estimates']}
    c_by_id = {r['id']:list(map(Q,r['kernel'])) for r in estimates['cancellation_estimate_search']['records']}
    cache = {}
    def actual(k,X):
        if k not in cache:
            c = c_by_id[k]
            sums = [0]*len(c)
            out = {}
            for n in range(1,len(values)):
                power = 1
                for j in range(len(c)):
                    sums[j] += values[n]*power
                    power *= n
                if n>=2:
                    out[n] = sum((a*Q(sums[j],n**j) for j,a in enumerate(c)),Q(0))
            cache[k] = out
        return cache[k][X]
    def bound(C,theta,b,X):
        return real(C)*(real(X).log()*real(theta)).exp()*real(X).log()**b
    def replay(k,C,theta,b,rewrite_id,threshold,initial):
        cert = source['records'][rewrite_id]['certificate']
        assert theta>=1 and b>=0 and threshold>=2
        assert cert['kernel']==list(map(str,c_by_id[k]))
        L = real(C)*real(threshold)**real(theta-1)*real(threshold).log()**b
        R = real(Q(cert['linear_constant'])+Q(cert['boundary_cost'])/threshold)
        assert L>=R
        observations = []
        for X in range(2,threshold):
            y = actual(k,X)
            assert real(abs(y))<=bound(C,theta,b,X)
            observations.append([X,str(y)])
        assert initial['status']=='certified_all_initial_integer_scales'
        assert initial['count']==len(observations)
        assert initial['exact_observations_sha256']==hashlib.sha256(json.dumps(observations).encode()).hexdigest()
        return len(observations)
    proved = falsified = repaired = initial_controls = open_goals = 0
    for row in source['estimate_obligation_feedback']:
        target = targets[row['estimate_id']]
        assert target['status']=='numerical_conjecture_missing_uniform_cancellation_certificate'
        k,C,theta,b = row['kernel_id'],Q(row['target_constant']),Q(row['target_theta']),int(row['target_log_power'])
        assert (str(C),str(theta),str(b))==(target['constant'],target['theta'],target['log_power'])
        if row['status']=='proved_original_estimate_by_finite_prefix_and_monotone_tail':
            initial_controls += replay(k,C,theta,b,row['rewrite_candidate_id'],row['tail_threshold'],row['initial_scale_proof_attempt'])
            proved += 1
            assert row['available_affine_bound_implies_requested_growth_bound']
        elif row['status']=='original_estimate_falsified_at_initial_scale':
            failed = row['initial_scale_proof_attempt']
            X = failed['X']
            y = actual(k,X)
            assert str(y)==failed['exact_sum'] and real(abs(y))>bound(C,theta,b,X)
            falsified += 1
        else:
            assert row['status']=='uniform_cancellation_obligation_still_open' and row['new_subgoal']
            open_goals += 1
        if 'synthesized_repaired_estimate' in row:
            fix = row['synthesized_repaired_estimate']
            assert (fix['theta'],fix['log_power'])==(str(theta),str(b))
            initial_controls += replay(k,Q(fix['constant']),theta,b,fix['rewrite_candidate_id'],fix['tail_threshold'],fix['finite_prefix_proof'])
            assert not fix['new_sublinear_cancellation']
            repaired += 1
    assert repaired==source['repaired_all_scale_estimates_proved']
    assert proved+falsified+open_goals==len(source['estimate_obligation_feedback'])
    return {'original_estimates_proved':proved,'original_estimates_falsified_at_initial_scales':falsified,
            'synthesized_repaired_all_scale_estimates_proved':repaired,'open_uniform_cancellation_goals':open_goals,
            'every_initial_integer_scale_replayed':initial_controls,
            'sublinear_or_RH_quality_bound_certified':False,'all_passed':True}


def public_audit(values):
    from exact_arithmetic import program_value
    executions = 0
    for primes in ([2],[3,11],[2,5,13]):
        for c in ([1,-1],[1,-3,3,-1]):
            result = program_value({'kind':'estimate_feedback_program','family':'rough_row_rewrite_certificate',
                                    'primes':primes,'kernel':c},{})
            assert result['arithmetic_target_preserved_exactly'] and not result['square_root_cancellation_obligation_discharged']
            executions += 1
            for X in (11,53,257):
                raw = sum((Q(values[n])*sum((Q(a)*Q(n,X)**j for j,a in enumerate(c)),Q(0))
                           for n in range(1,X+1)),Q(0))
                actual = program_value({'kind':'estimate_feedback_program','family':'rough_row_rewrite_value',
                        'input':'a','primes':primes,'kernel':c,'X':X},{'a':values})
                assert actual==raw
                executions += 1
    good = {'kind':'estimate_feedback_program','family':'rough_row_rewrite_certificate','primes':[2,3],'kernel':[1,-1]}
    invalid = [dict(good,primes=p) for p in ([],[2,2],[6],[True],list(range(2,11)))]
    invalid += [dict(good,kernel=c) for c in ([1],[0,0],[1,1],[1]+[0]*8+[-1])]
    rejected = 0
    for program in invalid:
        try:
            program_value(program,{})
        except (ValueError,TypeError):
            rejected += 1
        else:
            raise AssertionError('Invalid rewrite contract accepted')
    evaluator = dict(good,family='rough_row_rewrite_value',input='a',X=37)
    changed = values.copy()
    changed[2] = 1
    for bad_values in ([0]+[1]*37,changed,[0,1]):
        try:
            program_value(evaluator,{'a':bad_values})
        except ValueError:
            rejected += 1
        else:
            raise AssertionError('A generic or incomplete coefficient sequence inherited the Mobius rewrite')
    return {'public_executions':executions,'invalid_contracts_rejected':rejected,'all_passed':True}


def main():
    start = time.monotonic()
    flint.ctx.prec = 448
    path = DEST/'cancellation_rewrite_search.json'
    source = json.loads(path.read_text())
    assert source['all_passed']
    assert sha(DEST/'estimate_search.json')==source['source_estimate_search_sha256']
    assert sha(DEST/'estimate_verification.json')==source['source_estimate_verification_sha256']
    estimates = json.loads((DEST/'estimate_search.json').read_text())
    assert json.loads((DEST/'estimate_verification.json').read_text())['all_passed']
    for key,name in (('producer_code_sha256','cancellation_rewrite_search.py'),
                     ('grammar_code_sha256','cancellation_rewrite_grammar.py'),('proof_sha256','cancellation_rewrite_proof.txt')):
        assert source[key]==sha(BASE/name)
    values = [0]+[mu(n) for n in range(1,source['coefficient_cutoff']+1)]
    proofs = certificate_audit(source,values)
    feedback = feedback_audit(source,estimates,values)
    interface = public_audit(values)
    assert not source['sublinear_cancellation_certificate_discovered']
    assert not source['new_independent_prime_distribution_estimate_proved'] and not source['new_RH_estimate_proved']
    assert source['verified_new_operators']==[]
    checks = {'universal_polynomial_envelope_and_finite_sieve_certificates':proofs['all_passed'],
              'actual_arithmetic_rewrites_preserve_target_and_zero_signature':proofs['all_passed'],
              'finite_prefix_and_monotone_all_scale_proofs_replayed':feedback['all_passed'],
              'typed_public_rewrite_entry_point_and_invalid_contracts':interface['all_passed'],
              'unresolved_sublinear_cancellation_and_novelty_scope_honest':True}
    out = {'checks':checks,'certificate_audit':proofs,'estimate_feedback_audit':feedback,
           'public_entry_point_audit':interface,'source_artifact_sha256':sha(path),
           'checker_code_sha256':sha(BASE/'check_cancellation_rewrites.py'),
           'mathematical_audit_imports_production_code':False,'integration_checks_import_production_code':True,
           'all_passed':all(checks.values()),'seconds':time.monotonic()-start}
    (DEST/'cancellation_rewrite_verification.json').write_text(json.dumps(out,indent=2)+'\n')
    print('Independent cancellation-rewrite audit',sum(checks.values()),'/',len(checks),'seconds',out['seconds'],flush=True)


if __name__=='__main__':
    main()
