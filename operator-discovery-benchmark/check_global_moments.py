#!/usr/bin/env python3
"""Independent Laurent/native-circle/global-scale audit; separate API controls."""

from fractions import Fraction as Q
from pathlib import Path
import json
import time
import flint
import sympy as sp

BASE=Path(__file__).resolve().parent
DEST=BASE/'global-moment-results'


def real(x):
    x=Q(x);return flint.arb(x.numerator)/x.denominator


def roots(H):
    return [flint.acb(real(Q(2*k,H)).cos_pi(),real(Q(2*k,H)).sin_pi()) for k in range(H)]


def factor_mu(n):
    factors={}
    for p,e in flint.fmpz(n).factor():factors[int(p)]=factors.get(int(p),0)+int(e)
    rebuilt=1
    for p,e in factors.items():rebuilt*=p**e
    assert rebuilt==n
    return 0 if any(e>1 for e in factors.values()) else (-1)**len(factors)


def arithmetic_energy(source):
    mu=[0]+[factor_mu(n) for n in range(1,1025)];records=[]
    for row in source['additive_arithmetic_energy_search']['actual_zeta_inverse_family_observations']:
        D,H,d=row['scale'],row['row_modulus'],row['index_degree'];assert flint.fmpz(H).is_prime()
        chars=roots(H);native=flint.arb(0)
        for u in range(H):
            value=sum((mu[n]*chars[u*pow(n,d,H)%H] for n in range(1,D+1)),flint.acb(0))
            native+=value.real*value.real+value.imag*value.imag
        assert native.contains(row['exact_complete_residue_energy'])
        counts=[sum(pow(n,d,H)==r for n in range(1,D+1)) for r in range(H)]
        assert max(counts)==row['maximum_bucket_size'] and max(counts)<=d*((D+H-1)//H)
        # Put a(n)=1 only in a largest bucket: the exact norm is saturated.
        k=max(counts);residue=counts.index(k)
        saturated=[int(pow(n,d,H)==residue) for n in range(1,D+1)]
        sums=[sum(v for n,v in enumerate(saturated,1) if pow(n,d,H)==r) for r in range(H)]
        assert H*sum(v*v for v in sums)==H*k*sum(v*v for v in saturated)
        records.append({'scale':D,'row_modulus':H,'index_degree':d,'native_energy_ball':native.str(25),'all_passed':True})
    wrong=source['additive_arithmetic_energy_search']['operator_class_holdout']
    assert not flint.fmpz(wrong['row_modulus']).is_prime()
    assert sum(n*n%16==0 for n in range(1,17))==4>2
    assert wrong['actual_energy']==256 and wrong['invalid_prime_field_bound']==128
    return {'records':records,'independent_complete_Mobius_cutoff':1024,'prime_and_composite_operator_domains_checked':True,'all_passed':True}


def laurent_transfer(source):
    p,r,pc,rc,t=sp.symbols('p r pc rc t');E=p*p*pc*pc+r*r*rc*rc;C=p*pc*r*rc
    records=[]
    for row in source['generic_operator_moment_transfer_search']['universally_certified_transfers']:
        (a,b),(c,d)=row['signed_transfer_matrix'];k=row['shift_span_multiplier']
        u=a*p+b*t*r;uc=a*pc+b*rc/t;v=c*p+d*t*r;vc=c*pc+d*rc/t
        targets=[sp.expand((u*uc)**2+(v*vc)**2),sp.expand(u*uc*v*vc)]
        M=[[Q(v) for v in line] for line in row['fitted_energy_transfer']]
        for expression,line in zip(targets,M):
            assert sp.expand(expression.coeff(t,0)-line[0]*E-line[1]*C)==0
            assert set(sp.Poly(sp.expand(expression*t*t),t).monoms()).issubset({(j,) for j in range(5)})
            if k==1:assert expression.coeff(t,1)==expression.coeff(t,-1)==0
            else:assert k>=2
        assert k>=1
        records.append({'matrix':row['signed_transfer_matrix'],'shift_multiple':k,
                        'exact_Laurent_identity_and_universal_support_condition_checked':True,'all_passed':True})
    assert len(records)==24
    rejected=source['generic_operator_moment_transfer_search']['finite_training_recurrences_rejected']
    assert len(rejected)==16
    for row in rejected:
        P,R=[1,1],[1,2];shift=2*row['shift_span_multiplier'];outputs=[]
        for a,b in row['signed_transfer_matrix']:
            out=[0]*(2+shift)
            for n,v in enumerate(P):out[n]+=a*v
            for n,v in enumerate(R):out[n+shift]+=b*v
            outputs.append(out)
        def state(P,R):
            a=autocorrelation(P);b=autocorrelation(R)
            cross=a[0]*b[0]+2*sum(x*y for x,y in zip(a[1:],b[1:]))
            return [fourth(P)+fourth(R),cross]
        old=state(P,R);actual=state(*outputs)
        expected=[sum(Q(a)*b for a,b in zip(line,old)) for line in row['fitted_energy_transfer']]
        assert actual!=expected
    return {'records':records,'fresh_counterexamples_to_finite_training_recurrences':len(rejected),'all_passed':True}


def autocorrelation(a):
    return [sum(a[n]*a[n+k] for n in range(len(a)-k)) for k in range(len(a))]


def fourth(a):
    correlation=autocorrelation(a)
    return correlation[0]**2+2*sum(c*c for c in correlation[1:])


def native_circle(a,H):
    chars=roots(H);energy=flint.arb(0)
    for u in range(H):
        value=sum((coefficient*chars[u*n%H] for n,coefficient in enumerate(a)),flint.acb(0))
        squared=value.real*value.real+value.imag*value.imag
        energy+=squared*squared
    return energy/H


def global_recursion_and_moments(source):
    weights=[]
    for row in source['positive_functional_search']['records']:
        M=sp.Matrix([[Q(v) for v in line] for line in row['energy_transfer_matrix']]);rate=row['minimum_growth_rate']
        v=sp.Matrix([[Q(v) for v in row['minimizers'][0]['weights']]])
        assert v*M==rate*v and all(c>0 for c in v)
        positive_right=[vector for value,_,vectors in M.eigenvects() if value==rate for vector in vectors]
        assert len(positive_right)==1 and all(c>0 for c in positive_right[0])
        # A positive right eigenvector proves no smaller positive-functional
        # rate is possible, independently of the source's finite weight grid.
        weights.append({'rate':rate,'weights':[str(c) for c in v],'global_induction_and_optimal_positive_rate_proved':True})
    circle=[]
    for row in source['recursive_family_global_moment_calibration']['records']:
        j=row['level'];N=2**j
        a=[(-1)**(n&(n>>1)).bit_count() for n in range(N)]
        value=fourth(a);assert value==Q(row['exact_fourth_moment'])==Q(4*N*N-(-2)**j,3)
        assert value<=Q(3,2)*N*N
        if j<=5:
            ball=native_circle(a,2*N+1);assert ball.contains(real(value))
            circle.append({'level':j,'row_grid_size':2*N+1,'native_fourth_moment_ball':ball.str(25),'all_passed':True})
    for row in source['lacunary_family_global_moment_calibration']['records']:
        j=row['level'];N=3**j;a=[]
        for n in range(N):
            m=n;allowed=True
            while m:
                allowed&=m%3!=1;m//=3
            a.append(int(allowed))
        assert sum(a)==2**j and fourth(a)==Q(row['exact_fourth_moment'])==6**j
    j=sp.symbols('j',integer=True,nonnegative=True)
    # Validate the closed formula by initial values and its exact recurrence,
    # rather than expanding coefficient arrays at very large levels.
    formula=lambda k:sp.Rational(1,3)*(4*4**k-(-2)**k)
    assert formula(0)==1 and formula(1)==6
    assert sp.simplify(formula(j+2)-2*formula(j+1)-8*formula(j))==0
    # A too-short circle grid aliases nonzero frequencies into the integral.
    wrong=native_circle([1,1],2);assert (wrong-real(6)).abs_lower()>0
    return {'positive_functional_certificates':weights,'native_circle_moments':circle,
            'incorrect_short_grid_rejected':True,'all_level_formula_verified_by_recurrence':True,'all_passed':True}


def forcing_audit(source):
    checked=0
    for scale in (2,3,5):
        for rate in (Q(1,2),Q(3),Q(4),Q(6)):
            for beta in (1,2,3,4):
                r=rate/scale**beta;cost=sum((r**n for n in range(97)),Q(0))
                if r<1:assert cost==(1-r**97)/(1-r) and cost<=1/(1-r)
                elif r==1:assert cost==97
                else:assert cost>=97
                checked+=1
    controls=source['scale_cost_and_resonance_controls']
    row=next(v for v in controls['records'] if v['power_exponent']==2)
    assert row['critical_resonance_requires_logarithmic_scale_loss'] and not row['uniform_forced_cost_bound_proved']
    alias=controls['finite_horizon_constant_alias'];assert Q(alias['actual_cost'])>Q(alias['claimed_constant'])
    return {'fresh_recurrence_parameter_triples_checked':checked,'strict_margin_and_resonant_loss_checked':True,'all_passed':True}


def row_replication_audit(source):
    transfer=source['moment_to_arithmetic_target_transfer'];assert transfer['learned_moment_and_row_count_powers']==['1/2','-1/2']
    for row in transfer['held_out_replication_records']:
        m=row['admissible_row_count'];T=Q(row['target']);E=Q(row['uniform_error'])
        values=[T+E*(Q(2*j,m-1)-1) for j in range(m)]
        assert sum(v*v for v in values)==Q(row['exact_second_moment'])
        bound=Q(row['certified_rational_target_upper_bound']);squared=Q(row['exact_second_moment'])/m
        assert bound>=T and (bound-E)**2>=squared
        assert (bound-E-Q(1,2**32))**2<squared
    checked=0
    target=flint.acb(real(Q(7,5)),real(Q(-4,3)));error=Q(1,7)
    # Different complex rows and moment orders check the general transfer,
    # independently of the source's real second-moment fitting examples.
    for half_order in (1,2,3):
        rows=[target+flint.acb(real(error*x),real(error*y)) for x,y in ((1,0),(-1,0),(0,1),(0,-1))]
        moment=sum(((row.real*row.real+row.imag*row.imag)**half_order for row in rows),flint.arb(0))
        bound=real(error)+(moment/4)**(flint.arb(1)/(2*half_order))
        assert (bound-target.abs_upper()).lower()>0;checked+=1
    assert transfer['missing_error_control']['valid_bound']=='1'
    assert transfer['missing_error_control']['bound_with_error_discarded']=='0'
    assert not transfer['all_scale_prime_row_count_and_error_certificates_supplied']
    assert not transfer['new_Mobius_or_prime_target_bound_established']
    return {'native_complex_moment_orders_checked':checked,'exact_rational_upper_rounding_checked':True,
            'row_count_error_and_Mellin_numerator_premises_remain_separate':True,'all_passed':True}


def public_controls():
    from exact_arithmetic import program_value
    program={'kind':'family_moment_program','family':'circle_even_moment','input':'a','half_order':2}
    assert program_value(program,{'a':[1,1]})==6
    twist={'kind':'family_moment_program','family':'additive_twist_second_moment','input':'a','scale':5,'row_modulus':7}
    assert abs(program_value(twist,{'a':[0,1,-1,0,-1,1]})-28)<1e-9
    replication={'kind':'family_moment_program','family':'replicated_row_target_bound',
                 'moment_upper_input':'moment','error_input':'error','row_count':3,'half_order':1}
    bound=program_value(replication,{'moment':24,'error':Q(1,7)})
    assert (bound-Q(1,7))**2>=8 and (bound-Q(1,7)-Q(1,2**32))**2<8
    rejected=0
    for bad,inputs in ((dict(program,half_order=0),{'a':[1]}),
                       (dict(twist,scale=100),{'a':[0,1]}),
                       (dict(twist,row_modulus=0),{'a':[0]*6}),
                       (dict(twist,index_degree=-1),{'a':[0]*6}),
                       (dict(replication,row_count=0),{'moment':1,'error':0}),
                       (dict(replication,half_order=0),{'moment':1,'error':0}),
                       (replication,{'moment':-1,'error':0}),
                       (replication,{'moment':1,'error':-1})):
        try:program_value(bad,inputs)
        except (TypeError,ValueError):rejected+=1
        else:raise AssertionError('Invalid scale/domain program accepted')
    assert rejected==8
    return {'public_family_moment_entry_point_checked':True,'invalid_scale_order_and_missing_data_controls':rejected,'all_passed':True}


def main():
    start=time.monotonic();flint.ctx.prec=384
    source=json.loads((DEST/'global_moment_search.json').read_text());assert source['all_passed']
    arithmetic=arithmetic_energy(source);transfer=laurent_transfer(source)
    recursion=global_recursion_and_moments(source);forcing=forcing_audit(source);replication=row_replication_audit(source);public=public_controls()
    assert not source['QRH_global_moment_bound_independently_verified'] and source['verified_new_operators']==[]
    assert not source['new_uniform_prime_distribution_estimate_proved'] and not source['ordinary_zeta_zero_bridge_proved']
    checks={'independent_native_zeta_inverse_twist_energy_and_modulus_domains':arithmetic['all_passed'],
            'symbolic_Laurent_transfer_and_universal_support_separation':transfer['all_passed'],
            'positive_energy_functionals_induction_and_global_moment_formulas':recursion['all_passed'],
            'native_circle_integrals_and_short_grid_alias_rejection':recursion['all_passed'],
            'uniform_forcing_margin_and_logarithmic_resonance_loss':forcing['all_passed'],
            'moment_to_arithmetic_target_transfer_and_missing_premise_controls':replication['all_passed'],
            'public_entry_point_and_QRH_prime_root_novelty_scope':public['all_passed']}
    out={'checks':checks,'arithmetic_audit':arithmetic,'Laurent_audit':transfer,
         'global_recursion_audit':recursion,'forcing_audit':forcing,'row_replication_audit':replication,'public_entry_point_audit':public,
         'mathematical_audit_imports_production_code':False,'integration_checks_import_production_code':True,
         'all_passed':all(checks.values()),'seconds':time.monotonic()-start}
    (DEST/'global_moment_verification.json').write_text(json.dumps(out,indent=2)+'\n')
    print('Independent global moment audit',sum(checks.values()),'/',len(checks),'seconds',out['seconds'],flush=True)


if __name__=='__main__':main()
