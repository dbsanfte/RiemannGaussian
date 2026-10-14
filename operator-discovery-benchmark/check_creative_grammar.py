#!/usr/bin/env python3
"""Independent native kernels/symbolic laws; separate integration controls."""

from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import json
import time
import flint
import sympy as sp

BASE=Path(__file__).resolve().parent
DEST=BASE/'creative-results'


def real(x):
    x=Q(x);return flint.arb(x.numerator)/x.denominator


def field_kernel(p):
    roots=[flint.acb(real(Q(2*k,p)).cos_pi(),real(Q(2*k,p)).sin_pi()) for k in range(p)]
    inv={x:pow(x,-1,p) for x in range(1,p)}
    return [[sum((roots[(a*x-b*inv[x])%p] for x in range(1,p)),flint.acb(0))/p
             for b in range(p)] for a in range(p)]


def native_kernel_audit(source):
    rows=[];count=0
    for row in source['inverse_Fourier_projection_discovery']['records']:
        p=row['prime'];K=field_kernel(p);error=flint.arb(0)
        for a,b in product(range(p),repeat=2):
            target=real(Q(int(a==b))-Q(1,p))
            value=sum((K[a][x]*K[x][b] for x in range(p)),flint.acb(0))-target
            assert value.contains(0)
            error=max(error,value.abs_upper());count+=1
            assert (K[a][b]-K[b][a].conjugate()).contains(0)
        assert error<flint.arb('1e-100')
        for a in range(p):assert sum(K[a],flint.acb(0)).contains(0)
        # Squaring gives a proper projection, not the identity.
        wrong=sum((K[0][x]*K[x][0] for x in range(p)),flint.acb(0))-1
        assert wrong.abs_lower()>0
        rows.append({'prime':p,'native_projection_identity_maximum_error_upper_ball':error.str(25),
                     'unqualified_involution_wrong_difference_lower_ball':wrong.abs_lower().str(25),'all_passed':True})
    return {'records':rows,'full_matrix_entries_checked':count,'all_passed':True}


def symbolic(source):
    x,y,z=sp.symbols('x y z');rows=[]
    for row in source['nonassociative_phase_search']['models']:
        a,b=row['left_degree'],row['right_degree']
        delta=sp.Poly(sp.expand(x**a*y**b+(x+y)**a*z**b-y**a*z**b-x**a*(y+z)**b),x,y,z)
        got={tuple(r['degrees']):r['coefficient'] for r in row['associator_polynomial']}
        assert {key:int(value) for key,value in delta.terms() if value}==got
        rows.append({'degrees':[a,b],'expanded_monomial_count':len(got),'all_passed':True})
    learned=source['learned_phase_kernel_search'];features=learned['monomial_features']
    polys=[sp.expand(x**a*y**b+(x+y)**a*z**b-y**a*z**b-x**a*(y+z)**b) for a,b in features]
    all_monomials=sorted(set().union(*(set(sp.Poly(f,x,y,z).monoms()) for f in polys)))
    matrix=sp.Matrix([[sp.Poly(f,x,y,z).coeff_monomial(key) for f in polys] for key in all_monomials])
    assert len(features)-matrix.rank()==4==learned['universal_kernel_span_dimension']
    for row in learned['learned_universal_kernel_basis']:
        assert matrix*sp.Matrix(row['coefficients'])==sp.zeros(matrix.rows,1)
    for row in learned['cross_prime_false_law_controls']:
        f=sum(c*poly for c,poly in zip(row['coefficients_mod_three'],polys))
        assert all(int(f.subs({x:i,y:j,z:k}))%3==0 for i,j,k in product(range(3),repeat=3))
        i,j,k=row['counterexample_grades'];assert int(f.subs({x:i,y:j,z:k}))%row['failed_prime']!=0
    assert sp.expand(polys[features.index([1,2])])==-2*x*y*z
    return {'phase_laws':rows,'unknown_kernel_symbolic_nullspace_dimension':4,
            'small_characteristic_false_laws_rejected':len(learned['cross_prime_false_law_controls']),'all_passed':True}


def mobius(n):
    factors={}
    for p,e in flint.fmpz(n).factor():factors[int(p)]=factors.get(int(p),0)+int(e)
    assert product_int(p**e for p,e in factors.items())==n
    return 0 if any(e>1 for e in factors.values()) else (-1)**len(factors)


def product_int(values):
    result=1
    for v in values:result*=v
    return result


def coefficient_bridge(source):
    rows=[];N=4096;mu=[0]+[mobius(n) for n in range(1,N+1)]
    for row in source['zeta_coefficient_residue_bridge']['records']:
        p=row['prime'];v=[sum(mu[n] for n in range(1,N+1) if n%p==r) for r in range(p)]
        assert v==row['residue_vector']
        energy=Q(sum(n*n for n in v))-Q(sum(v)**2,p)
        K=field_kernel(p);out=[sum((entry*n for entry,n in zip(kr,v)),flint.acb(0)) for kr in K]
        actual=sum((c.real*c.real+c.imag*c.imag for c in out),flint.arb(0))
        assert actual.contains(real(energy))
        assert abs(float(energy)-row['transformed_energy'])<1e-8
        rows.append({'prime':p,'exact_projected_energy':str(energy),'native_energy_ball':actual.str(25),'all_passed':True})
    return {'records':rows,'independent_factorization_Mobius_cutoff':N,'all_passed':True}


def commutator_spectrum(source):
    records=[];count=0
    for row in source['commutator_defect_search']['records']:
        p=row['prime'];assert flint.fmpz(p).is_prime() and p%2==1
        factors={int(q) for q,_ in flint.fmpz(p-1).factor()}
        generator=next(g for g in range(2,p) if all(pow(g,(p-1)//q,p)!=1 for q in factors))
        logs={pow(generator,j,p):j for j in range(p-1)};assert len(logs)==p-1
        roots=[flint.acb(real(Q(2*k,p)).cos_pi(),real(Q(2*k,p)).sin_pi()) for k in range(p)]
        characters=[flint.acb(real(Q(2*k,p-1)).cos_pi(),real(Q(2*k,p-1)).sin_pi()) for k in range(p-1)]
        zero=[];lower=[]
        for k in range(p-1):
            chi={x:characters[k*logs[x]%(p-1)] for x in range(1,p)}
            value=sum((roots[-x%p]*(chi[x].conjugate()-chi[x]) for x in range(1,p)),flint.acb(0))/flint.arb(p).sqrt()
            for a in {1,2,p-1}:
                actual=sum(((roots[-a*pow(b,-1,p)%p]-roots[-pow(a,-1,p)*b%p])*chi[b] for b in range(1,p)),flint.acb(0))/flint.arb(p).sqrt()
                assert (actual-value*chi[a]).contains(0)
            if k in (0,(p-1)//2):assert value.contains(0);zero.append(k)
            else:assert value.abs_lower()>0;lower.append(value.abs_lower())
            count+=1
        assert zero==row['zero_multiplicative_character_indices'] and len(lower)==p-3
        records.append({'prime':p,'native_nonzero_character_eigenvalues':len(lower),
                        'minimum_nonzero_eigenvalue_lower_ball':min(lower).str(25) if lower else None,'all_passed':True})
    return {'records':records,'character_eigenvalues_checked':count,
            'universal_proof_uses_cyclotomic_independence':True,
            'a_uniform_lower_bound_in_prime_scale_is_not_proved':True,'all_passed':True}


def integration(source):
    # This deliberately exercises the new public entry point. These imports
    # are not used by the independent native/symbolic mathematical audit.
    from exact_arithmetic import program_value
    from creative_grammar import Term,MAP,VECTOR,SCALAR,ARITHMETIC,atom,compose,apply,embed,gram
    import numpy as np
    term=Term.read(source['inverse_Fourier_projection_discovery']['term'])
    application=apply(term,atom('input',VECTOR,'x'))
    v=np.array([complex(n,n*n/7) for n in range(13)])
    first=program_value({'kind':'residue_program','prime':13,'term':application.data()},{'x':v})
    second=program_value({'kind':'residue_program','prime':13,'term':application.data()},{'x':first})
    assert np.max(np.abs(second-(v-v.mean())))<1e-10
    def public(term,p,inputs):return program_value({'kind':'residue_program','prime':p,'term':term.data()},inputs)
    f=atom('input',VECTOR,'f');g=atom('input',VECTOR,'g');h=atom('input',VECTOR,'h')
    learned_checks=0
    for row in source['executable_phase_kernel_controls']['learned_kernel_executions']:
        term=Term.read(row['term'])
        def multiply(a,b):return Term('learned_phase_product',VECTOR,(a,b),term.parameter)
        rng=np.random.default_rng(177);p=23
        inputs={name:rng.normal(size=p)+1j*rng.normal(size=p) for name in ('f','g','h')}
        assert np.max(np.abs(public(multiply(multiply(f,g),h),p,inputs)-public(multiply(f,multiply(g,h)),p,inputs)))<1e-9
        learned_checks+=1
    p=19;inputs={name:np.eye(p,dtype=complex)[degree] for name,degree in zip(('f','g','h'),(1,2,3))}
    def weird(a,b):return Term('weighted_cyclic_product',VECTOR,(a,b),[1,2])
    lhs=public(weird(weird(f,g),h),p,inputs)[6];rhs=public(weird(f,weird(g,h)),p,inputs)[6]
    assert abs(lhs/rhs-np.exp(-4j*np.pi*6/p))<1e-12 and abs(lhs-rhs)>0.1
    qrh=source['executable_QRH_scalar_controls'];left=Term.read(qrh['left_term']);right=Term.read(qrh['right_term'])
    scalar_checks=0
    for row in qrh['records']:
        p=row['prime_norm']
        assert abs(public(left,p,{})-public(right,p,{}))<1e-10
        assert public(atom('eisenstein_character_at',SCALAR,0),p,{})==0
        scalar_checks+=1
    rejected=0
    for fn in (lambda:apply(atom('F',MAP),atom('input',ARITHMETIC,'a')),
               lambda:compose(atom('input',VECTOR,'x'),atom('F',MAP)),
               lambda:program_value({'kind':'residue_program','prime':9,'term':application.data()},{'x':[0]*9}),
               lambda:program_value({'kind':'residue_program','prime':13,'term':embed(atom('input',ARITHMETIC,'a'),100).data()},{'a':[0]*10}),
               lambda:program_value({'kind':'residue_program','prime':13,'term':gram(atom('CONJ',MAP)).data()},{}),
               lambda:public(Term('pointwise',MAP,(atom('F',MAP),atom('FI',MAP))),13,{}),
               lambda:public(atom('constant_one',MAP),13,{}),
               lambda:public(Term('compose',MAP,(atom('input',VECTOR,'x'),atom('F',MAP))),13,{'x':v}),
               lambda:public(Term('learned_phase_product',VECTOR,(f,g),{'coefficients':[1],'monomials':[]}),13,{'f':v,'g':v}),
               lambda:public(atom('root_of_unity',SCALAR,[0,1]),13,{}),
               lambda:public(atom('eisenstein_gauss',SCALAR,2),5,{})):
        try:fn()
        except (TypeError,ValueError):rejected+=1
        else:raise AssertionError('Invalid typed/domain program was accepted')
    assert rejected==11
    return {'public_program_value_entry_point_checked':True,'fresh_prime_learned_kernel_executions':learned_checks,
            'nonassociative_basis_associator_checked':True,'normalized_QRH_scalar_executions':scalar_checks,
            'invalid_type_domain_and_missing_data_controls':rejected,'all_passed':True}


def main():
    start=time.monotonic();flint.ctx.prec=384
    source=json.loads((DEST/'creative_search.json').read_text());assert source['all_passed']
    native=native_kernel_audit(source);polys=symbolic(source);bridge=coefficient_bridge(source);spectrum=commutator_spectrum(source);entry=integration(source)
    assert source['commutator_defect_search']['observed_lead']['universal_rank_equality_proved']
    assert not source['operator_word_search']['numerical_aliases_promoted_to_theorems']
    assert source['verified_new_operators']==[] and not source['new_RH_estimate_proved']
    assert not source['new_uniform_prime_distribution_estimate_proved']
    checks={'native_full_matrix_Kloosterman_projection_and_nonunit_controls':native['all_passed'],
            'independent_symbolic_phase_and_learned_kernel_laws':polys['all_passed'],
            'complete_zeta_inverse_residue_embedding_and_energy_identity':bridge['all_passed'],
            'public_grammar_entry_point_and_type_domain_rejections':entry['all_passed'],
            'native_character_spectrum_and_universal_rank_proof':spectrum['all_passed'],
            'numerical_aliases_uniform_norm_and_RH_novelty_scope_honest':True}
    out={'checks':checks,'native_kernel_audit':native,'symbolic_audit':polys,'arithmetic_embedding_audit':bridge,
         'public_entry_point_audit':entry,'commutator_spectral_audit':spectrum,'mathematical_audit_imports_production_code':False,
         'integration_checks_import_production_code':True,'all_passed':all(checks.values()),'seconds':time.monotonic()-start}
    (DEST/'creative_verification.json').write_text(json.dumps(out,indent=2)+'\n')
    print('Independent creative grammar audit',sum(checks.values()),'/',len(checks),'seconds',out['seconds'],flush=True)


if __name__=='__main__':main()
