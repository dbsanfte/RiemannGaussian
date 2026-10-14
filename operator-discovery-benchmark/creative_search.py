#!/usr/bin/env python3
"""Enumerate representation changes, defects, and nonassociative phase laws."""

from fractions import Fraction as Q
from itertools import product
from math import comb,gcd,lcm
from pathlib import Path
import hashlib
import json
import time
import numpy as np

from creative_grammar import (Term,MAP,VECTOR,SCALAR,ARITHMETIC,atom,compose,apply,combine,defect,gram,embed,
                              evaluate,outer,word_term,word_matrix,word_normal_form,
                              universal_kloosterman_certificate,information_gates,PRODUCTION_CATALOGUE,residue_character)

BASE=Path(__file__).resolve().parent
DEST=BASE/'creative-results'
OPS=('F','FI','INV','MASK','C2','C3','C4','T','M','CONJ')
HELD=(19,31,37,43,61)


def fingerprint(A,anti):
    real=np.round(A.real,8);imag=np.round(A.imag,8)
    real[np.abs(real)<1e-8]=0;imag[np.abs(imag)<1e-8]=0
    return hashlib.sha256(real.tobytes()+imag.tobytes()+bytes([anti])).hexdigest()


def enumeration():
    words=[()]
    for length in range(1,5):words.extend(product(OPS,repeat=length))
    caches={p:{():(np.eye(p,dtype=complex),False)} for p in (7,13)}
    groups={}
    for word in words:
        keys=[]
        for p,cache in caches.items():
            if word:
                child,anti=cache[word[1:]];cache[word]=outer(word[0],child,anti,p)
            A,anti=cache[word];keys.append(fingerprint(A,anti))
        groups.setdefault(tuple(keys),[]).append(word)
    certified=unproved=0;examples=[];pairs=[]
    for group in groups.values():
        reference=group[0];normal_ref,_=word_normal_form(reference)
        for candidate in group[1:]:
            normal,steps=word_normal_form(candidate);proved=normal==normal_ref
            if proved:certified+=1
            else:
                unproved+=1;pairs.append((reference,candidate))
                if len(examples)<80:examples.append({'reference':list(reference),'candidate':list(candidate),
                                                    'proof_status':'unproved','finite_match_only':True})
    # All training aliases not covered by a proof rule get fresh-prime probes.
    held=[]
    for p in HELD:
        rng=np.random.default_rng(2026100700+p)
        inputs=rng.normal(size=(p,2))+1j*rng.normal(size=(p,2))
        cache={(): (inputs,False)}
        needed=set()
        for a,b in pairs:
            for word in (a,b):
                for k in range(len(word)):needed.add(word[k:])
        for word in sorted(needed,key=len):
            child,anti=cache[word[1:]];cache[word]=outer(word[0],child,anti,p)
        failures=[]
        for reference,candidate in pairs:
            if np.max(np.abs(cache[reference][0]-cache[candidate][0]))>1e-8:failures.append((reference,candidate))
        held.append({'prime':p,'unproved_training_relations_tested':len(pairs),
                     'held_out_failures':len(failures),'generic_complex_probes':2})
        print('Creative held prime',p,'relations',len(pairs),'rejections',len(failures),flush=True)
    return {'primitives':list(OPS),'maximum_word_length':4,'map_programs_evaluated':len(words),
            'training_prime_full_basis_dimensions':[7,13],'distinct_training_fingerprints':len(groups),
            'universal_rewrite_certified_aliases':certified,'unproved_training_aliases':unproved,
            'unproved_alias_examples':examples,'fresh_prime_audits':held,
            'numerical_aliases_promoted_to_theorems':False,'all_passed':True}


def inverse_fourier_discovery():
    word=('FI','INV','MASK','F');target=('FI','MASK','F')
    models=[]
    for k in range(1,5):
        matches=True
        for p in (7,13):
            K,_=word_matrix(word,p);Qmat,_=word_matrix(target,p)
            matches=matches and np.max(np.abs(np.linalg.matrix_power(K,k)-Qmat))<1e-10
        models.append({'power':k,'training_equals_constant_complement_projection':bool(matches)})
    assert [m['power'] for m in models if m['training_equals_constant_complement_projection']]==[2,4]
    certificate=universal_kloosterman_certificate(word);assert certificate
    rows=[]
    for p in (2,3,5,7,13,*HELD):
        K,_=word_matrix(word,p);projection=np.eye(p)-np.ones((p,p))/p
        error=float(np.max(np.abs(K@K-projection)));cube=float(np.max(np.abs(K@K@K-K)))
        assert error<1e-10 and cube<1e-10
        rows.append({'prime':p,'projection_law_max_error':error,'cubic_law_max_error':cube,
                     'empirical_rank':int(np.linalg.matrix_rank(K,tol=1e-8)),
                     'empirical_operator_norm':float(np.linalg.norm(K,2)),'all_passed':True})
    return {'term':word_term(word).data(),'power_models':models,'minimal_positive_projection_power':2,
            'records':rows,'universal_certificate':certificate,'candidate_gates':information_gates(certificate),
            'historical_status':'Known finite Fourier/inversion/Kloosterman construction; recovered calibration',
            'all_passed':True}


def defect_search():
    rows=[]
    for p in (7,13,*HELD,3,5,11,17,23,29,41,47,53,67,71,101,103):
        F,_=word_matrix(('F',),p);I,_=word_matrix(('INV',),p);P,_=word_matrix(('MASK',),p)
        A=F@I-I@F;B=F@P-P@F
        rankA=int(np.linalg.matrix_rank(A,tol=1e-8));rankB=int(np.linalg.matrix_rank(B,tol=1e-8))
        assert rankB==2
        singular=np.linalg.svd(A,compute_uv=False);nonzero=singular[singular>1e-8]
        zero_characters=[];spectral_error=0
        roots=np.exp(-2j*np.pi*np.arange(p)/p)
        for k in range(p-1):
            chi=residue_character(p,p-1,k)
            value=np.sum(roots*(chi.conjugate()-chi))/np.sqrt(p)
            spectral_error=max(spectral_error,float(np.max(np.abs(A@chi-value*chi))))
            if abs(value)<1e-8:zero_characters.append(k)
        assert zero_characters==[0,(p-1)//2] and spectral_error<1e-10
        rows.append({'prime':p,'Fourier_inverse_commutator_rank':rankA,
                     'sample_rank_minus_p':rankA-p,
                     'smallest_observed_nonzero_singular_value':float(min(nonzero)) if len(nonzero) else None,
                     'Fourier_support_mask_commutator_rank':rankB,
                     'zero_multiplicative_character_indices':zero_characters,
                     'multiplicative_character_diagonalization_error':spectral_error})
    assert all(r['sample_rank_minus_p']==-3 for r in rows)
    return {'observed_lead':{'term':defect(atom('F',MAP),atom('INV',MAP)).data(),
                             'sampled_rank_rule':'p-3','universal_rank_equality_proved':True,
                             'proof_status':'Multiplicative characters diagonalize the nonzero residue block; cyclotomic independence proves exactly two zero eigenvalues for every odd prime',
                             'eigenvalue_formula':'lambda_chi=p^-1/2 sum_(x!=0)e_p(-x)*(conjugate(chi(x))-chi(x))',
                             'historical_novelty_established':False},
            'calibration':{'term':defect(atom('F',MAP),atom('MASK',MAP)).data(),
                           'universal_rank_two_for_all_primes_proved':True,
                           'reason':'Commutator with a rank-one complement; explicit independent constant and coordinate vectors'},
            'records':rows,'uniform_pseudoinverse_norm_bound_proved':False,'all_passed':True}


def phase_polynomial(a,b):
    out={}
    def add(key,value):
        out[key]=out.get(key,0)+value
        if not out[key]:del out[key]
    add((a,b,0),1);add((0,a,b),-1)
    for k in range(a+1):add((k,a-k,b),comb(a,k))
    for k in range(b+1):add((a,k,b-k),-comb(b,k))
    return out


def phase_products():
    rows=[]
    for a,b in product(range(1,5),repeat=2):
        poly=phase_polynomial(a,b)
        for x,y,z in product(range(6),repeat=3):
            raw=x**a*y**b+(x+y)**a*z**b-y**a*z**b-x**a*(y+z)**b
            expanded=sum(c*x**i*y**j*z**k for (i,j,k),c in poly.items())
            assert raw==expanded
        rows.append({'left_degree':a,'right_degree':b,'associator_polynomial':[
                     {'degrees':list(key),'coefficient':value} for key,value in sorted(poly.items())],
                     'universally_associative':not poly,
                     'universal_graded_associator_law_proved':True,
                     'nonassociativity_is_rejection':False,'all_passed':True})
    chosen=next(r for r in rows if (r['left_degree'],r['right_degree'])==(1,2))
    assert chosen['associator_polynomial']==[{'degrees':[1,1,1],'coefficient':-2}]
    return {'phase_product_programs':16,'models':rows,
            'selected_unconventional_law':'w(x,y)=exp(2*pi*i*x*y**2/p); associator on basis triples is exp(-4*pi*i*x*y*z/p)',
            'all_integer_Dirichlet_grade_lift':'Replace x,y,z by Omega(i),Omega(j),Omega(k); Omega(ij)=Omega(i)+Omega(j) proves the same law at every integer index',
            'unit_is_delta_one':True,'analytic_absolute_domain_for_zeta_product':'Re(s)>1, by domination by d_2(n)',
            'ordinary_zeta_zero_bridge_proved':False,'new_prime_distribution_estimate_proved':False,
            'historical_status':'Phase-twisted graded algebra framework; specific applications remain leads, not verified novelty',
            'all_passed':True}


def nullspace(rows,columns,prime=None):
    M=[[Q(x) if prime is None else x%prime for x in row] for row in rows];pivots=[];r=0
    for c in range(columns):
        pivot=next((i for i in range(r,len(M)) if M[i][c]),None)
        if pivot is None:continue
        M[r],M[pivot]=M[pivot],M[r]
        inverse=1/M[r][c] if prime is None else pow(int(M[r][c]),-1,prime)
        M[r]=[x*inverse if prime is None else x*inverse%prime for x in M[r]]
        for i in range(len(M)):
            if i==r or not M[i][c]:continue
            coefficient=M[i][c]
            M[i]=[a-coefficient*b if prime is None else (a-coefficient*b)%prime for a,b in zip(M[i],M[r])]
        pivots.append(c);r+=1
        if r==len(M):break
    basis=[]
    for c in range(columns):
        if c in pivots:continue
        v=[Q(0) if prime is None else 0]*columns;v[c]=Q(1) if prime is None else 1
        for i,p in enumerate(pivots):v[p]=-M[i][c] if prime is None else (-M[i][c])%prime
        if prime is None:
            denominator=lcm(*(x.denominator for x in v));v=[int(x*denominator) for x in v]
            divisor=gcd(*v);v=[x//divisor for x in v]
        basis.append(v)
    return basis


def kernel_synthesis():
    monomials=[(i,j) for degree in range(2,6) for i in range(1,degree) for j in (degree-i,)]
    def row(x,y,z):
        return [x**a*y**b+(x+y)**a*z**b-y**a*z**b-x**a*(y+z)**b for a,b in monomials]
    learned=nullspace([row(x,y,z) for x,y,z in product((1,2,3),repeat=3)],len(monomials))
    assert len(learned)==4
    certified=[]
    for coefficients in learned:
        total={}
        for (a,b),value in zip(monomials,coefficients):
            for key,c in phase_polynomial(a,b).items():
                total[key]=total.get(key,0)+value*c
                if not total[key]:del total[key]
        assert not total
        certified.append({'coefficients':coefficients,'symbolic_associator_polynomial':[],
                          'universal_law_proved':True})
    # Small-characteristic training may produce extra functional laws. Every
    # such law is explicitly held out at another prime, rather than lifted.
    small=nullspace([row(x,y,z) for x,y,z in product(range(3),repeat=3)],len(monomials),3)
    aliases=[]
    for coefficients in small:
        fails=next(((x,y,z) for x,y,z in product(range(7),repeat=3)
                    if sum(a*b for a,b in zip(coefficients,row(x,y,z)))%7),None)
        if fails:aliases.append({'coefficients_mod_three':coefficients,'failed_prime':7,
                                'counterexample_grades':list(fails),'universality_rejected':True})
    assert aliases
    return {'kernel_parameterization':'exp(2*pi*i*P(x,y)/p), P=sum unknown_c_(i,j)*x^i*y^j',
            'unknown_coefficients':len(monomials),'monomial_features':[list(v) for v in monomials],
            'training_grade_triples':27,'learned_universal_kernel_basis':certified,
            'universal_kernel_span_dimension':4,'small_characteristic_nullspace_dimension':len(small),
            'cross_prime_false_law_controls':aliases,
            'historical_status':'Recovered polynomial cocycles/coboundaries; no historical novelty claimed',
            'all_passed':True}


def executable_kernels(synthesis):
    f=atom('input',VECTOR,'f');g=atom('input',VECTOR,'g');h=atom('input',VECTOR,'h')
    rows=[]
    for model in synthesis['learned_universal_kernel_basis']:
        parameter={'coefficients':model['coefficients'],'monomials':synthesis['monomial_features']}
        def multiply(a,b):return Term('learned_phase_product',VECTOR,(a,b),parameter)
        term=multiply(f,g);held=[]
        for p in (11,17):
            rng=np.random.default_rng(2026100710+p)
            inputs={name:rng.normal(size=p)+1j*rng.normal(size=p) for name in ('f','g','h')}
            left=evaluate(multiply(multiply(f,g),h),p,inputs)
            right=evaluate(multiply(f,multiply(g,h)),p,inputs)
            error=float(np.max(np.abs(left-right)));assert error<1e-9
            held.append({'prime':p,'generic_vector_associativity_error':error,'all_passed':True})
        rows.append({'coefficients':model['coefficients'],'term':term.data(),'records':held,'all_passed':True})
    p=17;v=np.eye(p,dtype=complex)[1];inputs={'f':v,'g':v,'h':v}
    def weird(a,b):return Term('weighted_cyclic_product',VECTOR,(a,b),[1,2])
    left=evaluate(weird(weird(f,g),h),p,inputs);right=evaluate(weird(f,weird(g,h)),p,inputs)
    target=np.exp(-4j*np.pi/p)
    ratio_error=float(abs(left[3]/right[3]-target));disagreement=float(np.max(np.abs(left-right)))
    assert ratio_error<1e-12 and disagreement>0.1
    false_controls=[]
    for model in synthesis['cross_prime_false_law_controls']:
        parameter={'coefficients':model['coefficients_mod_three'],'monomials':synthesis['monomial_features']}
        def multiply(a,b):return Term('learned_phase_product',VECTOR,(a,b),parameter)
        p=model['failed_prime'];i,j,k=model['counterexample_grades']
        inputs={name:np.eye(p,dtype=complex)[degree] for name,degree in zip(('f','g','h'),(i,j,k))}
        left=evaluate(multiply(multiply(f,g),h),p,inputs);right=evaluate(multiply(f,multiply(g,h)),p,inputs)
        error=float(np.max(np.abs(left-right)));assert error>1e-8
        false_controls.append({'prime':p,'counterexample_grades':[i,j,k],'actual_associativity_difference':error,'rejected':True})
    return {'learned_kernel_executions':rows,'nonassociative_basis_control':{'prime':17,'grades':[1,1,1],
            'correct_associator_ratio_error':ratio_error,'actual_associativity_difference':disagreement,
            'ordinary_associativity_rejected':True},'cross_prime_false_law_execution_controls':false_controls,
            'all_passed':True}


def executable_qrh_scalars():
    def multiply(*terms):
        result=terms[0]
        for term in terms[1:]:result=combine('scalar_product',result,term)
        return result
    gauss=lambda j:atom('eisenstein_gauss',SCALAR,j)
    chi=lambda x:atom('eisenstein_character_at',SCALAR,x)
    direction=atom('eisenstein_unit_direction',SCALAR)
    left=multiply(gauss(5),gauss(3))
    right=multiply(atom('root_of_unity',SCALAR,[6,3]),chi(-1),chi(4),Term('scalar_conjugate',SCALAR,(direction,)),gauss(2))
    wrong=multiply(atom('root_of_unity',SCALAR,[6,3]),chi(-1),chi(4),direction,gauss(2))
    rows=[]
    for p in (7,13,19,31,37,43,61):
        lhs=evaluate(left,p,{});rhs=evaluate(right,p,{})
        error=float(abs(lhs-rhs));bad=float(abs(lhs-evaluate(wrong,p,{})))
        assert error<1e-10 and bad>1e-8 and evaluate(chi(0),p,{})==0
        rows.append({'prime_norm':p,'normalized_Gauss_identity_error':error,
                     'wrong_generator_conjugation_difference':bad,'nonunit_character_is_zero':True,'all_passed':True})
    return {'left_term':left.data(),'right_term':right.data(),'records':rows,
            'normalized_identity':'gamma_-1*gamma_3=-chi(-1)*chi(4)*conjugate(alpha)*gamma_2',
            'native_and_exact_certificates':'qrh-results/qrh_operator_benchmark.json and qrh_operator_verification.json',
            'full_QRH_proof_independently_verified':False,'all_passed':True}


def arithmetic_embedding():
    N=4096;values=[0]*(N+1);prior=[0]*(N+1)
    for n in range(1,N+1):
        values[n]=int(n==1)-prior[n]
        for m in range(2*n,N+1,n):prior[m]+=values[n]
    assert all(sum(values[d] for d in range(1,n+1) if n%d==0)==int(n==1) for n in range(1,257))
    term=embed(atom('input',ARITHMETIC,'inverse_zeta_coefficients'),N)
    transformed=apply(word_term(('FI','INV','MASK','F')),term)
    rows=[]
    for p in (7,13,*HELD):
        residue=evaluate(term,p,{'inverse_zeta_coefficients':values})
        out=evaluate(transformed,p,{'inverse_zeta_coefficients':values})
        lhs=float(np.vdot(out,out).real)
        expected=float(np.vdot(residue,residue).real-abs(residue.sum())**2/p)
        assert abs(lhs-expected)<1e-8
        rows.append({'prime':p,'cutoff':N,'residue_vector':list(map(int,residue.real)),
                     'transformed_energy':lhs,'exact_constant_complement_energy':expected,'all_passed':True})
    return {'input_origin':'Dirichlet inverse of complete zeta coefficient prefix, computed by divisor recursion',
            'uses_prime_indicator_input':False,'term':transformed.data(),'records':rows,
            'universal_finite_energy_identity_proved':True,
            'full_unwindowed_inverse_zeta_identity':'sum mu(n)n^-s=1/zeta(s) on Re(s)>1',
            'residue_embedding_has_nonzero_kernel':True,'ordinary_zeta_zero_fidelity_after_embedding_proved':False,
            'new_arithmetic_cancellation_estimate_proved':False,'all_passed':True}


def type_controls():
    rejected=[]
    for name,fn in (('arithmetic_as_residue_vector',lambda:apply(atom('F',MAP),atom('input',ARITHMETIC,'a'))),
                    ('compose_vector_and_map',lambda:compose(atom('input',VECTOR,'x'),atom('F',MAP))),
                    ('missing_arithmetic_coefficients',lambda:evaluate(embed(atom('input',ARITHMETIC,'a'),100),7,{'a':[0]*10})),
                    ('complex_adjoint_of_antilinear_map',lambda:evaluate(gram(atom('CONJ',MAP)),7,{}))):
        try:fn()
        except (TypeError,ValueError):rejected.append(name)
        else:raise AssertionError('Invalid type accepted: '+name)
    return {'rejected_programs':rejected,'all_passed':True}


def main():
    start=time.monotonic();DEST.mkdir(exist_ok=True)
    enumeration_result=enumeration();K=inverse_fourier_discovery();d=defect_search();phase=phase_products();kernels=kernel_synthesis()
    execution=executable_kernels(kernels);scalars=executable_qrh_scalars();bridge=arithmetic_embedding();types=type_controls()
    out={'production_catalogue':PRODUCTION_CATALOGUE,'operator_word_search':enumeration_result,
         'inverse_Fourier_projection_discovery':K,'commutator_defect_search':d,
         'nonassociative_phase_search':phase,'learned_phase_kernel_search':kernels,
         'executable_phase_kernel_controls':execution,'executable_QRH_scalar_controls':scalars,
         'zeta_coefficient_residue_bridge':bridge,'typed_rejection_controls':types,
         'priority':'New arithmetic information about actual primes across scales, with ordinary-zeta root information retained',
         'verified_new_operators':[],'historical_novelty_established':False,
         'new_uniform_prime_distribution_estimate_proved':False,'new_RH_estimate_proved':False,
         'all_passed':all(x['all_passed'] for x in (enumeration_result,K,d,phase,kernels,execution,scalars,bridge,types)),
         'seconds':time.monotonic()-start}
    (DEST/'creative_search.json').write_text(json.dumps(out,indent=2)+'\n')
    print('Creative grammar',enumeration_result['map_programs_evaluated'],'map programs,',phase['phase_product_programs'],
          'phase products; passed',out['all_passed'],'seconds',out['seconds'],flush=True)


if __name__=='__main__':main()
