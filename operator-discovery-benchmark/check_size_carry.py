#!/usr/bin/env python3
"""Independent audit: divisor recursions and prime-cycle height polynomials.

No production helper is imported. All floors use repeated integer
division. Generic LOG/EXP use Euler-degree triangular recursions rather
than finite powers; finite root lifts use a separate binomial evaluator.
"""

from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
from math import comb, factorial, gcd, isqrt
from pathlib import Path
import json


BASE=Path(__file__).resolve().parent


def height(n,base):
    value=0
    while n>=base:
        n//=base
        value+=1
    return value


def selected_weight(i,j,base,orientation):
    if orientation=='floor':return int(height(i*j,base)==height(i,base)+height(j,base))
    upper=lambda n:height(n,base)+int(n!=base**height(n,base))
    return int(upper(i*j)==upper(i)+upper(j))


def restrict_powers(values,base):
    result=[Q(0)]*len(values)
    for n in range(1,len(values)):
        m=n
        while m%base==0:m//=base
        if m==1:result[n]=values[n]
    return result


@lru_cache(maxsize=250000)
def factors(n):
    out={}
    p=2
    while p*p<=n:
        while n%p==0:
            out[p]=out.get(p,0)+1
            n//=p
        p+=1
    if n>1:
        out[n]=1
    return out


def degree(n):
    return sum(factors(n).values())


@lru_cache(maxsize=250000)
def phi(n,kind,p):
    if kind in ('floor_log','ceil_log','nearest_log'):
        h=height(n,p)
        return h+(int(n!=p**h) if kind=='ceil_log' else int(n*n>=p**(2*h+1)) if kind=='nearest_log' else 0)
    if kind=='floor_quotient':return n//p-1//p
    if kind=='remainder':return n%p-1%p
    if kind=='nonunit_modulus':return -int(gcd(n,p)>1)
    if kind=='omega':return degree(n)
    if kind=='v2':
        out=0
        while n%2==0:n//=2;out+=1
        return out
    if kind=='digit_sum':
        out=0
        while n:n,digit=divmod(n,p);out+=digit
        return out-1
    if kind=='floor_root':
        if p==2:return isqrt(n)-1
        lower,upper=0,1
        while upper**p<=n:upper*=2
        while upper-lower>1:
            middle=(lower+upper)//2
            if middle**p<=n:lower=middle
            else:upper=middle
        return lower-1
    if kind=='mixed_logs':return height(n,2)+p*height(n,3)
    raise ValueError(kind)


def w(model,a,b):
    if model['family']=='direct':
        rule=model['predicate']
        if rule=='coprime_sum_product':return int(gcd(a+b,a*b)==1)
        if a==1 or b==1:return 1
        if rule=='shifted_coprimality':return int(gcd(a-1,b-1)==1)
        return int(a%model['parameter']+b%model['parameter']<model['parameter'])
    kind,p=model['feature'],model['parameter']
    x=phi(a*b,kind,p)-phi(a,kind,p)-phi(b,kind,p)
    rule=model['predicate']
    if rule=='zero':return int(x==0)
    if rule=='nonnegative':return int(x>=0)
    if rule=='nonpositive':return int(x<=0)
    if rule=='even':return int(x%2==0)
    return int(-1<=x<=1)


def first_failure(model,triples):
    for a,b,c in triples:
        left,right=w(model,a,b)*w(model,a*b,c),w(model,b,c)*w(model,a,b*c)
        if left!=right:return {'a':str(a),'b':str(b),'c':str(c),'left':left,'right':right}
    return None


@lru_cache(maxsize=None)
def divisors(n):
    out=[1]
    for p,e in factors(n).items():
        out=[d*p**j for d in out for j in range(e+1)]
    return sorted(out)


def triangular(values,weight,operation):
    out=[Q(0)]*len(values)
    out[1]=Q(operation=='EXP')
    for n in range(2,len(values)):
        total=Q(0)
        for d in divisors(n)[1:-1]:
            e=n//d
            total+=degree(d)*weight(d,e)*(values[d]*out[e] if operation=='EXP' else out[d]*values[e])
        out[n]=values[n]+(total/degree(n) if operation=='EXP' else -total/degree(n))
    return out


def conv(a,b,weight):
    return [Q(0)]+[sum((weight(d,n//d)*a[d]*b[n//d] for d in divisors(n)),Q(0)) for n in range(1,len(a))]


def root_zeta(cutoff,q):
    out=[Q(0),Q(1)]
    for n in range(2,cutoff+1):
        value=Q(1)
        for e in factors(n).values():
            for j in range(e):value*=Q(1,q)+j;value/=j+1
        out.append(value)
    return out


def root_lift(cutoff,q,weight):
    residual=root_zeta(cutoff,q)
    residual[1]=Q(0)
    term=[Q(0)]*(cutoff+1);term[1]=Q(1)
    out=term[:]
    for k in range(1,min(q,cutoff.bit_length()-1)+1):
        term=conv(term,residual,weight)
        out=[a+comb(q,k)*b for a,b in zip(out,term)]
    return out


def height_polynomial_profile(item):
    base,alpha=item['base'],Q(item['alpha'])
    full={0:Q(1)}
    total_grade=0
    for p,e in item['factorization']:
        total_grade+=e
        rows=[{0:Q(1)}]
        for k in range(1,e+1):
            row={}
            for j in range(1,k+1):
                shift=height(p**j,base)
                for index,value in rows[k-j].items():row[index+shift]=row.get(index+shift,Q(0))+alpha*value/k
            rows.append(row)
        next_full={}
        for i,x in full.items():
            for j,y in rows[e].items():next_full[i+j]=next_full.get(i+j,Q(0))+x*y
        full=next_full
    n=int(item['n'])
    coefficient=full.get(height(n,base),Q(0))
    integer_scaled=coefficient*factorial(total_grade)*alpha.denominator**total_grade
    return coefficient==Q(item['coefficient']) and integer_scaled.denominator==1


def main():
    source=json.loads((BASE/'size-results/size_carry_search.json').read_text())
    search=source['kernel_grammar']
    decisions=[]
    boundary=[[int(x) for x in row] for row in search['exact_large_power_boundary_stresses']]
    for model in search['records']:
        failure=first_failure(model,product(range(1,5),repeat=3))
        if failure:
            decisions.append(not model['training_passed'] and failure==model['first_counterexample'])
            continue
        failure=first_failure(model,product(range(1,25),repeat=3))
        if failure is None and model['large_boundary_stress_performed']:
            failure=first_failure(model,boundary)
        decisions.append(model['training_passed'] and (failure is None)==model['held_out_passed'] and failure==model['first_counterexample'])
    print(f"Independent grammar decisions: {sum(decisions)}/{len(decisions)}",flush=True)
    generic=[]
    for record in source['exact_operator_checks']['records']:
        a,b=[[Q(v) for v in record[key]] for key in ('input_a','input_b')]
        base=record['base']; orientation=record['orientation']
        weight=lambda i,j:selected_weight(i,j,base,orientation)
        ordinary=lambda i,j:1
        ua=triangular(triangular(a,ordinary,'LOG'),weight,'EXP')
        inverse=triangular(triangular(ua,weight,'LOG'),ordinary,'EXP')
        ub=triangular(triangular(b,ordinary,'LOG'),weight,'EXP')
        generic.append([str(v) for v in ua]==record['output_a'] and inverse==a
                       and triangular(triangular(conv(a,b,ordinary),ordinary,'LOG'),weight,'EXP')==conv(ua,ub,weight))
    zeta=[]
    integer_coefficients=True
    for record in source['zeta_profiles']:
        cutoff,base,orientation=record['cutoff'],record['base'],record['orientation']
        weight=lambda i,j:selected_weight(i,j,base,orientation)
        h=[Q(0),Q(0)]+[Q(1,next(iter(factors(n).values()))) if len(factors(n))==1 else Q(0) for n in range(2,cutoff+1)]
        limit=triangular(h,weight,'EXP')
        passed=[str(v) for v in limit]==record['limit_coefficients']
        integer_coefficients &= all((factorial(degree(n))*limit[n]).denominator==1 for n in range(1,cutoff+1))
        for item in record['root_lifts']:
            values=root_lift(cutoff,item['order'],weight)
            passed &= [str(v) for v in values]==item['coefficients'] and all(0<=v<=1 for v in values)
        zeta.append(passed)
    paired=[]
    for record in source['paired_root_identity']['records']:
        cutoff,base,beta=record['cutoff'],record['base'],Q(record['beta'])
        g=root_zeta(cutoff,beta.denominator)
        lower=conv(g,g,lambda i,j:selected_weight(i,j,base,'floor'))
        upper=conv(g,g,lambda i,j:selected_weight(i,j,base,'ceil'))
        ordinary=conv(g,g,lambda i,j:1)
        resonant=restrict_powers(ordinary,base)
        value=[(a+b-c+d)/2 for a,b,c,d in zip(lower,upper,ordinary,resonant)]
        target=conv(g,restrict_powers(g,base),lambda i,j:1)
        passed=value==target and [str(x) for x in lower]==record['lower_square_coefficients']
        passed &= [str(x) for x in upper]==record['upper_square_coefficients'] and [str(x) for x in value]==record['paired_coefficients']
        paired.append(passed)
    generic_paired=[]
    generic_bilinear=[]
    for record in source['exact_operator_checks']['records']:
        g=[Q(v) for v in record['input_a']];base=record['base']
        lower=conv(g,g,lambda i,j:selected_weight(i,j,base,'floor'))
        upper=conv(g,g,lambda i,j:selected_weight(i,j,base,'ceil'))
        ordinary=conv(g,g,lambda i,j:1)
        resonant=restrict_powers(ordinary,base)
        generic_paired.append([(a+b-c+d)/2 for a,b,c,d in zip(lower,upper,ordinary,resonant)]
                              ==conv(g,restrict_powers(g,base),lambda i,j:1))
        other=[Q(v) for v in record['input_b']]
        low_ab=conv(g,other,lambda i,j:selected_weight(i,j,base,'floor'))
        high_ab=conv(g,other,lambda i,j:selected_weight(i,j,base,'ceil'))
        ordinary_ab=conv(g,other,lambda i,j:1)
        left_res=conv(restrict_powers(g,base),other,lambda i,j:1)
        right_res=conv(g,restrict_powers(other,base),lambda i,j:1)
        out_res=restrict_powers(ordinary_ab,base)
        generic_bilinear.append([a+b for a,b in zip(low_ab,high_ab)]
                                ==[a+b+c-d for a,b,c,d in zip(ordinary_ab,left_res,right_res,out_res)])
    false_resonance_hom=[]
    for base,a,b in ((4,2,2),(6,2,3),(12,3,4)):
        f,g=[[Q(0)]*(base+1) for _ in range(2)]
        f[1]=g[1]=Q(1)
        f[a]=g[b]=Q(1)
        false_resonance_hom.append(restrict_powers(conv(f,g,lambda i,j:1),base)
                                  !=conv(restrict_powers(f,base),restrict_powers(g,base),lambda i,j:1))
    impulse=[Q(0)]*9
    impulse[2]=Q(1)
    extract=lambda values:[values[n*n] for n in range(isqrt(len(values)-1)+1)]
    extraction_fails=extract(conv(impulse,impulse,lambda i,j:selected_weight(i,j,2,'floor')))
    extraction_target=conv(extract(impulse),extract(impulse),lambda i,j:selected_weight(i,j,2,'floor'))
    carry_only_associative=all((1-selected_weight(a,b,base,orientation))*(1-selected_weight(a*b,c,base,orientation))
                              ==(1-selected_weight(b,c,base,orientation))*(1-selected_weight(a,b*c,base,orientation))
                              for base,orientation in product((2,3,6),('floor','ceil'))
                              for a,b,c in product(range(1,17),repeat=3))
    collapsed=[]
    for record in source['floor_quotient_collapse_controls']:
        m=record['quotient_modulus'];cutoff=512
        source_log=[Q(0),Q(0)]+[Q(1,next(iter(factors(n).values()))) if len(factors(n))==1 else Q(0) for n in range(2,cutoff+1)]
        f=lambda n:n//m-1//m
        got=triangular(source_log,lambda i,j:int(f(i*j)==f(i)+f(j)),'EXP')
        collapsed.append(all(got[n]==source_log[n] for n in range(2*m+3,cutoff+1)))
    checks={'every_kernel_search_decision_recomputed':all(decisions),
            'generic_unit_group_laws_independently_recomputed':all(generic),
            'all_zeta_coefficients_and_integer_root_lifts_recomputed':all(zeta),
            'Omega_factorial_clears_all_limit_coefficient_denominators':integer_coefficients,
            'all_large_integer_divisor_profiles_match_cycle_height_polynomials':all(height_polynomial_profile(x) for x in source['large_integer_sparse_divisor_profiles']),
            'paired_root_identity_all_bases_and_betas_recomputed':all(paired),
            'paired_identity_on_unrelated_generic_inputs':all(generic_paired),
            'full_bilinear_paired_identity_on_unrelated_inputs':all(generic_bilinear),
            'composite_base_resonance_homomorphism_rejected':all(false_resonance_hom),
            'carry_only_associativity_recomputed':carry_only_associative,
            'floor_quotient_family_collapses_to_classical_log_tail':all(collapsed),
            'actual_prime_relabeling_invariance_fails':height(6,2)==height(2,2)+height(3,2) and height(35,2)!=height(5,2)+height(7,2),
            'ordinary_exponent_extraction_is_not_endomorphism':extraction_fails!=extraction_target,
            'known_unitary_calibration_matches':all(int(gcd(a+b,a*b)==1)==int(gcd(a,b)==1) for a,b in product(range(1,129),repeat=2))}
    result={'checks':checks,'grammar_models_checked':len(decisions),'generic_records_checked':len(generic),
            'large_integer_cycle_profiles_checked':len(source['large_integer_sparse_divisor_profiles']),
            'all_passed':all(checks.values()),'proof':'size_carry_proof.txt','novelty_not_certified':True}
    (BASE/'size-results/size_carry_verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(f"Independent size audit: {sum(checks.values())}/{len(checks)} gates")
    assert result['all_passed']


if __name__=='__main__':main()
