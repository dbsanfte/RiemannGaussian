#!/usr/bin/env python3
"""Search Boolean compositions of size kernels and correlated-angle laws."""

from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
from math import factorial,comb
from pathlib import Path
import json
import random
import time

from exact_arithmetic import sequence,unit,convolve,formal_log,normalized_power
from size_carry_search import algebra_exp,algebra_log


BASE=Path(__file__).resolve().parent
PAIRS=((2,3),(2,5),(2,6),(2,4),(3,9))


@lru_cache(maxsize=None)
def height(n,b,orientation='floor'):
    h,power=0,1
    while power*b<=n:power*=b;h+=1
    return h+int(orientation=='ceil' and power!=n)


@lru_cache(maxsize=None)
def pattern(a,d,b,c,o1,o2):
    x=int(height(a*d,b,o1)==height(a,b,o1)+height(d,b,o1))
    y=int(height(a*d,c,o2)==height(a,c,o2)+height(d,c,o2))
    return 2*x+y


def weight(a,d,b,c,o1='floor',o2='floor',mask=8):
    return (mask>>pattern(a,d,b,c,o1,o2))&1


def first_failure(b,c,o1,o2,mask,triples):
    for a,d,e in triples:
        left=weight(a,d,b,c,o1,o2,mask)*weight(a*d,e,b,c,o1,o2,mask)
        right=weight(d,e,b,c,o1,o2,mask)*weight(a,d*e,b,c,o1,o2,mask)
        if left!=right:return {'a':str(a),'d':str(d),'e':str(e),'left':left,'right':right}
    return None


def boolean_search():
    records=[]
    for (b,c),o1,o2,mask in product(PAIRS,('floor','ceil'),('floor','ceil'),range(16)):
        unital=bool(mask&8)
        failure=first_failure(b,c,o1,o2,mask,product(range(1,5),repeat=3)) if unital else None
        training=unital and failure is None
        boundary=((b**120,b**120+1,c**79),(c**80-1,b**128+1,b**127+1),(b**31-1,c**19+1,2))
        if training:
            failure=first_failure(b,c,o1,o2,mask,product(range(1,25),repeat=3))
            if failure is None:failure=first_failure(b,c,o1,o2,mask,boundary)
        records.append({'bases':[b,c],'orientations':[o1,o2],'truth_table_mask':mask,'unit_constraint_passed':unital,
                        'training_passed':training,'held_out_passed':training and failure is None,'counterexample':failure})
    return {'models_scored':len(records),'training_range':[1,4],'held_out_range':[1,24],
            'large_integer_boundary_rule':'(b^120,b^120+1,c^79),(c^80-1,b^128+1,b^127+1),(b^31-1,c^19+1,2)',
            'training_fits':sum(x['training_passed'] for x in records),'held_out_survivors':sum(x['held_out_passed'] for x in records),
            'records':records,'finite_fits_are_not_universal_proofs':True,
            'selected_universal_kernel':'Boolean AND, truth table mask 8; associative identities of the two kernels multiply'}


def joint_product(a,d,b,c,o1='floor',o2='floor'):
    if len(a)!=len(d):raise ValueError('Equal explicit cutoffs required')
    result=[Q(0)]*len(a)
    for i in range(1,len(a)):
        if a[i]:
            for j in range(1,(len(a)-1)//i+1):
                if d[j] and weight(i,j,b,c,o1,o2):result[i*j]+=a[i]*d[j]
    return result


def transfer(f,b,c,o1='floor',o2='floor'):
    return algebra_exp(formal_log(f),lambda a,d:joint_product(a,d,b,c,o1,o2))


def lift(f,q,b,c):
    root=normalized_power(f,Q(1,q))
    out=unit(len(f)-1)
    for _ in range(q):out=joint_product(out,root,b,c)
    return out


def generic_checks():
    rng=random.Random(2026100703)
    records=[]
    for cutoff in (32,96):
        a,d=[sequence([1]+[Q(rng.randint(-3,3),rng.randint(1,7)) for _ in range(cutoff-1)]) for _ in range(2)]
        for (b,c),o1,o2 in product(((2,3),(2,4),(2,6)),('floor','ceil'),('floor','ceil')):
            prod=lambda x,y:joint_product(x,y,b,c,o1,o2)
            ta,td=transfer(a,b,c,o1,o2),transfer(d,b,c,o1,o2)
            inverse=lambda f:algebra_exp(algebra_log(f,prod),convolve)
            laws={'unit_group_transfer':transfer(convolve(a,d),b,c,o1,o2)==prod(ta,td),
                  'inverse':inverse(ta)==a,'prefix':ta[:cutoff//2+1]==transfer(a[:cutoff//2+1],b,c,o1,o2)}
            records.append({'bases':[b,c],'orientations':[o1,o2],'cutoff':cutoff,'input_a':[str(x) for x in a],
                            'input_d':[str(x) for x in d],'output_a':[str(x) for x in ta],'laws':laws})
    return {'records':records,'all_passed':all(all(x['laws'].values()) for x in records)}


def zeta_checks(cutoff=512):
    u=sequence([1]*cutoff)
    records=[]
    for b,c in PAIRS:
        limit=transfer(u,b,c)
        lifts=[]
        for q in (2,3,4,8,16):
            output=lift(u,q,b,c)
            lifts.append({'q':q,'coefficients':[str(x) for x in output],'bounded_by_one':all(0<=v<=1 for v in output)})
        records.append({'bases':[b,c],'cutoff':cutoff,'limit_coefficients':[str(x) for x in limit],
                        'limit_bounded_by_one':all(0<=v<=1 for v in limit),'root_lifts':lifts})
    return records


def sparse_profile(factors,b,c,alpha):
    divisors=[(1,0)]
    for p,e in factors.items():divisors=[(n*p**j,grade+j) for n,grade in divisors for j in range(e+1)]
    values={1:Q(1)}
    for n,grade in sorted(divisors):
        if n==1:continue
        total=Q(0)
        for p,e in factors.items():
            for j in range(1,e+1):
                power=p**j
                if n%power:break
                if weight(power,n//power,b,c):total+=values[n//power]
        values[n]=Q(alpha)*total/grade
    n=max(values)
    return {'factors':[[p,e] for p,e in factors.items()],'n':str(n),'bases':[b,c],'alpha':str(alpha),
            'explicit_divisor_count':len(divisors),'coefficient':str(values[n])}


def simplex_boxes(q,mesh):
    coefficients=[1]+[0]*(mesh-1)
    for _ in range(q):
        total=0
        updated=[]
        for value in coefficients:total+=value;updated.append(total)
        coefficients=updated
    return Q(sum(coefficients[:max(0,mesh-q)]),mesh**q),Q(sum(coefficients),mesh**q)


def dependent_digit_count(q,k):
    values=[1]+[0]*(k-1)
    for _ in range(q):
        updated=[];total=0
        for x in values:total+=x;updated.append(total)
        values=updated
    return sum(values)


def volume_search():
    observations=[]
    for q,k in product((2,3,4,8,12,16),(2,3,5,7)):
        low,high=simplex_boxes(q,1024)
        factor=Q(dependent_digit_count(q,k),k**q)
        observations.append({'q':q,'power_relation_k':k,'independent_lower':str(low**2),'independent_upper':str(high**2),
                             'dependent_lower':str(factor*low),'dependent_upper':str(factor*high),
                             'correlated_digit_count':dependent_digit_count(q,k)})
    models=list(product((-2,-1,0,1,2),(-1,0,1),(-1,0,1),(0,1,2),(Q(1,2),Q(1),Q(2))))
    training=[x for x in observations if x['q'] in (2,3,4) and x['power_relation_k'] in (2,3)]
    fits=[]
    for shift,exponent,power,factorial_power,scale in models:
        def model(q,k):
            top=k+q+shift
            if top<q:return None
            return scale*Q(comb(top,q))**exponent*Q(k)**(power*q)/Q(factorial(q))**factorial_power
        if all((v:=model(x['q'],x['power_relation_k'])) is not None and Q(x['dependent_lower'])<=v<=Q(x['dependent_upper']) for x in training):
            failures=[x for x in observations if (v:=model(x['q'],x['power_relation_k'])) is None or not Q(x['dependent_lower'])<=v<=Q(x['dependent_upper'])]
            fits.append({'binomial_shift':shift,'binomial_exponent':exponent,'k_exponent_per_q':power,
                         'factorial_denominator_power':factorial_power,'scale':str(scale),'held_out_passed':not failures})
    return {'models_scored':len(models),'observations':observations,'training_fits':fits,
            'survivors':[x for x in fits if x['held_out_passed']],
            'independent_law':'1/(q!)^2','dependent_law':'binomial(k+q-1,q)/(k^q*q!)',
            'independent_formula_rejected_for_b_and_b_squared':all(Q(x['dependent_lower'])>Q(1,factorial(x['q'])**2)
                                                                 for x in observations if x['power_relation_k']==2)}


def main():
    started=time.monotonic()
    output=BASE/'joint-results';output.mkdir(exist_ok=True)
    search=boolean_search()
    print(f'Boolean kernel grammar: {search["models_scored"]}, training={search["training_fits"]}, fresh={search["held_out_survivors"]}',flush=True)
    generic=generic_checks();zeta=zeta_checks();volumes=volume_search()
    sparse=[sparse_profile(f,b,c,alpha) for f in ({2:11,3:7},{3:9,7:5},{2:10,11:6})
            for b,c in ((2,3),(2,4),(2,6)) for alpha in (Q(1),Q(1,2),Q(3,2))]
    result={'boolean_grammar':search,'generic_checks':generic,'zeta_profiles':zeta,'correlated_angle_volume_grammar':volumes,
            'large_integer_profiles':sparse,'selected_definition':'K_(b,c)=K_floor,b AND K_floor,c; V=EXP_K LOG_D',
            'absolute_zeta_domain':'Re(s)>1, every finite q lift and root-order limit',
            'two_independent_bases_Abelian_law':'epsilon^alpha*L_q(1+epsilon+i*(m*tau_b+n*tau_c)) -> A_q(m)*A_q(n)',
            'natural_boundary_Re_s_eq_one_proved_for_finite_q_ge_2':True,
            'multiplicative_independence_required':True,'arbitrary_many_inverse_logs_independence_claimed':False,
            'paired_single_base_identity_not_invalidated':True,'counts_as_new_primitive':False,
            'historical_originality':'Unresolved; Boolean intersection and abstract LOG/EXP transfer are known constructions',
            'proof':'joint_size_proof.txt',
            'all_passed':generic['all_passed'] and all(x['limit_bounded_by_one'] and all(y['bounded_by_one'] for y in x['root_lifts']) for x in zeta)
                         and volumes['independent_formula_rejected_for_b_and_b_squared'],
            'elapsed_seconds':time.monotonic()-started}
    (output/'joint_size_search.json').write_text(json.dumps(result,indent=2)+'\n')
    print(f'Joint exact search: all={result["all_passed"]}, elapsed={result["elapsed_seconds"]:.2f}s')
    assert result['all_passed']


if __name__=='__main__':main()
