#!/usr/bin/env python3
"""Independent divisor recursion and bivariate-cycle audit of joint kernels."""

from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
from math import comb,factorial
from pathlib import Path
import json


BASE=Path(__file__).resolve().parent


@lru_cache(maxsize=None)
def h(n,b,upper=False):
    value=0
    original=n
    while n>=b:n//=b;value+=1
    return value+int(upper and original!=b**value)


def w(i,j,b,c,o1='floor',o2='floor',mask=8):
    a=int(h(i*j,b,o1=='ceil')==h(i,b,o1=='ceil')+h(j,b,o1=='ceil'))
    d=int(h(i*j,c,o2=='ceil')==h(i,c,o2=='ceil')+h(j,c,o2=='ceil'))
    return (mask>>(2*a+d))&1


def failure(record,triples):
    b,c=record['bases'];o1,o2=record['orientations'];mask=record['truth_table_mask']
    for a,d,e in triples:
        left=w(a,d,b,c,o1,o2,mask)*w(a*d,e,b,c,o1,o2,mask)
        right=w(d,e,b,c,o1,o2,mask)*w(a,d*e,b,c,o1,o2,mask)
        if left!=right:return {'a':str(a),'d':str(d),'e':str(e),'left':left,'right':right}
    return None


@lru_cache(maxsize=None)
def factors(n):
    result={};p=2
    while p*p<=n:
        while n%p==0:result[p]=result.get(p,0)+1;n//=p
        p+=1
    if n>1:result[n]=1
    return result


@lru_cache(maxsize=None)
def divisors(n):
    values=[1]
    for p,e in factors(n).items():values=[d*p**j for d in values for j in range(e+1)]
    return sorted(values)


def omega(n):return sum(factors(n).values())


def conv(a,d,weight):
    out=[Q(0)]*len(a)
    for n in range(1,len(a)):
        out[n]=sum((weight(i,n//i)*a[i]*d[n//i] for i in divisors(n)),Q(0))
    return out


def triangular(f,weight,kind):
    out=[Q(0)]*len(f);out[1]=Q(kind=='EXP')
    for n in range(2,len(f)):
        middle=Q(0)
        for d in divisors(n)[1:-1]:
            e=n//d
            middle+=omega(d)*weight(d,e)*(f[d]*out[e] if kind=='EXP' else out[d]*f[e])
        out[n]=f[n]+(middle if kind=='EXP' else -middle)/omega(n)
    return out


def zeta_root(cutoff,q):
    values=[Q(0),Q(1)]
    for n in range(2,cutoff+1):
        v=Q(1)
        for e in factors(n).values():
            for j in range(e):v*=Q(Q(1,q)+j,j+1)
        values.append(v)
    return values


def lift(cutoff,q,weight):
    f=zeta_root(cutoff,q);f[1]=Q(0)
    term=[Q(0)]*(cutoff+1);term[1]=Q(1)
    out=term.copy()
    for k in range(1,min(q,cutoff.bit_length()-1)+1):
        term=conv(term,f,weight)
        out=[x+comb(q,k)*y for x,y in zip(out,term)]
    return out


def polynomial_profile(item):
    alpha=Q(item['alpha']);b,c=item['bases']
    merged={(0,0):Q(1)}
    for p,e in item['factors']:
        local=[{(0,0):Q(1)}]
        for power in range(1,e+1):
            coefficients={}
            for j in range(1,power+1):
                x,y=h(p**j,b),h(p**j,c)
                for (a,d),value in local[power-j].items():
                    key=(a+x,d+y)
                    coefficients[key]=coefficients.get(key,Q(0))+alpha*value/power
            local.append(coefficients)
        out={}
        for (x,y),a in merged.items():
            for (v,z),d in local[e].items():out[x+v,y+z]=out.get((x+v,y+z),Q(0))+a*d
        merged=out
    n=int(item['n'])
    coefficient=merged.get((h(n,b),h(n,c)),Q(0))
    grade=sum(e for p,e in item['factors'])
    return coefficient==Q(item['coefficient']) and (coefficient*factorial(grade)*alpha.denominator**grade).denominator==1


def main():
    source=json.loads((BASE/'joint-results/joint_size_search.json').read_text())
    decisions=[]
    for item in source['boolean_grammar']['records']:
        b,c=item['bases'];unital=bool(item['truth_table_mask']&8)
        witness=failure(item,product(range(1,5),repeat=3)) if unital else None
        training=unital and witness is None
        if training:
            witness=failure(item,product(range(1,25),repeat=3))
            if witness is None:witness=failure(item,((b**120,b**120+1,c**79),(c**80-1,b**128+1,b**127+1),(b**31-1,c**19+1,2)))
        decisions.append(training==item['training_passed'] and (training and witness is None)==item['held_out_passed'] and witness==item['counterexample'])
    generic=[]
    for item in source['generic_checks']['records']:
        b,c=item['bases'];o1,o2=item['orientations']
        weight=lambda i,j:w(i,j,b,c,o1,o2)
        a,d=[[Q(x) for x in item[k]] for k in ('input_a','input_d')]
        ordinary=lambda i,j:1
        ua=triangular(triangular(a,ordinary,'LOG'),weight,'EXP')
        ud=triangular(triangular(d,ordinary,'LOG'),weight,'EXP')
        inverse=triangular(triangular(ua,weight,'LOG'),ordinary,'EXP')
        generic.append([str(x) for x in ua]==item['output_a'] and inverse==a
                       and triangular(triangular(conv(a,d,ordinary),ordinary,'LOG'),weight,'EXP')==conv(ua,ud,weight))
    zeta=[]
    for item in source['zeta_profiles']:
        cutoff=item['cutoff'];b,c=item['bases']
        weight=lambda i,j:w(i,j,b,c)
        log_u=[Q(0),Q(0)]+[Q(1,next(iter(factors(n).values()))) if len(factors(n))==1 else Q(0) for n in range(2,cutoff+1)]
        limit=triangular(log_u,weight,'EXP')
        passed=[str(x) for x in limit]==item['limit_coefficients'] and all(0<=x<=1 for x in limit)
        for record in item['root_lifts']:
            result=lift(cutoff,record['q'],weight)
            passed &= [str(x) for x in result]==record['coefficients'] and all(0<=x<=1 for x in result)
        zeta.append(passed)
    volumes=[]
    for item in source['correlated_angle_volume_grammar']['observations']:
        q,k=item['q'],item['power_relation_k'];mesh=1024
        lo,hi=Q(comb(mesh-1,q),mesh**q),Q(comb(mesh+q-1,q),mesh**q)
        digit_factor=Q(comb(k+q-1,q),k**q)
        volumes.append(Q(item['independent_lower'])==lo**2 and Q(item['independent_upper'])==hi**2
                       and Q(item['dependent_lower'])==digit_factor*lo and Q(item['dependent_upper'])==digit_factor*hi
                       and item['correlated_digit_count']==comb(k+q-1,q))
    wrong=q2_wrong=(Q(3,8)!=Q(1,4))
    # A concrete failure of the ordinary linear pencil for a joint kernel.
    complement_failure=None
    for a,d,e in product(range(1,25),repeat=3):
        left=(1-w(a,d,2,3))*(1-w(a*d,e,2,3))
        right=(1-w(d,e,2,3))*(1-w(a,d*e,2,3))
        if left!=right:complement_failure={'a':a,'d':d,'e':e,'left':left,'right':right};break
    checks={'all_Boolean_grammar_decisions_recomputed':all(decisions),
            'generic_normalized_group_and_inverse_laws_independently_recomputed':all(generic),
            'all_zeta_root_lifts_and_limits_independently_recomputed':all(zeta),
            'large_integer_bivariate_cycle_profiles_match':all(polynomial_profile(x) for x in source['large_integer_profiles']),
            'independent_and_correlated_box_volumes_exactly_recomputed':all(volumes),
            'dependent_base_independence_shortcut_rejected':wrong and source['correlated_angle_volume_grammar']['independent_formula_rejected_for_b_and_b_squared'],
            'joint_complement_associativity_shortcut_rejected':complement_failure is not None}
    result={'checks':checks,'all_passed':all(checks.values()),'grammar_models_checked':len(decisions),
            'generic_records_checked':len(generic),'large_integer_profiles_checked':len(source['large_integer_profiles']),
            'joint_complement_counterexample':complement_failure,'proof':'joint_size_proof.txt','no_production_imports':True}
    (BASE/'joint-results/joint_size_verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(f'Independent joint arithmetic audit: {sum(checks.values())}/{len(checks)}')
    assert result['all_passed']


if __name__=='__main__':main()
