#!/usr/bin/env python3
"""Global radix carry transfers, inferred log degree and root-type controls."""

from fractions import Fraction as Q
from functools import lru_cache
from math import factorial,comb
from pathlib import Path
import json
import random
import time

from exact_arithmetic import factorization, formal_log, formal_exp, convolve, normalized_power

BASE=Path(__file__).resolve().parent
DEST=BASE/'radix-results'


def digits(n,b):
    total=0
    while n:
        total+=n%b;n//=b
    return total


@lru_cache(maxsize=None)
def omega(n):
    return sum(factorization(n).values())


def allowed(i,j,b):
    return digits(i,b)+digits(j,b)==digits(i+j,b)


def product(a,c,b):
    out=[Q(0)]*len(a)
    for i in range(1,len(a)):
        if a[i]:
            for j in range(1,(len(a)-1)//i+1):
                if c[j] and allowed(omega(i),omega(j),b):out[i*j]+=a[i]*c[j]
    return out


def EXP(h,b):
    unit=[Q(0)]*len(h);unit[1]=Q(1)
    result=list(unit);term=unit
    bound=max(digits(omega(n),b) for n in range(1,len(h)))
    for k in range(1,bound+1):
        term=[v/k for v in product(term,h,b)]
        result=[v+w for v,w in zip(result,term)]
    return result


def LOG(f,b):
    residual=list(f);residual[1]-=1
    term=[Q(0)]*len(f);term[1]=Q(1);out=[Q(0)]*len(f)
    bound=max(digits(omega(n),b) for n in range(1,len(f)))
    for k in range(1,bound+1):
        term=product(term,residual,b)
        out=[v+Q((-1)**(k+1),k)*w for v,w in zip(out,term)]
    return out


def transfer(f,b):
    return EXP(formal_log(f),b)


def graded_exp(h,b):
    out=[Q(1)]+[Q(0)]*(len(h)-1)
    for n in range(1,len(h)):
        out[n]=sum((k*h[k]*out[n-k] for k in range(1,n+1) if allowed(k,n-k,b)),Q(0))/n
    return out


def choose(x,k):
    value=Q(1)
    for j in range(k):value*=Q(x-j,j+1)
    return value


def polynomial_grammar():
    rows=[];D=40
    for b in (2,3,4,5,7):
        higher=[Q(0)]*(D+1)
        for n,v in {2:Q(2,7),3:Q(-1,5),4:Q(3,11),5:Q(1,6),8:Q(-2,13)}.items():higher[n]=v
        def observation(z):
            h=list(higher);h[1]=Q(z)
            return sum(graded_exp(h,b),Q(0))
        observations=[observation(z) for z in range(9)]
        differences=[];level=observations[:7]
        while level:
            differences.append(level[0]);level=[v-u for u,v in zip(level,level[1:])]
        degree=max(k for k,v in enumerate(differences) if v)
        held=all(sum((choose(z,k)*v for k,v in enumerate(differences)),Q(0))==observation(z) for z in (-3,7,8,11))
        coarse=[higher[b*k] for k in range((D-(b-1))//b+1)]
        recursive=sum(graded_exp(coarse,b),Q(0))/factorial(degree)
        leading=differences[degree]/factorial(degree)
        rows.append({'radix':b,'grade_cutoff':D,'higher_log_coefficients':list(map(str,higher)),
                     'observations':list(map(str,observations)),'Newton_difference_coefficients':list(map(str,differences)),
                     'inferred_polynomial_degree':degree,'held_out_passed':held,
                     'inferred_leading_coefficient':str(leading),'coarse_grade_leading_coefficient':str(recursive),
                     'leading_scale_identity_passed':leading==recursive})
    models=[{'slope':a,'intercept':c,'held_out_passed':all(a*r['radix']+c==r['inferred_polynomial_degree'] for r in rows[3:])}
            for a in range(-3,4) for c in range(-3,4)
            if all(a*r['radix']+c==r['inferred_polynomial_degree'] for r in rows[:3])]
    return {'records':rows,'radix_degree_models_scored':49,'radix_degree_fits':models,
            'finite_graded_polynomial_target':True,'universal_proof':'radix_proof.txt'}


def generic():
    rng=random.Random(2026100730);rows=[]
    for b in (2,3,4,5,7):
        N=128
        f=[Q(0),Q(1)]+[Q(rng.randint(-2,3),rng.randint(1,5)) for _ in range(N-1)]
        g=[Q(0),Q(1)]+[Q(rng.randint(-2,2),rng.randint(1,5)) for _ in range(N-1)]
        S=transfer(f,b);R=transfer(normalized_power(f,Q(1,2)),b)
        checks={'transfer_group_isomorphism':transfer(convolve(f,g),b)==product(S,transfer(g,b),b),
                'closed_inverse':formal_exp(LOG(S,b))==f,
                'reverse_inverse':transfer(formal_exp(LOG(f,b)),b)==f,
                'typed_output_half_root':product(R,R,b)==S,
                'prefix_consistency':transfer(f[:65],b)==S[:65],
                'ordinary_output_half_root_differs':R!=normalized_power(S,Q(1,2))}
        rows.append({'radix':b,'input':list(map(str,f)),'second_input':list(map(str,g)),
                     'output':list(map(str,S)),'checks':checks})
    return {'records':rows,'all_passed':all(all(row['checks'].values()) for row in rows)}


def profiles():
    rows=[];N=4096
    h=[Q(0)]*(N+1)
    for n in range(2,N+1):
        fs=factorization(n)
        if len(fs)==1:h[n]=Q(1,next(iter(fs.values())))
    for b in (2,3,4,5,7):
        for beta in (Q(1),Q(1,2)):
            values=EXP([beta*v for v in h],b)
            rows.append({'radix':b,'beta':str(beta),'encoded_cutoff':N,'coefficients':list(map(str,values)),
                         'dominated_by_ordinary_positive_root_coefficients':all(0<=v<=w for v,w in zip(values,formal_exp([beta*v for v in h]))),
                         'first_squarefree_capacity_zero':values[30]==0 if b==3 else None})
    S3=next(row for row in rows if row['radix']==3 and row['beta']=='1')
    root=normalized_power(list(map(Q,S3['coefficients'][:65])),Q(1,2))
    inp=next(row for row in rows if row['radix']==3 and row['beta']=='1/2')
    control={'radix':3,'index':8,'transfer_of_ordinary_input_half_root':inp['coefficients'][8],
             'ordinary_output_half_root':str(root[8]),'all_passed':Q(inp['coefficients'][8])==Q(1,6) and root[8]==Q(-1,48)}
    return {'records':rows,'ordinary_root_type_control':control,'all_passed':control['all_passed'] and all(row['dominated_by_ordinary_positive_root_coefficients'] for row in rows)}


def main():
    start=time.monotonic();g=polynomial_grammar();laws=generic();zeta=profiles()
    passed=(laws['all_passed'] and zeta['all_passed'] and all(row['held_out_passed'] and row['leading_scale_identity_passed'] for row in g['records'])
            and g['radix_degree_fits']==[{'slope':1,'intercept':-1,'held_out_passed':True}])
    wrong={'radix':4,'degree_triple':[1,1,2],
           'binomial_nondivisibility_left':int(comb(2,1)%4!=0)*int(comb(4,2)%4!=0),
           'binomial_nondivisibility_right':int(comb(3,1)%4!=0)*int(comb(4,1)%4!=0),
           'actual_radix_digit_kernel_parenthesizations':[int(allowed(1,1,4))*int(allowed(2,2,4)),int(allowed(1,2,4))*int(allowed(1,3,4))],
           'nonassociative_replacement_rejected':True}
    out={'log_polynomial_grammar':g,'generic_transfer_laws':laws,'zeta_profiles':zeta,
         'composite_radix_binomial_filter_negative_control':wrong,
         'universal_leading_coefficient_identity':'beta**(b-1)/(b-1)! * F_(b,beta/b)(b*s)',
         'ordinary_output_root_fidelity':'rejected','counts_as_new_primitive':False,
         'historical_novelty_established':False,'new_RH_estimate_proved':False,
         'all_passed':passed,'seconds':time.monotonic()-start}
    DEST.mkdir(exist_ok=True)
    (DEST/'radix_search.json').write_text(json.dumps(out,indent=2)+'\n')
    print('Global radix exact search:',passed,'seconds',out['seconds'],flush=True)
    assert passed


if __name__=='__main__':main()
