"""Structural tests, not factor-success fixtures. Standard library only."""
from fractions import Fraction as F
from itertools import product
from math import prod
import argparse,json
import source_layout as sl
from source_parameters import Parameters,check_stats
from source_factor_solver import count

def independent_operator(U,t,g):
    # Dense projector elementary-symmetric recurrence, independent of subset differences.
    joint=U.joints[t,g];n=len(joint);index={u:i for i,u in enumerate(joint)}
    I=[[F(i==j) for j in range(n)] for i in range(n)]
    def add(A,B):return [[a+b for a,b in zip(x,y)] for x,y in zip(A,B)]
    def mul(A,B):return [[sum(A[i][k]*B[k][j] for k in range(n)) for j in range(n)] for i in range(n)]
    E=[I]+[[[F(0)]*n for _ in range(n)] for _ in range(U.p.R-1)]
    Sprod=I
    for a in range(U.p.Q):
        if a==t:continue
        S=[[F(index[sl.swap_positions(u,(a,))]==j) for j in range(n)] for u in joint]
        P=[[ (I[i][j]-S[i][j])/2 for j in range(n)] for i in range(n)]
        for j in range(U.p.R-1,0,-1):E[j]=add(E[j],mul(P,E[j-1]))
        Sprod=mul(Sprod,S)
    C=[[sum(U.cs[k]*E[k][i][j] for k in range(U.p.R)) for j in range(n)] for i in range(n)]
    matrix=mul(Sprod,C)
    for i,u in enumerate(joint):
        for j,y in enumerate(joint):assert matrix[i][j]*U.denominator==U.N[t,g,u].get(y,0)
    return n*n

def run():
    results=[]
    for Q,R in [(2,1),(3,2)]:
        U=sl.Universal(Parameters(2,Q,R,F(1,4)),sl.Work())
        checks=sum(independent_operator(U,t,g) for t in range(Q) for g in range(2))
        results.append(dict(test='independent_dense_projectors',Q=Q,R=R,entries=checks))
    words=tuple(product(range(2),repeat=2));p=Parameters(2,2,1,F(1,4));frozen=sl.frozen_counter()
    fixtures=[('one_complete_copy',4,((0,1,2,3),)*4,(words,words)),
      ('complete_plus_leftover',4,((0,1,2,3),)*4+((0,),),(words,words+(words[0],))),
      ('identity_leftovers_repeated_owner',3,((0,1),(1,2)),None),
      ('empty_factor',2,((0,1),()),None)]
    for name,n,scopes,labels in fixtures:
        layout=sl.construct_layout(n,scopes,p,labels=labels,require_guard=False)
        factors=tuple(frozen.Factor(scope,lambda bits,k=k:F(int(sum(bits)%3!=1))) for k,scope in enumerate(scopes))
        # Literal original integer rows, not normalized rational measurement vectors.
        for key,indices in layout.selected_indices.items():
            assert layout.measurement_rows(*key)==tuple(layout.raw_constraints[key][i] for i in indices)
        actual=frozen.count(n,factors,layout);expected=frozen.direct_count(n,factors)
        assert actual.value==expected.value
        results.append(dict(test=name,n=n,M=sum(map(len,scopes)),block_count=layout.block_count,
          leftovers=len(layout.leftovers),value=str(actual.value),setup=layout.work.output(),counter=actual.stats))
    # Independent enumeration of conditional completions (small table only).
    n=2;scopes=((0,1),);work=sl.Work();av,df,history=sl.computed_words(n,scopes,p,work)
    def score(seq):
        return sl.conditional_score(n,scopes,p,{i:x for i,x in enumerate(seq[:n])},{i:x for i,x in enumerate(seq[n:])})
    for depth in range(4):
        fixed=(av+df)[:depth]
        completions=tuple(product(words,repeat=3-depth))
        brute=sum(score(fixed+tail) for tail in completions)/len(completions)
        assert brute==score(fixed)
    results.append(dict(test='conditional_mean_exhaustive_completion',history=list(map(str,history))))
    factors=(frozen.Factor((0,1),lambda a:int(a[0]!=a[1])),)
    fallback=count(2,factors);assert fallback['method']=='explicit_invalid_guard_exhaustive_fallback'
    assert fallback['result']['value_numerator']==2
    # Invalid guard must be checked before either words or universal matrices.
    old_words,old_universal=sl.computed_words,sl.Universal
    def forbidden(*args,**kwargs):raise AssertionError('allocation before guard')
    sl.computed_words=sl.Universal=forbidden
    try:
        try:sl.construct_layout(2,((0,1),),p)
        except ValueError as exc:assert 'guard failed' in str(exc)
        else:raise AssertionError('invalid guard accepted')
    finally:sl.computed_words,sl.Universal=old_words,old_universal
    results.append(dict(test='invalid_guard_precedes_all_auxiliary_allocation',accepted=True))
    # Guard-only enormous numeric instance: never allocate its incidence list or D matrix.
    n=2**100000;guard=check_stats(n,2*n,2,2**75000,Parameters(2,4096,1024,F(1,64)))
    assert guard['accepted'];results.append(dict(test='strong_guard_exact_integer_only',n_bit_length=n.bit_length(),accepted=True))
    results.append(dict(test='early_invalid_guard_fallback',result=fallback))
    return dict(status='PASS',scope='structural algebra and small exact tensor counts; no factoring campaign',tests=results)

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--output',default='source-tests.json');args=parser.parse_args()
    result=run()
    with open(args.output,'w') as f:json.dump(result,f,indent=2)
    print(json.dumps(dict(status=result['status'],tests=len(result['tests']),output=args.output)))
