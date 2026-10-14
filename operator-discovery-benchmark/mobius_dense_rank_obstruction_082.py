"""Geometry-only exact rational interval invention for dense rank-one duals.
No Mobius signs, source evaluation, or dense producer grouping is accessed.
"""
from fractions import Fraction as Q
from math import gcd
from flint import fmpq_mat, fmpz
import check_mobius_dense_completion_082 as C
MAX_DENOMINATOR=512
MAX_POINTS=200000
MAX_BITS=100000


def _ceil(q):return -((-q.numerator)//q.denominator)


def _threshold_power(value,exponent,m):
    # u**(b-a) >= value**b, computed prospectively and exactly.
    a,b=exponent.numerator,exponent.denominator;k=b-a
    if k<=0:raise ValueError('sublinear exponent required')
    bits=b*(value.numerator.bit_length()+value.denominator.bit_length())
    if bits>MAX_BITS:raise C.ResourceLimit('threshold power bit gate')
    m.charge(bits+k.bit_length());num=value.numerator**b;den=value.denominator**b
    root=int(fmpz(num//den).root(k))
    return root if root**k*den>=num else root+1


def interval_threshold(p,row,m):
    l,r=Q(row['left']),Q(row['right']);length=r-l
    threshold=max(1,_ceil(24/length)**2,_ceil(2/l))
    cap=Q(1,p['kernel'][0][0])
    for (s,e),v in zip(p['profiles'],row['profiles']):
        if e==1:
            k=min(s,cap);margin=k/r-v
            if margin<=0 or not k/l<v+1:raise ValueError('interval floor margins must be strict')
            threshold=max(threshold,int(1/(l*margin))+1)
        else:
            if v!=0:raise ValueError('sublinear limiting profile must vanish')
            threshold=max(threshold,_threshold_power(2*s/l,e,m))
    if threshold.bit_length()>MAX_BITS:raise C.ResourceLimit('threshold integer bit gate')
    return threshold


def _cell(p,x):
    cap=Q(1,p['kernel'][0][0]);lo=Q(0);hi=cap;source=[];profiles=[]
    for i in range(p['memory']+1):
        source.append(sum((w for d,w in p['kernel'] if x<Q(1,2**i*d)),Q(0)))
        for d,_ in p['kernel']:
            cut=Q(1,2**i*d)
            if x==cut:return None
            if cut<x:lo=max(lo,cut)
            else:hi=min(hi,cut)
    for s,e in p['profiles']:
        if e<1:profiles.append(0);continue
        k=min(s,cap);v=int(k/x)
        if k/x==v:return None
        profiles.append(v);lo=max(lo,k/(v+1))
        if v:hi=min(hi,k/v)
    if not lo<x<hi:return None
    l=(lo+x)/2;r=(x+hi)/2
    return dict(left=str(l),right=str(r),profiles=profiles,source=list(map(str,source)))


def _solve(rows,dim,nprofiles,m):
    n=len(rows);features=1+(dim-1)+nprofiles
    matrix=[[Q(row['source'][i]) for row in rows] for i in range(dim)]
    matrix += [[Q(row['profiles'][j]) for row in rows] for j in range(nprofiles)]
    matrix=[r+[Q(int(i==0))] for i,r in enumerate(matrix)]
    values=[q for r in matrix for q in r]
    if max((max(q.numerator.bit_length(),q.denominator.bit_length()) for q in values),default=1)>4096:raise C.ResourceLimit('matrix entry bit gate')
    m.reserve(16384+1024*features*(n+1));m.charge(features*(n+1)*min(features,n+1)*100)
    R,rank=fmpq_mat([[str(q) for q in r] for r in matrix]).rref();answer=[Q(0)]*n
    for i in range(rank):
        pivot=next((j for j in range(n+1) if R[i,j]),None)
        if pivot==n:return None
        if pivot is not None:answer[pivot]=Q(str(R[i,n]))
    if max((max(t.numerator.bit_length(),t.denominator.bit_length()) for t in answer),default=1)>4096:raise C.ResourceLimit('nullvector rational bit gate')
    # Verify reconstruction independently of native RREF layout.
    for i,r in enumerate(matrix):
        if sum((r[j]*answer[j] for j in range(n)),Q(0))!=r[-1]:raise ArithmeticError('exact reconstruction mismatch')
    return answer


def discover(program,max_denominator=MAX_DENOMINATOR,meter=None):
    m=meter or C.Meter();out={};points=0
    try:
        p=C.parse_program(program,m)
        if sum((w for _,w in p['kernel']),Q(0))!=0:raise ValueError('registered zero-sum kernel scope')
        base=[(4,Q(-1)),(5,Q(1)),(8,Q(1)),(10,Q(-1))]
        extended=sorted(base+[(12,Q(-3547,8192)),(15,Q(3547,8192)),(24,Q(3547,8192)),(30,Q(-3547,8192))])
        if list(p['kernel']) not in (base,extended):raise ValueError('only two original unfolded kernels admitted')
        if type(max_denominator)is not int or not 2<=max_denominator<=MAX_DENOMINATOR:raise ValueError('bounded denominator domain')
        rows=[];seen=set();cap=Q(1,p['kernel'][0][0]);answer=None
        for den in range(2,max_denominator+1):
            for num in range(1,_ceil(cap*den)):
                if gcd(num,den)!=1:continue
                points+=1;m.charge(100*(1+len(p['profiles'])+len(p['kernel'])))
                if points>MAX_POINTS:raise C.ResourceLimit('sample point gate')
                row=_cell(p,Q(num,den))
                if row is None:continue
                key=(tuple(row['source']),tuple(row['profiles']))
                if key in seen:continue
                seen.add(key);rows.append(row)
                answer=_solve(rows,p['memory']+1,len(p['profiles']),m)
                if answer is not None:break
            if answer is not None:break
        if answer is None:
            out.update(status='NOT_FOUND_WITHIN_GRAMMAR',sample_points=points,patterns=len(rows))
        else:
            selected=sorted((dict(row,t=str(t)) for row,t in zip(rows,answer) if t),key=lambda row:Q(row['left']))
            # Sample cells for different patterns are disjoint by construction.
            tau=min((Q(row['right'])-Q(row['left']))/(4*abs(Q(row['t']))) for row in selected)
            threshold=max(interval_threshold(p,row,m) for row in selected)
            H00=C.drift_matrix(p,m)[0][0]
            certificate=dict(schema='dense-rank-interval-v1',intervals=selected,tau=str(tau),threshold=threshold,H00=str(H00),lower_coefficient=str(C._mul(H00,C._mul(tau,tau,m),m)))
            out.update(status='PROPOSED_UNIFORM_RANK_OBSTRUCTION',certificate=certificate,sample_points=points,patterns=len(rows),max_denominator_reached=den,independent_admission_required=True)
    except (ValueError,TypeError,KeyError,OverflowError) as e:
        out.update(status='RESOURCE_LIMIT' if isinstance(e,C.ResourceLimit) else 'REJECTED',reason=str(e),sample_points=points)
    out.update(ops=m.ops,peak_bytes=m.peak_bytes,uniform_source_bound_proved=False,uniform_unlinked_bound_proved=False,RH_proved=False)
    return out
