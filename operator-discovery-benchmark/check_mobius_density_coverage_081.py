"""Independent finite coefficient geometry; no coverage/packet producer imports.

Reuses the frozen independent arithmetic and direct maximum-denominator pair
compiler. No finite geometry quantity is an arithmetic cancellation bound.
"""
from fractions import Fraction as Q
import math
import numpy as np
import check_mobius_density_packet_081 as C


def _dot(v,T,w):
    return sum((v[i]*T[i][j]*w[j] for i in range(len(T)) for j in range(len(T))),Q(0))


def verify_coverage(program, certificate, meter=None):
    m=meter or C.Meter();out={}
    try:
        p=C.parse_program(program,m);_,T=C.drift_matrix(p,m)
        if type(certificate) is not dict:raise C.AdmissionError('coverage dictionary required')
        u=C.F._integer(certificate.get('u'),'u',1,C.F.MAX_PARENT)
        D=C._integer_root(C._power_target(u,p['eta'].numerator,p['eta'].denominator,0,m),p['eta'].denominator,m)
        pairs=D*(D-1)//2
        if D>C.A.MAX_HORIZON or pairs>C.MAX_FINITE_PAIRS:raise C.ResourceLimit('complete ratio bank gate')
        horizon=max(D,u//min(p['kernel']));budget=C._pair_budget(p,T,D.bit_length(),m)
        m.reserve(C._resident()+C._program_cost(p)+budget['temporary_bytes']+pairs*budget['pair_bytes']+96*(horizon+1)+8192)
        m.charge(pairs*(budget['products']+1)+100*(horizon+1))
        source=C.A.ensure_horizon(horizon,m);mu=source['mu'];least=source['least']
        limit=u//min(p['kernel'])
        sf=np.cumsum(mu[:limit+1]!=0,dtype=np.int64)
        flags=(least[:limit+1]==np.arange(limit+1)) & (np.arange(limit+1)>=2)
        prime=np.cumsum(flags,dtype=np.int64)
        dim=len(T)
        cuts=sorted({0}|{u//(2**i*d) for i in range(dim) for d in p['kernel']})
        def vector(n):
            return [sum((w for d,w in p['kernel'].items() if n*2**i*d<=u),Q(0)) for i in range(dim)]
        bands=[]
        for l,h in zip(cuts,cuts[1:]):
            bands.append(dict(left=l,right=h,vector=vector(l+1),squarefree=int(sf[h]-sf[l]),primes=int(prime[h]-prime[l])))
        mass=diag=Q(0);edges=0
        m.charge(1000*len(bands)**2)
        for i,b in enumerate(bands):
            n=b['squarefree'];v=_dot(b['vector'],T,b['vector']);diag+=n*abs(v);mass+=n*(n-1)*abs(v);edges+=n*(n-1)//2*bool(v)
            for c in bands[i+1:]:
                v=_dot(b['vector'],T,c['vector']);mass+=2*n*c['squarefree']*abs(v);edges+=n*c['squarefree']*bool(v)
        rows=[];P=N=Q(0);nonzero=pc=nc=zc=0
        for b in range(2,D+1):
            if not mu[b]:continue
            for a in range(1,b):
                if not mu[a] or math.gcd(a,b)!=1:continue
                terms,I=C._pair(p,T,a,b,m);primes=C._factor_primes(a,source)+C._factor_primes(b,source)
                density=Q(int(mu[a])*int(mu[b]))*I
                for primefactor in primes:density*=Q(primefactor,primefactor+1)
                rows.append((a,b,terms,primes,density))
                if density>0:P+=density
                elif density<0:N-=density
                if terms:
                    nonzero+=1
                    if density>0:pc+=1
                    elif density<0:nc+=1
                    else:zc+=1
        wp=min(Q(1),N/P) if P else Q(0);wn=min(Q(1),P/N) if N else Q(0)
        removed=weighted=Q(0);touched=0
        for a,b,terms,primes,density in rows:
            w=wp if density>0 else wn if density<0 else Q(1)
            if not w or not terms:continue
            # Direct max-denominator kernel segments, restricted counts via
            # square-divisor/coprimality inclusion-exclusion, never event masks.
            cumulative=Q(0)
            for i,(den,c) in enumerate(terms):
                cumulative+=c
                if not cumulative:continue
                top=u//den;bottom=u//terms[i+1][0] if i+1<len(terms) else 0
                count=C._count(a*b,primes,top,source,m)-C._count(a*b,primes,bottom,source,m)
                if count<0:raise C.AdmissionError('negative independent segment count')
                touched+=count;weighted+=w*count;removed+=w*abs(cumulative)*count
        if not 0<=removed<=mass or not 0<=weighted<=touched<=edges:raise C.AdmissionError('disjoint geometry inequality failed')
        lo,hi=u//5,u//4;frontier={'admitted':False}
        # Every intersecting band is required, not only interval endpoints.
        target=[Q(-1)]+[Q(0)]*(dim-1)
        valid=lo<hi<=limit and lo>=D and all(b['vector']==target for b in bands if b['right']>lo and b['left']<hi)
        if valid:
            count=int(prime[hi]-prime[lo])
            frontier=dict(admitted=True,lower_exclusive=lo,upper_inclusive=hi,prime_count=count,unordered_prime_pairs=count*(count-1)//2,per_pair_signed_coefficient=str(2*T[0][0]),signed_contribution=str(T[0][0]*count*(count-1)),all_pairs_have_gcd_one=True,all_reduced_labels_exceed_D=True,packet_removes_none_of_these_pairs=True,interpretation='positive actual-prime block remains insideU and must cancel jointly with its complement')
        expected=dict(u=u,D=D,bands=[dict(b,vector=list(map(str,b['vector']))) for b in bands],complete_ratio_labels=len(rows),nonzero_ratio_labels=nonzero,retained_nonzero_ratio_labels=int(wp>0)*pc+int(wn>0)*nc+zc,weighted_label_count=str(wp*pc+wn*nc+zc),unordered_nonzero_offdiagonal_pairs=edges,absolute_offdiagonal_coefficient_mass=str(mass),absolute_diagonal_coefficient_mass=str(diag),retained_nonzero_physical_pairs=touched,weighted_physical_pairs=str(weighted),removed_absolute_coefficient_mass=str(removed),remaining_absolute_coefficient_mass=str(mass-removed),fraction_absolute_mass_removed=str(removed/mass if mass else Q(0)),fraction_nonzero_edges_touched=str(Q(touched,edges) if edges else Q(0)),untouched_prime_block=frontier,arithmetic_cancellation_bound_proved=False,uniform_unlinked_bound_proved=False,RH_proved=False)
        # Equality is strict: canonical rational strings, exact schema, and no
        # extra proof claims are admitted. Reject bools in numeric positions.
        def identical(a,b):
            if type(a) is not type(b):return False
            if isinstance(a,dict):return set(a)==set(b) and all(identical(a[k],b[k]) for k in a)
            if isinstance(a,list):return len(a)==len(b) and all(identical(x,y) for x,y in zip(a,b))
            return a==b
        if not identical(certificate,expected):raise C.AdmissionError('independent coverage certificate mismatch')
        out.update(status='VERIFIED_FINITE_DENSITY_COVERAGE',finite_geometry_verified=True,u=u,D=D,absolute_mass=str(mass),removed_mass=str(removed),prime_block_verified=valid)
    except (ValueError,TypeError,KeyError,OverflowError) as e:
        out.update(status='INVALID',reason=str(e))
        if isinstance(e,C.ResourceLimit):out['resource_limit']=True
    out.update(ops=m.ops,peak_bytes=m.peak_bytes,arithmetic_cancellation_bound_proved=False,uniform_unlinked_bound_proved=False,RH_proved=False,source_kernel_binding_still_required=True)
    return out
