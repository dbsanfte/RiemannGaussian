"""Obstruction-driven arithmetic partitions of the complete signed work kernel.

Numerical ranking uses double precision discovery data.  The triangle rule
is universal, but its grouped absolute sum is an OPEN arithmetic obligation.
No partition, including an exact one, is by itself a cancellation theorem.
"""
from fractions import Fraction as Q
import math
import numpy as np
from flint import arb
from scipy.special import exp1


def floor_root(n, k):
    if type(n) is not int or n < 0 or type(k) is not int or k < 1:
        raise ValueError('nonnegative integer and positive root order')
    if n < 2 or k == 1:
        return n
    lo, hi = 0, 1 << ((n.bit_length()+k-1)//k)
    while lo+1 < hi:
        mid = (lo+hi)//2
        if mid**k <= n: lo = mid
        else: hi = mid
    return hi if hi**k <= n else lo


def rational_power_floor(n, exponent):
    e = Q(exponent)
    if not 0 < e <= 1:
        raise ValueError('declared fractional scale powers')
    return floor_root(n**e.numerator, e.denominator)


def cutoff_value(cutoff, X):
    kind, value = cutoff['kind'], cutoff['value']
    if kind == 'none' and value == '0': return 0
    if kind == 'fixed' and value in ('2', '3'): return int(value)
    if kind == 'power' and value in ('1/6','1/3','1/2','2/3','1'):
        return rational_power_floor(X, value)
    if kind == 'log2' and value == '1': return X.bit_length()-1
    raise ValueError('declared cutoff AST')


def factor_tables(H):
    small, large = [0]*(H+1), [0]*(H+1)
    for p in range(2, H+1):
        if small[p]: continue
        for n in range(p, H+1, p):
            if not small[n]: small[n] = p
            large[n] = p
    return small, large


def labels(program, X, meter):
    if type(X) is not int or X < 2: raise ValueError('integer X>=2')
    if set(program) != {'base','post'}: raise ValueError('partition AST fields')
    base, post = program['base'], program['post']
    if set(base) != {'op','cutoff','valuation_step'} or base['op'] != 'strip_small_prime_powers':
        raise ValueError('base AST')
    if base['valuation_step'] not in (1,2) or type(base['valuation_step']) is not int:
        raise ValueError('valuation step')
    if set(post) != {'op','value'}: raise ValueError('post AST')
    H, q = 4*X-1, cutoff_value(base['cutoff'], X)
    small, large = factor_tables(H)
    stripped = list(range(H+1))
    for p in range(2, min(q,H)+1):
        if small[p] != p: continue
        for n in range(p,H+1,p):
            t, e = n, 0
            while t % p == 0: t //= p; e += 1; meter.charge(2)
            stripped[n] //= p**(e-e%base['valuation_step'])
            meter.charge(4)
    op, value = post['op'], post['value']
    out = [0]*(H+1)
    for n in range(1,H+1):
        r = stripped[n]
        if op == 'identity' and value == '0': a = r
        elif op in ('remove_largest_once','remove_smallest_once','remove_largest_all') and value == '0':
            p = (small if op == 'remove_smallest_once' else large)[r]
            a = r if r == 1 else r//p
            if op == 'remove_largest_all' and r > 1:
                while a % p == 0: a //= p; meter.charge(2)
        elif op == 'root' and value in ('2','3','6'): a = floor_root(r,int(value))
        elif op == 'quotient' and value in ('1/3','1/2'): a = r//max(1,rational_power_floor(X,value))
        elif op == 'residue' and value in ('2','3','6'): a = r%int(value)
        else: raise ValueError('post operation')
        out[n] = a; meter.charge(20)
    return out


def prime_frontier_certificate(source, Ru):
    """Extract the first nonzero COMPLETE prime term, with formal beta/Ru."""
    scalars = {'beta':(Q(1),Q(0)), '-beta':(Q(-1),Q(0)), '-R_u':(Q(0),Q(-1))}
    rows = {}
    for term in source['terms']:
        b,r = scalars[term['coefficient']]
        for shift, exponent in term['zeta_factors']:
            s,e = Q(shift),Q(exponent)
            old = rows.get(s,(Q(0),Q(0)))
            rows[s] = (old[0]+b*e, old[1]+r*e)
    rows = {s:v for s,v in rows.items() if any(v)}
    if not rows: raise ValueError('no nonzero complete prime term')
    first = min(rows); b,r = rows[first]
    amplitude = arb(b.numerator)/b.denominator*arb(9)/2 + arb(r.numerator)/r.denominator*Ru
    if not amplitude.is_finite() or amplitude.contains(0): raise ValueError('prime amplitude not certified nonzero')
    return dict(rule='singleton_fresh_prime_frontier',
        complete_prime_terms=[dict(exponent=str(s),beta=str(b),R_u=str(r)) for s,(b,r) in sorted(rows.items())],
        leading_exponent=str(first),leading_coefficient=str(amplitude),
        forced_absolute_power=str(1-2*first),positive_power_obstruction=first<Q(1,2),
        scope='any prime-stripping set contained in primes<=X; each valuation step; all X sufficiently large',
        proof='primes in(2X,5X/2] form singleton classes; step kernel>=3/(40X); weighted prime number theorem',
        imported_theorems=['prime number theorem, used only for an unconditional lower bound on a proof majorant'],
        all_prime_source_terms_combined=True,does_not_disprove_signed_target=True,
        whole_signed_bound_proved=False,RH_proved=False)


def generate(frontier,meter):
    cuts = [('none','0'),('fixed','2'),('fixed','3')]+[('power',p) for p in ('1/6','1/3','1/2','2/3','1')]+[('log2','1')]
    posts = [('remove_largest_once','0'),('remove_smallest_once','0'),('remove_largest_all','0')]
    posts += [('root',v) for v in ('2','3','6')]+[('quotient',v) for v in ('1/3','1/2')]+[('residue',v) for v in ('2','3','6')]
    rows=[]
    for kind,value in cuts:
        for step in ((1,) if kind=='none' else (1,2)):
            base=dict(op='strip_small_prime_powers',cutoff=dict(kind=kind,value=value),valuation_step=step)
            pid=len(rows)
            rows.append(dict(id=pid,program=dict(base=base,post=dict(op='identity',value='0')),
                parent=None,complexity=1,round=0,lane='valuation_orbit',
                proof_gate='ruled_out_prime_frontier' if frontier['positive_power_obstruction'] else 'open',
                obstruction=frontier['rule']))
    # The fixed mutation rule is activated by a proved obstruction, not scores.
    for parent in list(rows):
        if parent['proof_gate']!='ruled_out_prime_frontier': continue
        for op,value in posts:
            rows.append(dict(id=len(rows),program=dict(base=parent['program']['base'],post=dict(op=op,value=value)),
                parent=parent['id'],complexity=2,round=1,
                lane='prime_cofactor' if op.startswith('remove_') else 'fractional_interval' if op in ('root','quotient') else 'residue',
                proof_gate='open_grouped_arithmetic_premise',obstruction=None))
            cut=parent['program']['base']['cutoff']
            if parent['program']['base']['valuation_step']==1 and cut['kind']=='power' and Q(cut['value'])>Q(1,2):
                if op.startswith('remove_'):
                    rows[-1].update(proof_gate='eventually_one_bucket_restatement',obstruction='rough_residual_has_at_most_one_prime')
                elif op in ('root','quotient') and frontier['positive_power_obstruction']:
                    rows[-1].update(proof_gate='ruled_out_prime_only_coarsening',obstruction='sublinear_width_prime_only_interior_groups')
            meter.charge(80)
    return rows


def compact_labels(label):
    values, inverse = np.unique(np.asarray(label[1:],dtype=np.int64),return_inverse=True)
    return values.tolist(),inverse


def kernel_vectors(X,eta='1',rho='1/2'):
    H=4*X-1;n=np.arange(1,H+1,dtype=np.float64)
    def weights(Y):
        left=np.maximum(Y,n);live=left<2*Y
        d=np.where(live,1/left-1/(2*Y),0.)
        ell=np.where(live,exp1(np.log(left))-exp1(math.log(2*Y)),0.)
        return d,ell
    d1,l1=weights(X);d2,l2=weights(2*X)
    e,r=float(Q(eta)),float(Q(rho))
    return (1-e)*(d2-r*d1), e*(l2-r*l1)/2, np.log(n)


def grouped_float(coeff,label,X,meter,eta='1',rho='1/2'):
    H=4*X-1
    if len(coeff)!=H+1 or len(label)!=H+1 or coeff[0]!=0: raise ValueError('complete index domain')
    values, ids=compact_labels(label);G=len(values)
    a,b,logs=kernel_vectors(X,eta,rho)
    matrix=np.zeros((G,G));C=np.zeros(G);L=np.zeros(G);diag=0.
    for i in range(H):
        f=float(coeff[i+1]);g=ids[i]
        update=f*((a[i]+b[i]*logs[i])*C+b[i]*L)
        matrix[g,:]+=update;matrix[:,g]+=update
        term=f*f*(a[i]+2*b[i]*logs[i]);matrix[g,g]+=term;diag+=term
        C[g]+=f;L[g]+=f*logs[i]
        meter.charge(12*G+40)
    signed=float(matrix.sum());absolute=float(np.abs(matrix).sum())
    meter.live(G*G+5*H+5*G)
    return dict(group_labels=values,group_count=G,signed_total=signed,sum_abs=absolute,
        positive_sum=float(np.maximum(matrix,0).sum()),negative_sum=float(np.minimum(matrix,0).sum()),
        diagonal_coefficient_sum=diag,rounding_bound_not_certified=True,
        max_group_size=int(np.bincount(ids).max()),matrix=matrix)


def grouped_arb(coeff,label,X,meter,eta='1',rho='1/2'):
    H=4*X-1
    if len(coeff)!=H+1 or len(label)!=H+1 or not coeff[0].is_zero(): raise ValueError('complete index domain')
    values=sorted(set(label[1:]));position={v:i for i,v in enumerate(values)};G=len(values)
    C=[arb(0)]*G;L=[arb(0)]*G;mat=[[arb(0) for _ in range(G)] for _ in range(G)]
    e,r=Q(eta),Q(rho);e=arb(e.numerator)/e.denominator;r=arb(r.numerator)/r.denominator
    endpoints={n:arb(n).log().expint(1) for n in range(X,4*X+1)}
    diag=arb(0)
    for n in range(1,H+1):
        def weight(Y):
            if n>=2*Y:return arb(0),arb(0)
            left=max(Y,n)
            return arb(1)/left-arb(1)/(2*Y),endpoints[left]-endpoints[2*Y]
        d1,l1=weight(X);d2,l2=weight(2*X);a=(1-e)*(d2-r*d1);b=e*(l2-r*l1)/2
        f,ln,j=coeff[n],arb(n).log(),position[label[n]]
        for k in range(G):
            update=f*((a+b*ln)*C[k]+b*L[k]);mat[j][k]+=update;mat[k][j]+=update
        t=f*f*(a+2*b*ln);mat[j][j]+=t;diag+=t;C[j]+=f;L[j]+=f*ln
        meter.charge(25*G+500)
    flat=[q for row in mat for q in row];signed=sum(flat,arb(0));absolute=sum(map(abs,flat),arb(0))
    return dict(group_labels=values,group_matrix=mat,signed_total=signed,sum_abs=absolute,
        positive_sum=(signed+absolute)/2,negative_sum=(signed-absolute)/2,diagonal_coefficient_sum=diag)


def obligation(row):
    return dict(schema='complete-grouped-work-obligation-v1',program_id=row['id'],program=row['program'],
        grouped_pair='Q_(r,s)(X)=sum_(h,k<=4X-1,label_X(h)=r,label_X(k)=s) f(h)f(k)[K_1,2X(h,k)-K_1,X(h,k)/2]',
        proved_identity='Delta W_1(X)=sum_(r,s)Q_(r,s)(X)',
        proved_upper_rule='Delta W_1(X)<=sum_(r,s)|Q_(r,s)(X)|',
        missing_bound='there exist finite C and fixed k>=0 such that sum_(r,s)|Q_(r,s)(X)|<=C(1+log2X)^k for EVERY dyadic X>=1024',
        original_degree2_branch='to establish the selected constant C1 degree2 step specifically, the corresponding stronger constant and degree must also be paid',
        complete_support=True,unit_and_old_head_included=True,all_four_mode_crosses_included=True,
        imported_recovery='signed Volterra history recovery; original corrections and inverse costs remain attached to parent target',
        proof_dependency_cycle=False,uniform_group_bound_proved=False,whole_signed_bound_proved=False,RH_proved=False)
