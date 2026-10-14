"""Complete centered arithmetic product fibers and recoverable band operators.

Arb values are finite measurements. Universal recovery applies conditionally
to a uniform bound on the entire band/partial-prefix auxiliary, not to a fit.
"""
from fractions import Fraction as Q
from itertools import groupby
from math import comb, gcd

from flint import arb, ctx
import prime_bank_candidates as SOURCE

GAMMAS = ('0', '1/6', '1/3')
SECTORS = ('aa_sf','aa_ns','cross_sf','cross_ns','mm_sf','mm_ns')


def tight(value):
    return value.is_finite() and value.rad() <= arb(2)**(-65)*(1+abs(value.mid()))


def encode(value):
    if not tight(value):
        raise ArithmeticError('tight finite measurement required')
    return value.str(55)


def source(H, meter):
    state = SOURCE.source_state(H, meter)
    mu = [0]*(H+1)
    mu[1] = 1
    m = [arb(0)]*(H+1)
    b = [arb(0)]*(H+1)
    sixth = [arb(0)]*(H+1)
    previous = arb(0)
    for n in range(1,H+1):
        if n > 1:
            p = state['spf'][n]
            mu[n] = 0 if (n//p)%p == 0 else -mu[n//p]
        m[n] = state['main'][n]-previous
        b[n] = state['a'][n]-m[n]
        sixth[n] = arb(n).root(6)
        previous = state['main'][n]
        meter.charge(80)
    state.update(mu=mu,m=m,b=b,sixth=sixth)
    meter.live(state['_resident_cells']+5*(H+1))
    return state


def stencils():
    records = []
    for c1 in range(-2,3):
        for c2 in range(-2,3):
            admitted = abs(c2)<=1 and abs(c1)<=1+c2
            records.append(dict(id=len(records),coefficients=[1,c1,c2],
                                cofinal_inverse_admitted=admitted,
                                inverse_root_condition='|c2|<=1 and |c1|<=1+c2',
                                inverse_coefficient_envelope='|g_l|<=l+1' if admitted else None,
                                status='POLYLOG_RECOVERY' if admitted else 'EXPONENTIAL_INVERSE_REQUIRES_EXTRA_SOURCE_GAIN'))
    return records


def inverse_coefficients(coefficients, length, meter):
    if (type(coefficients) is not list or len(coefficients)!=3 or coefficients[0]!=1 or
            any(type(c) is not int for c in coefficients) or type(length) is not int or length<1):
        raise ValueError('integer causal quadratic with constant one')
    _,c1,c2 = coefficients
    out = [1]
    for n in range(1,length):
        out.append(-c1*out[n-1]-(c2*out[n-2] if n>=2 else 0))
        meter.charge(4)
    return out


def scatter(X, state, meter):
    """Each product stores its one SF status and AA/cross/MM/centered fibers."""
    N = 2*X-1
    if type(X) is not int or X<1 or state['H']<N:
        raise ValueError('complete positive prefix block')
    rows = {}
    a,m,b,mu = (state[name] for name in ('a','m','b','mu'))
    for h in range(1,N+1):
        for k in range(h,N+1):
            product = h*k
            weight = (2 if h!=k else 1)*(2*X-max(X,k))
            sf = bool(mu[h] and mu[k] and gcd(h,k)==1)
            aa = weight*a[h]*a[k]
            cross = -weight*(a[h]*m[k]+m[h]*a[k])
            mm = weight*m[h]*m[k]
            centered = weight*b[h]*b[k]
            meter.charge(24)
            if product not in rows:
                rows[product] = [h,sf,aa,cross,mm,centered]
            else:
                row = rows[product]
                if row[1] != sf:
                    raise AssertionError('squarefreeness is a product property')
                for index,value in enumerate((aa,cross,mm,centered),2):
                    row[index] += value
                meter.charge(4)
        meter.live(state.get('_resident_cells',0)+20*len(rows)+4096)
    return rows


def weights(product, row, state, meter):
    h = row[0]
    inverse = 1/(state['sixth'][h]*state['sixth'][product//h])
    meter.charge(4)
    return (arb(1),inverse,inverse*inverse)


def profiles(X, rows, state, cutoffs, meter):
    """Complete six-sector prefix queries in increasing product order."""
    cutoffs = sorted(set(cutoffs))
    if any(type(T) is not int or T<0 for T in cutoffs):
        raise ValueError('integer nonnegative product cutoffs')
    sums = [[arb(0)]*7 for _ in GAMMAS]
    answer = {}
    ordered = iter(sorted(rows))
    current = next(ordered,None)
    for T in cutoffs:
        while current is not None and current<=T:
            row = rows[current]
            sector = 0 if row[1] else 1
            for gi,weight in enumerate(weights(current,row,state,meter)):
                for offset,index in enumerate((2,3,4)):
                    sums[gi][2*offset+sector] += row[index]*weight
                sums[gi][6] += row[5]*weight
                meter.charge(8)
            current = next(ordered,None)
        answer[T] = {}
        for gi,gamma in enumerate(GAMMAS):
            values = [value/(X*X) for value in sums[gi]]
            if not (sum(values[:6],arb(0))-values[6]).contains(0):
                raise ArithmeticError('six complete sectors recover direct centered coefficients')
            answer[T][gamma] = dict(zip(SECTORS,values[:6]),
                                    centered_sf=values[0]+values[2]+values[4],
                                    centered_ns=values[1]+values[3]+values[5],centered=values[6])
            meter.charge(22)
    return answer


def search_bands(X, rows, state, grammar, meter, candidate_pairs=None):
    """All rational breakpoints, not sampled t values or endpoint-only fits."""
    N = 2*X-1
    J = (N*N-1).bit_length()
    top = 1<<J
    accepted = [row for row in grammar if row['cofinal_inverse_admitted']]
    allowed = {(row['id'],gamma) for row in accepted for gamma in GAMMAS}
    if candidate_pairs is not None and (not candidate_pairs or not set(candidate_pairs)<=allowed):
        raise ValueError('declared admitted stencil/weight pairs')
    powers = []
    for j in range(J+1):
        root = arb(1<<j).root(6)
        powers.append((arb(1),root,root*root))
        meter.charge(68)
    partial = [[arb(0)]*(J+1) for _ in GAMMAS]
    records = []
    for row in accepted:
        for gamma in GAMMAS:
            if candidate_pairs is not None and (row['id'],gamma) not in candidate_pairs:
                continue
            records.append(dict(stencil_id=row['id'],gamma=gamma,upper=arb(0),lower=arb(0),
                                witness=dict(j=0,t='1/2',value=arb(0))))
    lookup = {(r['stencil_id'],r['gamma']):r for r in records}
    # Each break is m/2^j with j=ceil(log2 m); one common dyadic denominator
    # permits exact simultaneous updates when multiple bands jump together.
    coordinate = lambda product: product << (J-(product-1).bit_length())
    ordered = sorted(rows,key=coordinate)
    event_count = 0
    for event,products in groupby(ordered,key=coordinate):
        affected = set()
        for product in products:
            row = rows[product]
            j = (product-1).bit_length()
            for gi,weight in enumerate(weights(product,row,state,meter)):
                partial[gi][j] += row[5]*weight*powers[j][gi]/(X*X)
                meter.charge(4)
            affected.update(range(j,min(J,j+2)+1))
        for j in sorted(affected):
            for stencil in accepted:
                _,c1,c2 = stencil['coefficients']
                for gi,gamma in enumerate(GAMMAS):
                    if (stencil['id'],gamma) not in lookup:
                        continue
                    value = partial[gi][j]
                    if j>=1 and c1:
                        value += c1*partial[gi][j-1]
                    if j>=2 and c2:
                        value += c2*partial[gi][j-2]
                    upper,lower = value.abs_upper(),value.abs_lower()
                    record = lookup[(stencil['id'],gamma)]
                    if upper > record['upper']:
                        record['upper'] = upper
                    if lower > record['lower']:
                        record['lower'] = lower
                        record['witness'] = dict(j=j,t=str(Q(event,top)),value=value)
                    meter.charge(14)
        event_count += 1
        meter.charge(2)
    for record in records:
        gamma = Q(record['gamma'])
        stencil = next(row for row in accepted if row['id']==record['stencil_id'])
        inverse = inverse_coefficients(stencil['coefficients'],J+1,meter)
        inverse_sum = sum((J-j+1)*abs(value) for j,value in enumerate(inverse))
        if inverse_sum > comb(J+3,3):
            raise AssertionError('unit-disc recurrence recovery envelope')
        constant = (2-arb(2)**(-arb(gamma.numerator)/gamma.denominator))*inverse_sum
        record.update(inverse_coefficients=inverse,inverse_l1_sum=inverse_sum,
                      recovery_constant=constant,recovered_energy_upper=(constant*record['upper']).upper(),
                      all_partial_breakpoints_examined=True,uniform_in_X_proved=False,
                      whole_signed_bound_proved=False,RH_proved=False)
        meter.charge(80)
    meter.live(state.get('_resident_cells',0)+22*len(rows)+64*len(records)*(J+1)+4096)
    return dict(X=X,N=N,J=J,distinct_products=len(rows),relative_breakpoints=event_count,candidates=records)


def prefix_diagnostics(X,state,meter):
    N = 2*X-1
    accumulators = [arb(0)]*3
    unnormalized = [arb(0)]*3
    normalized = [arb(0)]*3
    raw = arb(0)
    for n in range(1,N+1):
        root = state['sixth'][n]
        scale = (arb(1),root,root*root)
        for gi,factor in enumerate(scale):
            accumulators[gi] += state['b'][n]/factor
            if n>=X:
                unnormalized[gi] += accumulators[gi]*accumulators[gi]/(X*X)
                normalized[gi] += (factor*accumulators[gi])**2/(X*X)
            meter.charge(12)
        if n>=X:
            raw += state['R'][n]*state['R'][n]/(X*X)
            meter.charge(4)
    if not (raw-normalized[0]).contains(0):
        raise ArithmeticError('center increments retain full original prefix')
    return dict(original_energy=raw,weighted_energy=dict(zip(GAMMAS,unnormalized)),
                normalized_abel_energy=dict(zip(GAMMAS,normalized)))


def serialize(value):
    if isinstance(value,arb):
        return encode(value)
    if isinstance(value,dict):
        return {str(k):serialize(v) for k,v in value.items()}
    if isinstance(value,(tuple,list)):
        return [serialize(v) for v in value]
    return value
