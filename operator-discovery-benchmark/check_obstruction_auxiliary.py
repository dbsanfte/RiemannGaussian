"""Independent source split and finite-kernel evaluation of auxiliary states."""
from fractions import Fraction as Q
from math import isqrt
from flint import arb
import check_shifted_quotient_candidates as C


def source_state(H, meter):
    C._precision(); C._horizon(H)
    values = C.source('mu', H, meter); table = C._spf(H, meter)
    u, v = Q(1, 3), Q(2, 3)
    powers = [C._powers(b, H, meter) for b in (u, v)]
    atoms = [C._kernel(b, values, table, power, meter) for b, power in zip((u, v), powers)]
    coefficient = C._convolution(*atoms, table, meter)
    m = C.normalizer({'shifts':['1/3', '2/3']}, meter)[0]['coefficient']
    result = {name:[arb(0)]*(H+1) for name in ('T', 'V', 'R')}
    T = composite = total = diagonal = arb(0)
    for n in range(1, H+1):
        factors = C._factor(n, table, meter)
        d = t = arb(0)
        if len(factors) == 1:
            p, exponent = factors[0]
            if exponent >= 2:
                q = powers[0][p]
                d = (arb(9)/2)*(1-q*q)*q**(exponent-2)*(1-q**(exponent-1))
                meter.charge(2*exponent+8)
        elif len(factors) == 2:
            first, second = [p**e for p, e in factors]
            t = atoms[0][first]*atoms[1][second]+atoms[0][second]*atoms[1][first]
            meter.charge(7)
        total += coefficient[n]; diagonal += d; T += t
        composite += coefficient[n]-d-t
        main = m*n*powers[0][n]
        result['T'][n] = T; result['V'][n] = composite-main
        result['R'][n] = total-diagonal-main
        meter.charge(12)
    meter.live(24*(H+1)+4096)
    return dict(atoms=result, H=H, main_coefficient=m, prefix_cache={})


def integer_root(X, exponent):
    fraction = Q(exponent); value = X**fraction.numerator
    lo, hi = 0, value+1
    while lo+1 < hi:
        m = (lo+hi)//2
        if m**fraction.denominator > value: hi = m
        else: lo = m
    return lo


def kernels(tree, X, meter):
    """Compile arithmetic syntax into complete finite rational shift stencils."""
    op = tree[0]; meter.charge()
    if op == 'atom': return {tree[1]:{0:Q(1)}}
    if op in ('add', 'sub'):
        first, second = [kernels(t, X, meter) for t in tree[1:]]
        for channel, row in second.items():
            target = first.setdefault(channel, {})
            for r, w in row.items():
                meter.charge(2); target[r] = target.get(r, Q(0))+(w if op == 'add' else -w)
        return {name:{r:w for r,w in row.items() if w} for name,row in first.items()}
    old = kernels(tree[2], X, meter); h = integer_root(X, tree[1]); out = {}
    for channel, row in old.items():
        new = {}
        for r, w in row.items():
            if op == 'shift':
                new[r+h] = w; meter.charge()
            elif op == 'average':
                for j in range(h):
                    new[r+j] = new.get(r+j, Q(0))+w/h; meter.charge(3)
            else: raise ValueError('independent supported transform')
        out[channel] = new
    return out


def differences(row, meter):
    out = {}
    for r, w in row.items():
        out[r] = out.get(r, Q(0))+w
        out[r+1] = out.get(r+1, Q(0))-w
        meter.charge(4)
    return {r:w for r,w in out.items() if w}


def prefixes(state, channel, order, meter):
    cache = state.setdefault('prefix_cache', {})
    if (channel, 0) not in cache: cache[channel, 0] = state['atoms'][channel]
    for j in range(1, order+1):
        if (channel, j) in cache: continue
        out = [arb(0)]; total = arb(0)
        for v in cache[channel, j-1][1:]:
            total += v; out.append(total); meter.charge()
        cache[channel, j] = out
    return cache[channel, order]


def evaluate_tree(tree, X, start, stop, state, meter):
    compiled = kernels(tree, X, meter); result = [arb(0)]*(stop-start)
    for name, kernel in compiled.items():
        if kernel and stop-1+max(kernel) > state['H']:
            raise ValueError('complete independent shift horizon')
        candidates = [(0, kernel)]
        for j in (1, 2): candidates.append((j, differences(candidates[-1][1], meter)))
        order, chosen = min(candidates, key=lambda item:(len(item[1]), item[0]))
        data = prefixes(state, name, order, meter)
        weights = [(r, arb(w.numerator)/w.denominator*((-1)**order)) for r,w in chosen.items()]
        for i, n in enumerate(range(start, stop)):
            for r, w in weights:
                index = n+r-order
                if index >= 1: result[i] += w*data[index]
                meter.charge(3)
    meter.live(18*(state['H']+1)+4096)
    return result


def measure(program, X, state, meter):
    """Direct complete square evaluation, independent of producer Gram assembly."""
    if program['family'] == 'transport':
        parent = state['atoms']['R'][X:2*X]; child = state['atoms']['R'][2*X:4*X]
        if len(child) != 2*X: raise ValueError('complete child block')
        E = sum((r*r for r in parent), arb(0))/(X*X)
        E2 = sum((r*r for r in child), arb(0))/(4*X*X)
        cross = positive = arb(0)
        for j, text in enumerate((program['a0'], program['a1'])):
            q = Q(text); a = arb(q.numerator)/q.denominator
            for r, v in zip(parent, child[j::2]):
                d = v-a*r; cross += 2*a*r*d; positive += d*d
                meter.charge(8)
        cross /= 4*X*X; positive /= 4*X*X
        q = Q(program['rho']); drift = E2-arb(q.numerator)/q.denominator*E
        meter.charge(6*X+10)
        return dict(X=X, energy=E, child_energy=E2, majorant=E, child_majorant=E2,
                    drift=drift, cross=cross, positive=positive, open_quantity=drift, correction=positive)
    cases = []
    for base in (X, 2*X):
        rows = [evaluate_tree(t, base, base, 2*base, state, meter) for t in program['terms']]
        diagonal = [sum((r*r for r in row), arb(0))/(base*base) for row in rows]
        E = sum((r*r for r in state['atoms']['R'][base:2*base]), arb(0))/(base*base)
        cross = arb(0)
        for i in range(len(rows)):
            for j in range(i+1, len(rows)):
                for a,b in zip(rows[i], rows[j]): cross += 2*a*b; meter.charge(3)
        cross /= base*base
        weights = [Q(w) for w in program['weights']]
        F = sum((arb(w.numerator)/w.denominator*d for w,d in zip(weights,diagonal)), arb(0))
        meter.charge(2*base*(len(rows)+1)+10)
        cases.append(dict(energy=E, F=F, correction=sum(diagonal[1:],arb(0)),
                          joint=diagonal[0], cross=cross))
    first,second=cases
    return dict(X=X, energy=first['energy'], child_energy=second['energy'],
                majorant=first['F'], child_majorant=second['F'], drift=second['F']-first['F'],
                cross=first['cross'], positive=first['joint'],
                open_quantity=first['joint'], correction=first['correction'])
