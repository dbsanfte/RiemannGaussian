"""Linear-storage complete joined product correlation and source sectors.

The high off-diagonal correlation is an equivalent unresolved signed target.
Its fast evaluation and finite identities do not prove its all-scale bound.
"""
from math import isqrt

from flint import arb, ctx
import prime_bank_candidates as SOURCE

MAX_HORIZON = 131071
SECTORS = ('aa', 'cross', 'mm', 'centered')


def source(H, meter):
    if type(H) is not int or not 1 <= H <= MAX_HORIZON:
        raise ValueError('source horizon1..131071')
    state = SOURCE.source_state(H, meter)
    m = state['m_u']
    R_u = arb(2)*m/3
    E0 = -R_u*(arb(1)/3).zeta()
    if not m > 0 or not E0 > 0:
        raise ArithmeticError('positive exact source constants')
    pure = [arb(0)]*(H+1)
    centered = [arb(0)]*(H+1)
    for n in range(1,H+1):
        pure[n] = R_u/arb(n).root(3)
        centered[n] = state['a'][n]-pure[n]
        meter.charge(70)
    meter.charge(280)
    state.update(pure=pure, tilde_b=centered, R_u=R_u, E0=E0)
    meter.live(state['_resident_cells']+2*(H+1)+64)
    return state


def _products(left_a, left_c, right_a, right_c):
    return (left_a*right_a, -(left_a*right_c+left_c*right_a),
            left_c*right_c, (left_a-left_c)*(right_a-right_c))


def prepare(state, max_X, meter):
    """One convolution head and prefix table per complete source sector."""
    H = state.get('H')
    if (type(H) is not int or not 1 <= H <= MAX_HORIZON or
            type(max_X) is not int or not 1 <= max_X <= (H+1)//2):
        raise ValueError('complete source and positive block horizon')
    for name in ('a','pure','R'):
        if type(state.get(name)) is not list or len(state[name]) != H+1:
            raise ValueError('complete source dimensions')
        if state[name][0] != 0:
            raise ValueError('zero source prehistory')
    cells = state.get('_resident_cells',4*(H+1))+16*(H+1)+4*(max_X+1)+4096
    meter.live(cells)
    # All four channels include the same support and normalization.
    energy = [[arb(0)]*(H+1) for _ in SECTORS]
    diagonal = [[arb(0)]*(H+1) for _ in SECTORS]
    diagonal_n = [[arb(0)]*(H+1) for _ in SECTORS]
    original_energy = [arb(0)]*(H+1)
    T = [arb(0)]*(H+1)
    A = C = arb(0)
    a,c = state['a'],state['pure']
    for n in range(1,H+1):
        A += a[n]; C += c[n]; T[n] = A-C
        pairs = _products(a[n],c[n],a[n],c[n])
        prefixes = _products(A,C,A,C)
        for j in range(4):
            energy[j][n] = energy[j][n-1]+prefixes[j]
            diagonal[j][n] = diagonal[j][n-1]+pairs[j]
            diagonal_n[j][n] = diagonal_n[j][n-1]+n*pairs[j]
        original_energy[n] = original_energy[n-1]+state['R'][n]**2
        meter.charge(55)
    head = [[arb(0)]*(max_X+1) for _ in SECTORS]
    # h<=k counts each ordered factor pair once with the exact multiplicity.
    for h in range(1,isqrt(max_X)+1):
        for k in range(h,max_X//h+1):
            m = h*k
            values = _products(a[h],c[h],a[k],c[k])
            multiplicity = 1 if h==k else 2
            for j,value in enumerate(values):
                head[j][m] += multiplicity*value
            meter.charge(22)
    for m in range(1,max_X+1):
        for j in range(4):
            head[j][m] += head[j][m-1]
        meter.charge(4)
    return dict(H=H,max_X=max_X,precision=ctx.prec,energy=energy,
                diagonal=diagonal,diagonal_n=diagonal_n,head=head,
                original_energy=original_energy,tilde_R=T,
                _resident_cells=cells)


def query(X, tables, meter):
    if (type(X) is not int or not 1 <= X <= tables['max_X'] or
            tables['precision'] != ctx.prec):
        raise ValueError('declared complete block at source precision')
    N = 2*X-1
    c = isqrt(X)
    values = {}
    for j,name in enumerate(SECTORS):
        E,Q,Q1 = tables['energy'][j],tables['diagonal'][j],tables['diagonal_n'][j]
        energy = (E[N]-E[X-1])/(X*X)
        head = tables['head'][j][X]/X
        diagonal = (X*(Q[X]-Q[c])+2*X*(Q[N]-Q[X])-(Q1[N]-Q1[X]))/(X*X)
        values[name] = dict(energy=energy,low_head=head,high_diagonal=diagonal,
                            O=energy-head-diagonal)
        meter.charge(30)
    for name in ('energy','low_head','high_diagonal','O'):
        joint = sum((values[key][name] for key in SECTORS[:3]),arb(0))
        if not (joint-values['centered'][name]).contains(0):
            raise ArithmeticError('joint AA/cross/MM must recover centered source')
        meter.charge(6)
    E = tables['original_energy']
    original = (E[N]-E[X-1])/(X*X)
    centered = values['centered']
    correction = original-centered['energy']
    residual = original-centered['O']-centered['low_head']-centered['high_diagonal']-correction
    if not residual.contains(0):
        raise ArithmeticError('complete joint target recovery')
    meter.charge(16)
    return dict(X=X,N=N,Hsplit=c,O=centered['O'],low_head=centered['low_head'],
                high_diagonal=centered['high_diagonal'],energy_R=original,
                energy_tilde=centered['energy'],center_correction=correction,
                identity_residual=residual,sectors=values,
                uniform_signed_bound_proved=False,whole_signed_bound_proved=False,RH_proved=False)


def analytic_remainder(X, state, meter):
    if type(X) is not int or X<1:
        raise ValueError('positive scale')
    N = 2*X-1
    K = arb(9)/2+state['m_u']; E0 = state['E0']
    low = K*K*(1+arb(X).log())**3
    diagonal = 2*K*K*(1+arb(N).log())**3
    center = 4*E0*K*(1+arb(2*X).log())+E0*E0/X
    meter.charge(210)
    return dict(low_head=low,high_diagonal=diagonal,center_correction=center,
                combined=low+diagonal+center,
                source='CENTERED_BAND_FORCING_REVIEW_003.txt section9',
                uniform_remainder_proved_analytically=True,
                signed_O_upper_bound_proved=False,RH_proved=False)
