"""Complete finite Gram diagnostics; no fitted constants or proof promotion."""
from fractions import Fraction as Q
from flint import arb

ATOMS = ('K', '-L0', 'Lu', 'Lv', '-main')
PAIRS = tuple((i,j) for i in range(5) for j in range(i,5))


def tight(value):
    return (type(value) is arb and value.is_finite() and
            value.rad() <= arb(2)**(-65)*(1+abs(value.mid())))


def check_identity(values, meter):
    H = values['H']
    for key in ('K','L0','Lu','Lv','reduced','R','main'):
        if len(values[key]) != H+1: raise ValueError('complete pointwise arrays')
    for n in range(1,H+1):
        residual = values['R'][n]-values['reduced'][n]-values['Lv'][n]
        meter.charge(40)
        if (not residual.contains(0) or not tight(residual) or
            not tight(values['R'][n]) or not tight(values['reduced'][n])):
            raise ArithmeticError('complete prime-bank identity at n='+str(n))
    return H


def coverage(theta_text, begin, end, meter):
    """Exact maximum possible cofactor from the strict cutoff, with no logs.

    k<x^(1-theta) is necessary, not sufficient for a prime bank entry. This
    records the scope of the finite experiment, not unseen arithmetic proof.
    """
    theta=Q(theta_text)
    def largest_possible(n):
        target=n**(theta.denominator-theta.numerator); lo,hi=0,n
        meter.charge(theta.denominator)
        while lo < hi:
            mid=(lo+hi+1)//2; meter.charge(theta.denominator+3)
            if mid**theta.denominator < target:lo=mid
            else:hi=mid-1
        return lo
    return dict(first_point=begin,last_point=end-1,
                necessary_cofactor_max_first=largest_possible(begin),
                necessary_cofactor_max_last=largest_possible(end-1),
                describes='strict k<n^(1-theta); actual-prime existence is additional')


def gram_block(values, X, meter):
    if type(X) is not int or X<1 or 2*X-1>values['H']:
        raise ValueError('complete block horizon')
    gram=[arb(0)]*len(PAIRS); sums=[arb(0)]*5
    energies=[arb(0),arb(0)]
    for n in range(X,2*X):
        row=(values['K'][n],-values['L0'][n],values['Lu'][n],values['Lv'][n],-values['main'][n])
        for j in range(5): sums[j]+=row[j]
        for j,(a,b) in enumerate(PAIRS): gram[j]+=row[a]*row[b]
        energies[0]+=values['R'][n]*values['R'][n]
        energies[1]+=values['reduced'][n]*values['reduced'][n]
        meter.charge(41)
    scale=X*X; gram=[g/scale for g in gram]; sums=[g/X for g in sums]
    E,reduced=(v/scale for v in energies)
    whole=sum((g*(1 if a==b else 2) for g,(a,b) in zip(gram,PAIRS)),arb(0))
    sub=sum((g*(1 if a==b else 2) for g,(a,b) in zip(gram,PAIRS) if a!=3 and b!=3),arb(0))
    diagonal=sum((g for g,(a,b) in zip(gram,PAIRS) if a==b),arb(0))
    meter.charge(180)
    for direct,computed in ((E,whole),(reduced,sub)):
        residual=direct-computed; meter.charge(4)
        if not residual.contains(0) or not tight(residual):raise ArithmeticError('complete signed Gram recombination')
    out={f'G_{a}_{b}':g for g,(a,b) in zip(gram,PAIRS)}
    out.update({f'mean_{j}':g for j,g in enumerate(sums)})
    out.update(energy_R=E,energy_reduced=reduced,energy_diagonal=diagonal,
               signed_cross=E-diagonal)
    meter.charge(1)
    if not all(tight(v) for v in out.values()):raise ArithmeticError('tight finite Gram output')
    return out


def measure(values,X,meter):
    if 4*X-1>values['H']: raise ValueError('complete parent and child blocks')
    parent=gram_block(values,X,meter);child=gram_block(values,2*X,meter)
    numeric={f'parent.{k}':v for k,v in parent.items()}
    numeric.update({f'child.{k}':v for k,v in child.items()})
    numeric['drift_R']=child['energy_R']-parent['energy_R']
    numeric['drift_reduced']=child['energy_reduced']-parent['energy_reduced']
    for a,b in PAIRS:numeric[f'gram_drift_{a}_{b}']=child[f'G_{a}_{b}']-parent[f'G_{a}_{b}']
    meter.charge(len(PAIRS)+2)
    return dict(X=X,theta=values['theta'],atoms=list(ATOMS),numeric=numeric,
                coverage=coverage(values['theta'],X,4*X,meter),
                target_domain_dyadic=(X&(X-1))==0,
                fitted_constant=None,uniform_signed_bound_proved=False,RH_proved=False)


def encode(case):
    return dict(case,numeric={k:v.str(45) for k,v in case['numeric'].items()})


def compare(saved,current,meter):
    if {k:v for k,v in saved.items() if k!='numeric'}!={k:v for k,v in current.items() if k!='numeric'}:
        raise ValueError('complete finite case metadata mismatch')
    if set(saved['numeric'])!=set(current['numeric']): raise ValueError('complete finite scalar field set')
    for key,value in current['numeric'].items():
        old=arb(saved['numeric'][key]);meter.charge(8)
        if not tight(old) or not tight(value) or not old.overlaps(value):
            raise ArithmeticError('independent tight interval mismatch '+key)
    return len(current['numeric'])
