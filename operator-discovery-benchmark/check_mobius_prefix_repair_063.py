"""Independent finite short repair rules and complete floor-matrix replay.

No producer, source/LP data or Mobius inverse is used by this verifier.
Source binding is intentionally delegated to whole-candidate062 admission.
"""
from fractions import Fraction as Q
from math import gcd,prod
import check_mobius_mass_conservation_060 as MASS

Meter=MASS.Meter
RULES=('raw','zero','left','right','linear','reciprocal_linear','core','core_inverse')
MAX_H=4096


def _arrays(obj,H,m):
    if type(obj) is not list or len(obj)!=2:raise ValueError('two complete short arrays')
    result=[]
    for row in obj:
        if type(row) is not list or len(row)!=H:raise ValueError('every short index present at both endpoints')
        result.append([MASS._rational(x,m) for x in row])
    return result


def _fills(residuals,H,ps,rule,m):
    R=prod(ps);coprime=[gcd(d,R)==1 for d in range(1,H+1)]
    m.charge(H*(10+R.bit_length()))
    left=[0]*H;right=[0]*H;last=1
    for i in range(H):
        if coprime[i]:last=i+1
        left[i]=last;m.charge(2)
    last=H+1
    for i in range(H-1,-1,-1):
        if coprime[i]:last=i+1
        right[i]=last;m.charge(2)
    fills=[[],[]]
    for i in range(H):
        d=i+1
        core=d
        if rule in ('core','core_inverse'):
            for p in ps:
                while core%p==0:core//=p;m.charge(4)
        for e in range(2):
            row=residuals[e]
            if coprime[i] or rule=='raw':value=row[i]
            elif rule=='zero':value=Q(0)
            elif rule in ('core','core_inverse'):
                value=row[core-1]
                if rule=='core_inverse':value/=d//core
            else:
                a,b=left[i],right[i];u=row[a-1];v=row[b-1] if b<=H else Q(0)
                if rule=='left':value=u
                elif rule=='right':value=v
                elif rule=='linear':value=(b-d)*u/(b-a)+(d-a)*v/(b-a)
                else:value=Q(a*(b-d),d*(b-a))*u+Q(b*(d-a),d*(b-a))*v
            fills[e].append(MASS._bounded(value,m))
    return fills,coprime


def verify_repair(cert,meter=None):
    m=Meter() if meter is None else meter
    MASS._fields(cert,('schema','primes','H','rule','residuals','filled','coefficients','coefficient_l1'))
    MASS._expect(cert['schema'],'mobius-short-repair-v1')
    ps=cert['primes']
    if type(ps) is not list or not 2<=len(ps)<=8:raise ValueError('bounded registered prime mask')
    for p in ps:MASS._prime(p,m)
    if ps!=sorted(set(ps)):raise ValueError('distinct ascending actual primes')
    H=cert['H']
    if type(H) is not int or not 1<=H<=MAX_H:raise ValueError('bounded complete short horizon')
    rule=cert['rule']
    if type(rule) is not str or rule not in RULES:raise ValueError('recognized universal repair fill rule')
    residuals=_arrays(cert['residuals'],H,m)
    filled=_arrays(cert['filled'],H,m)
    coefficients=_arrays(cert['coefficients'],H,m)
    expected,coprime=_fills(residuals,H,ps,rule,m)
    if filled!=expected:raise ValueError('filled array does not implement complete repair rule')
    claimed=cert['coefficient_l1']
    if type(claimed) is not list or len(claimed)!=2:raise ValueError('two exact coefficient L1 costs')
    claimed=[MASS._rational(x,m) for x in claimed]
    prices=[];suprema=[];first_moments=[]
    for e in range(2):
        suffix=[Q(0)]*(H+1);price=Q(0);first=Q(0)
        for i in range(H-1,-1,-1):
            suffix[i]=MASS._bounded(suffix[i+1]+coefficients[e][i],m)
            price=MASS._bounded(price+abs(coefficients[e][i]),m)
            first=MASS._bounded(first+(i+1)*coefficients[e][i],m)
        for d in range(1,H+1):
            value=Q(0)
            for j in range(d,H+1,d):value=MASS._bounded(value+suffix[j-1],m)
            if value!=filled[e][d-1]:raise ValueError('complete forward floor identity fails')
        if price!=claimed[e]:raise ValueError('complete exact coefficient L1 price')
        prices.append(str(price));suprema.append(str(max(map(abs,filled[e]))));first_moments.append(str(first))
    m.charge(100)
    return {'verified':True,'schema':'verified-mobius-short-repair-v1','primes':ps,'H':H,'rule':rule,
        'rows_checked_per_endpoint':H,'coprime_rows_preserved':sum(coprime),
        'unit_preserved':True,'all_coprime_rows_including_squareful':True,
        'virtual_endpoint':{'index':H+1,'value':'0'},
        'repair_identity':'filled(d)=sum_(j=1..H)c_j*floor(j/d), every positive integer d',
        'repair_identity_proved':True,'beyond_H_zero_proved':True,
        'forward_replay':'A_j=sum_(l>=j)c_l; filled(d)=sum_(m<=H/d)A_(m*d)',
        'coefficient_l1':prices,'filled_sup_norm':suprema,
        'first_moment':first_moments,'first_moment_equals_input_unit':True,
        'universal_positive_envelope':'||c||_1<=2*H*(1+log(H))*||filled||_infinity',
        'universal_positive_envelope_proved':True,
        'original_source_binding_proved':False,'whole_candidate_requires_062_admission':True,
        'uniform_N_growth_proved':False,'whole_signed_target_bound_proved':False,'RH_proved':False,
        'scientific_source_or_LP_evaluated':False}
