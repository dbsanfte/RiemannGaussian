"""Reused-archive proposal Grams and finite interval audits of coupled scales.

The complete f/F is retained. Prime profiles are explicit auxiliaries even
outside their prime-only rough domain. No observation is a uniform theorem.
"""
from fractions import Fraction
import math
import resource
import time

import numpy as np
from flint import arb, ctx
import prime_cofactor_observations as O

CAP = 500_000_000
SECONDS = 600
MAX_H = 262143


class Meter:
    def __init__(self, cap=CAP, seconds=SECONDS):
        if type(cap) is not int or cap < 1 or type(seconds) not in (int,float) or seconds <= 0:
            raise ValueError('positive resource limits')
        self.cap = cap
        self.operations = 0
        self.peak_cells = 0
        self.started = time.monotonic()
        self.deadline = self.started + seconds

    def charge(self, n=1):
        if type(n) is not int or n < 0:
            raise ValueError('nonnegative proxy charge')
        self.operations += n
        if self.operations > self.cap:
            raise OverflowError('coupled evidence operation cap')
        if time.monotonic() > self.deadline:
            raise TimeoutError('coupled evidence deadline')

    def live(self, cells):
        if type(cells) is not int or cells < 0:
            raise ValueError('nonnegative resident cells')
        self.charge()
        self.peak_cells = max(cells,self.peak_cells)
        if cells > 192_000_000:
            raise MemoryError('coupled evidence16GiB proxy cap')

    def counts(self):
        return dict(operations=self.operations,peak_cells=self.peak_cells,
                    elapsed_seconds=time.monotonic()-self.started,
                    operation_cap=self.cap,seconds_cap=self.deadline-self.started,
                    maxrss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)


def _scales(scales):
    if type(scales) not in (tuple,list) or not scales or len(scales)>32:
        raise ValueError('nonempty bounded dyadic scales')
    if any(type(x) is not int or x<1 or x&(x-1) for x in scales):
        raise ValueError('strict dyadic positive integers')
    if list(scales)!=sorted(set(scales)) or 2*max(scales)-1>MAX_H:
        raise ValueError('ascending distinct scales, horizon<=262143')
    return tuple(scales)


def _divisors(divisors):
    if type(divisors) not in (tuple,list) or not divisors or len(divisors)>16:
        raise ValueError('bounded divisor list')
    if any(type(d) is not int or d<1 or d>64 for d in divisors) or list(divisors)!=sorted(set(divisors)):
        raise ValueError('ascending distinct positive divisors<=64')
    return tuple(divisors)


def _cutoff(X):
    y=math.isqrt(2*X)
    return y+(y*y<2*X)


def _profile(handle,state,t,y):
    """Explicit unit+prime profile, with zero below1 and strict lower cutoff."""
    if t<1:
        return arb(0)
    return handle['unit'][state]+handle['profiles'][state][t]-handle['profiles'][state][min(t,y)]


def _number(value):
    result=float(value.mid())
    if not math.isfinite(result):
        raise ArithmeticError('finite proposal midpoint')
    return result


def _ball(value):
    if not value.is_finite():
        raise ArithmeticError('finite audit enclosure')
    return dict(value=_number(value),interval=value.str(65),width=float((value.upper()-value.lower()).upper()))


def _overlap(left,right,meter):
    meter.charge(2)
    if not left.overlaps(right):
        raise ArithmeticError('archived complete-source interval binding failed')


def _gram(handle,X,features):
    meter=handle['meter'];y=_cutoff(X)
    size=1+len(features)
    meter.live(handle['resident_cells']+size*X+size*size+4096)
    meter.charge((2*size*size+5*size)*X)
    values=np.empty((size,X),dtype=float)
    values[0]=handle['F_float'][X:2*X]
    indices=np.arange(X,2*X,dtype=np.int64)
    for j,feature in enumerate(features,1):
        state,d=feature['state'],feature['divisor'];t=indices//d
        prefixes=handle['profile_float'][state]
        values[j]=handle['unit_float'][state]+prefixes[t]-prefixes[np.minimum(t,y)]
        values[j,t==0]=0
    gram=(values@values.T)/(X*X)
    if not np.isfinite(gram).all():
        raise ArithmeticError('finite complete Gram')
    return gram.tolist()


def _prepare(data,rows,polys,Ru,scales,divisors,meter):
    """Arithmetic preparation. Input data is already structure-validated."""
    H=2*max(scales)-1;dimension=len(rows)
    resident=(10+2*dimension)*(H+1)+8192
    meter.live(resident)
    modes=[data['mode:'+name] for name in O.NAMES]
    weights=(arb(9)/2,-arb(9)/2,-Ru,-arb(9)/2)
    primes=O._sieve(H,meter)
    unit=[]
    for row in rows:
        a,b=O._affine(row)[0]
        unit.append(O._real(a)+O._real(b)*Ru)
    profiles=[[arb(0)]*(H+1) for _ in rows]
    profile_float=[np.zeros(H+1) for _ in rows]
    F_float=np.zeros(H+1)
    squared_prefix=[arb(0)]*(H+1)
    cumulative=arb(0);prime_count=0;checks=0
    for j in range(4):
        _overlap(modes[j][1],arb(1),meter);checks+=1
    for n in range(1,H+1):
        meter.charge(30+dimension)
        weighted=[weights[j]*modes[j][n] for j in range(4)]
        _overlap(sum(weighted,arb(0)),data['core'][n],meter)
        cumulative+=data['core'][n]
        _overlap(cumulative,data['F'][n],meter);checks+=2
        F_float[n]=_number(data['F'][n])
        squared_prefix[n]=squared_prefix[n-1]+data['core'][n]**2
        if primes[n]:
            prime_count+=1;meter.charge(64)
            z=1/arb(n).root(6)
            for i,row in enumerate(rows):
                meter.charge(12+16*len(polys[i]))
                expected=sum(((O._real(a)+O._real(b)*Ru)*z**power
                              for power,(a,b) in polys[i].items()),arb(0))
                actual=sum((O._real(a)*value for a,value in zip(row,weighted)),arb(0))
                _overlap(expected,actual,meter);checks+=1
                profiles[i][n]=profiles[i][n-1]+expected
                profile_float[i][n]=_number(profiles[i][n])
        else:
            for i in range(dimension):
                profiles[i][n]=profiles[i][n-1]
                profile_float[i][n]=profile_float[i][n-1]
    for i,row in enumerate(rows):
        _overlap(unit[i],sum((O._real(a)*weights[j]*modes[j][1]
                             for j,a in enumerate(row)),arb(0)),meter);checks+=1
    return dict(meter=meter,H=H,scales=scales,divisors=divisors,dimension=dimension,
                core=data['core'],F=data['F'],F_float=F_float,unit=unit,
                unit_float=[_number(u) for u in unit],profiles=profiles,
                profile_float=profile_float,squared_prefix=squared_prefix,
                resident_cells=resident,source_verified=True,
                audit_checks=checks,prime_count=prime_count)


def build_evidence(archive,basecert,scales=tuple(2**k for k in range(18)),divisors=(1,2,3),meter=None):
    """Return JSON proposal evidence and an opaque reusable interval handle.

    No archive is accessed at import. The caller freezes source/protocol before
    invoking this on research data. Parsing all twelve rows is disclosed even
    though only six vector prefixes are decoded.
    """
    scales=_scales(scales);divisors=_divisors(divisors)
    meter=Meter() if meter is None else meter
    old=ctx.prec;ctx.prec=192
    try:
        rows,polys,_=O._certificate(basecert,meter)
        H=2*max(scales)-1
        data,archive_H,parsed_entries=O._archive(archive,H,meter)
        meter.charge(524)
        z=(arb(2)/3).zeta()
        Ru=(arb(9)/2)*((arb(4)/3).zeta()/(z*z)-1/z)
        if not Ru.is_finite() or not 1<=Ru<=5:
            raise ArithmeticError('actual complete-source R_u domain')
        handle=_prepare(data,rows,polys,Ru,scales,divisors,meter)
        features=[dict(state=i,divisor=d) for i in range(len(rows)) for d in divisors]
        blocks=[]
        for X in scales:
            D=handle['squared_prefix'][4*X-1]/X if 4*X-1<=H else None
            blocks.append(dict(X=X,gram=_gram(handle,X,features),
                               D=None if D is None else _number(D),cutoff=_cutoff(X)))
        evidence=dict(schema='coupled-scale-evidence-v1',features=features,blocks=blocks,
                      verified=True,finite_evidence_only=True,whole_bound_proved=False,
                      source='original_complete_core_f',R_u=Ru.str(65),
                      audit=dict(source_binding_verified=True,overlap_checks=handle['audit_checks'],
                                 all_actual_primes_checked=handle['prime_count'],unit_retained=True),
                      exposure=dict(archive=str(archive),archive_H=archive_H,decoded_H=H,
                                    parsed_scalar_strings=parsed_entries,decoded_scalar_entries=6*(H+1),
                                    structure_rows=12,reused_data=True,new_source_data=False,held_out=False,
                                    complete_source=True,stage033_residual_isolated=False),metadata=meter.counts())
        return evidence,handle
    except BaseException as error:
        error.evidence_counts=meter.counts()
        raise
    finally:
        ctx.prec=old


def _candidates(candidates,handle):
    if type(candidates) is not list or len(candidates)>6:
        raise ValueError('at most six candidate interval audits')
    result=[];seen=set();meter=handle['meter']
    for candidate in candidates:
        if type(candidate) is not dict or set(candidate)!={'id','program','recurrence_C'}:
            raise ValueError('candidate fields id/program/recurrence_C')
        ident=candidate['id']
        if (type(ident) is int and ident>=0) or (type(ident) is str and 1<=len(ident)<=128):
            pass
        else:
            raise ValueError('strict candidate identifier')
        if (type(ident),ident) in seen:
            raise ValueError('unique candidate identifier')
        seen.add((type(ident),ident))
        C=O._q(candidate['recurrence_C'],meter)
        if C<0:
            raise ValueError('nonnegative recurrence C')
        terms=candidate['program']
        if type(terms) is not list or len(terms)>32:
            raise ValueError('bounded complete term list')
        parsed=[]
        for term in terms:
            if type(term) is not dict or set(term)!={'state','divisor','exponent','coefficient'}:
                raise ValueError('strict compensation term fields')
            i,d=term['state'],term['divisor']
            if type(i) is not int or not 0<=i<handle['dimension'] or type(d) is not int or d not in handle['divisors']:
                raise ValueError('declared state/divisor')
            gamma=O._q(term['exponent'],meter);coefficient=O._q(term['coefficient'],meter)
            parsed.append((i,d,gamma,coefficient))
        result.append((ident,parsed,C))
    return result


def _energy(handle,X,terms):
    meter=handle['meter'];y=_cutoff(X)
    factors=[]
    for i,d,gamma,c in terms:
        meter.charge(64)
        factor=O._real(c)*(arb(X).log()*(-O._real(gamma))).exp()
        if not factor.is_finite():
            raise ArithmeticError('finite scale compensation')
        factors.append((i,d,factor))
    full=arb(0);auxiliary=arb(0);cross=arb(0);target=arb(0)
    for n in range(X,2*X):
        meter.charge(14+8*len(terms))
        correction=sum((factor*_profile(handle,i,n//d,y) for i,d,factor in factors),arb(0))
        original=handle['F'][n];G=original+correction
        full+=G*G;auxiliary+=correction*correction
        target+=original*original;cross+=2*original*correction
    scale=X*X
    full/=scale;auxiliary/=scale;target/=scale;cross/=scale
    _overlap(full,target+auxiliary+cross,meter)
    return dict(EG=full,EH=auxiliary,EF=target,cross_twice=cross)


def _status(defect):
    if defect<=0:
        return 'pass'
    if defect>0:
        return 'fail'
    return 'unresolved'


def interval_audit(handle,candidates):
    """Audit up to six frozen programs plus baseline, without reopening archive.

    Tests EG(2X)-EG(X)-C D(X)<=0 on all available adjacent parent scales.
    A pass is a finite interval observation, never a uniform proof certificate.
    """
    meter=handle['meter'];old=ctx.prec;ctx.prec=192
    try:
        if handle.get('source_verified') is not True:
            raise ValueError('independently bound complete-source handle')
        parsed=_candidates(candidates,handle)
        programs=[('baseline',[],Fraction(0))]+parsed
        tables=[]
        for ident,terms,C in programs:
            energies={X:_energy(handle,X,terms) for X in handle['scales']}
            blocks=[dict(X=X,cutoff=_cutoff(X),**{key:_ball(value) for key,value in energies[X].items()})
                    for X in handle['scales']]
            recurrences=[]
            for X in handle['scales']:
                if 2*X not in energies or 4*X-1>handle['H']:
                    continue
                meter.charge(8)
                D=handle['squared_prefix'][4*X-1]/X
                defect=energies[2*X]['EG']-energies[X]['EG']-O._real(C)*D
                recurrences.append(dict(X=X,D=_ball(D),defect=_ball(defect),status=_status(defect)))
            tables.append(dict(id=ident,program=[dict(state=i,divisor=d,exponent=str(g),coefficient=str(c))
                                                 for i,d,g,c in terms],recurrence_C=str(C),
                               blocks=blocks,recurrences=recurrences))
        return dict(schema='coupled-scale-interval-audit-v1',verified=True,
                    finite_evidence_only=True,uniform_recurrence_proved=False,RH_proved=False,
                    source='original_complete_core_f',precision=192,candidates=tables,
                    metadata=meter.counts())
    except BaseException as error:
        error.evidence_counts=meter.counts()
        raise
    finally:
        ctx.prec=old
