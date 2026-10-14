"""Finite, archived full-source prime/cofactor covariance observations.

No producer is imported. Numerical overlaps audit these finite observations;
they never prove an all-prime law or the requested uniform signed bound.
"""
from fractions import Fraction as Q
import gzip
import json
import math
from pathlib import Path
import resource
import time

from flint import arb, ctx

MAX_H = 131071
ARCHIVE_H = 262143
NAMES = ('nu0','nu1','nu2','mu')
VECTOR_NAMES = ('core','F','log_prefix','log_abel') + tuple(
    prefix+name for prefix in ('mode:','prefix:') for name in NAMES)
CAP = 200000000
SECONDS = 180


class Meter:
    def __init__(self, cap=CAP, seconds=SECONDS):
        self.cap, self.operations, self.peak_cells = cap, 0, 0
        self.started = time.monotonic()
        self.deadline = self.started+seconds

    def charge(self, n=1):
        if type(n) is not int or n < 0:
            raise ValueError('nonnegative proxy work')
        self.operations += n
        if self.operations > self.cap:
            raise OverflowError('observation200m operation cap')
        if time.monotonic() > self.deadline:
            raise TimeoutError('observation180s deadline')

    def live(self, cells):
        self.charge()
        self.peak_cells=max(self.peak_cells,cells)
        if cells > 48000000:
            raise MemoryError('observation48m scalar-cell cap')

    def counts(self):
        return dict(operations=self.operations,peak_cells=self.peak_cells,
                    elapsed_seconds=time.monotonic()-self.started,
                    operation_cap=self.cap,seconds_cap=self.deadline-self.started,
                    maxrss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)


def _q(text,meter):
    if type(text) is not str or not 1<=len(text)<=2500:
        raise ValueError('canonical bounded rational')
    meter.charge(1+len(text)//32)
    x=Q(text)
    if str(x)!=text or max(abs(x.numerator).bit_length(),x.denominator.bit_length())>4096:
        raise ValueError('canonical4096-bit rational')
    return x


def _real(q):
    return arb(q.numerator)/q.denominator


def _same(a,b):
    if type(a) is not type(b):return False
    if type(a) is dict:return set(a)==set(b) and all(_same(a[k],b[k]) for k in a)
    if type(a) is list:return len(a)==len(b) and all(_same(x,y) for x,y in zip(a,b))
    return a==b


def _source():
    def a(kind,shift):return dict(kind=kind,shift=shift)
    return dict(lattice=6,channels=[
        dict(atoms=[a('power',2),a('mu',0),a('mu',0)],weight=['9/2','0']),
        dict(atoms=[a('power',2),a('mu',0),a('mu',4)],weight=['-9/2','0']),
        dict(atoms=[a('power',2),a('mu',4)],weight=['0','-1']),
        dict(atoms=[a('mu',0)],weight=['-9/2','0'])])


def _affine(row):
    beta=Q(9,2)
    unit=(beta*(row[0]-row[1]-row[3]),-row[2])
    degrees={0:(beta*(-2*row[0]+row[1]+row[3]),Q(0)),
             2:(beta*(row[0]-row[1]),-row[2]),
             4:(beta*row[1],row[2])}
    return unit,{d:c for d,c in degrees.items() if c!=(0,0)}


def _function(value,meter):
    if type(value) is not dict or set(value)!={'numerator','denominator'}:
        raise ValueError('rational transfer function')
    result={}
    for key in value:
        terms=value[key]
        if type(terms) is not list or len(terms)>256:
            raise ValueError('bounded transfer terms')
        parsed={}
        for term in terms:
            if type(term) is not list or len(term)!=3:
                raise ValueError('transfer monomial')
            i,j,c=term
            if type(i) is not int or type(j) is not int or not 0<=i<=128 or not 0<=j<=32 or (i,j) in parsed:
                raise ValueError('unique bounded transfer degrees')
            parsed[i,j]=_q(c,meter)
        result[key]=parsed
    if not result['denominator']:raise ValueError('nonzero transfer denominator')
    return result


def _certificate(c,meter):
    if type(c) is not dict or not _same(c.get('source'),_source()):
        raise ValueError('original full four-mode source binding')
    basis=c.get('basis')
    if type(basis) is not list or not 1<=len(basis)<=12:
        raise ValueError('bounded state basis')
    rows=[]
    for row in basis:
        if type(row) is not list or len(row)!=4:raise ValueError('four source channels')
        rows.append(tuple(_q(x,meter) for x in row))
    d=len(rows)
    target=c.get('target_row')
    if type(target) is not list or len(target)!=d:raise ValueError('complete target recovery')
    target=tuple(_q(x,meter) for x in target)
    if tuple(sum((target[i]*rows[i][j] for i in range(d)),Q(0)) for j in range(4))!=(1,1,1,1):
        raise ValueError('target is whole original core')
    units=c.get('unit'); bounds=c.get('frontier_bounds'); states=c.get('states')
    if not all(type(x) is list and len(x)==d for x in (units,bounds,states)):
        raise ValueError('every generated state has unit and prime polynomial')
    polys=[]
    for i,row in enumerate(rows):
        if type(states[i]) is not dict or states[i].get('row')!=basis[i]:
            raise ValueError('state expression row matches basis')
        unit,poly=_affine(row)
        u=units[i]
        if type(u) is not dict or set(u)!={'constant','R'} or (_q(u['constant'],meter),_q(u['R'],meter))!=unit:
            raise ValueError('unit includes all signed weights')
        b=bounds[i]
        if type(b) is not dict or type(b.get('state')) is not int or b['state']!=i:
            raise ValueError('state prime polynomial index')
        entries=b.get('prime_polynomial')
        if type(entries) is not list or len(entries)>129:raise ValueError('bounded prime polynomial')
        parsed={}
        for term in entries:
            if type(term) is not list or len(term)!=3 or type(term[0]) is not int or not 0<=term[0]<=128 or term[0] in parsed:
                raise ValueError('prime polynomial degrees')
            parsed[term[0]]=(_q(term[1],meter),_q(term[2],meter))
        if parsed!=poly:raise ValueError('compiled prime polynomial is complete')
        polys.append(poly)
    transfer=c.get('transfer')
    if type(transfer) is not list or len(transfer)!=d:raise ValueError('full transfer matrix')
    functions=[]
    for row in transfer:
        if type(row) is not list or len(row)!=d:raise ValueError('square transfer matrix')
        functions.append([_function(v,meter) for v in row])
    if not _same(c.get('domain'),dict(prime=True,cofactor_coprime=True,all_valuations=True)):
        raise ValueError('prime/copime/all-valuation domain')
    return rows,polys,functions


def _archive(path,H,meter):
    selected={'core','F'}|{'mode:'+name for name in NAMES}
    result={};seen=set();length=None;parsed_entries=0
    max_line=256*(ARCHIVE_H+1)+4096
    with gzip.open(Path(path),'rt',encoding='utf8') as stream:
        while True:
            line=stream.readline(max_line+1)
            if not line:break
            meter.charge(1+len(line)//32)
            meter.live(12*(H+1)+len(line)//4+8192)
            if len(line)>max_line or not line.endswith('\n'):raise ValueError('bounded complete JSONL row')
            row=json.loads(line)
            if type(row) is not dict or set(row)!={'name','values'}:raise ValueError('archive record fields')
            name,values=row['name'],row['values']
            if type(name) is not str or name not in VECTOR_NAMES or name in seen:raise ValueError('unique twelve source rows')
            if type(values) is not list or not H+1<=len(values)<=ARCHIVE_H+1:raise ValueError('archive horizon')
            if length is not None and length!=len(values):raise ValueError('all archive horizons equal')
            length=len(values);seen.add(name);parsed_entries+=length
            meter.charge(length)
            if any(type(v) is not str or not 1<=len(v)<=256 for v in values):raise ValueError('bounded Arb strings')
            if name in selected:
                meter.charge(8*(H+1));data=[arb(v) for v in values[:H+1]]
                if any(not v.is_finite() for v in data) or not data[0].is_zero():raise ValueError('finite archive with index0 zero')
                result[name]=data
    if seen!=set(VECTOR_NAMES):raise ValueError('all twelve original source vectors')
    return result,length-1,parsed_entries


def _sieve(H,meter):
    meter.charge(2*(H+1));prime=bytearray(b'\1')*(H+1)
    prime[0]=0
    if H>=1:prime[1]=0
    for p in range(2,math.isqrt(H)+1):
        meter.charge()
        if prime[p]:
            count=(H-p*p)//p+1;meter.charge(count)
            prime[p*p:H+1:p]=b'\0'*count
    return prime


def _dot(row,values,meter):
    meter.charge(2*len(row))
    return sum((_real(a)*v for a,v in zip(row,values)),arb(0))


def _series(function,z,count,meter):
    polys=[]
    for key in ('numerator','denominator'):
        v=[arb(0)]*(count+1)
        for (i,j),c in function[key].items():
            if j<=count:
                meter.charge(8+i);v[j]+=_real(c)*z**i
        polys.append(v)
    num,den=polys
    if den[0].contains(0):raise ArithmeticError('formal denominator constant separated from zero')
    out=[]
    for e in range(count+1):
        meter.charge(4*(e+1));out.append((num[e]-sum((den[j]*out[e-j] for j in range(1,e+1)),arb(0)))/den[0])
    return out


class _Audit:
    def __init__(self):self.checks=0;self.max_width=arb(0)
    def overlap(self,a,b,meter):
        meter.charge(3);self.checks+=1
        if not a.is_finite() or not b.is_finite() or not a.overlaps(b):
            raise ArithmeticError('finite source identity intervals do not overlap')
        self.width(a);self.width(b)
    def width(self,x):
        if not x.is_finite():raise ArithmeticError('nonfinite observation')
        self.max_width=max(self.max_width,2*x.rad())


def _energy_table(X,state,values,prime_count,audit,meter):
    full,rough,comp,cross=values
    scale=arb(X)**2
    full,rough,comp,cross=[v/scale for v in (full,rough,comp,cross)]
    residual=full-rough-comp-cross
    meter.charge(14)
    if not residual.contains(0):raise ArithmeticError('complete signed energy decomposition')
    for v in (full,rough,comp,cross,residual):audit.width(v)
    diagonal=rough+comp
    ratio=cross/diagonal if diagonal>0 else None
    def number(x):
        v=float(x.mid())
        if not math.isfinite(v):raise ArithmeticError('finite float observation summary')
        return v
    return dict(state=state,X=X,Efull=number(full),Erough=number(rough),Ecomp=number(comp),
        cross_twice=number(cross),cross_to_diagonal=None if ratio is None else number(ratio),
        identity_residual_bound=abs(residual).upper().str(55),
        intervals=dict(Efull=full.str(55),Erough=rough.str(55),Ecomp=comp.str(55),cross_twice=cross.str(55)),
        primecount=prime_count,cutoff=math.isqrt(2*X)+(math.isqrt(2*X)**2<2*X))


def observe_archive(archive_path,certificate,scales=(256,1024,4096,16384,65536)):
    """Observe a frozen certificate on reused finite archived source data."""
    if type(scales) not in (tuple,list) or not 1<=len(scales)<=64 or any(type(X) is not int or X<1 for X in scales):
        raise ValueError('nonempty strict positive integer scales')
    if list(scales)!=sorted(set(scales)):raise ValueError('distinct ascending scales')
    H=2*max(scales)-1
    if H>MAX_H:raise ValueError('observation horizon<=131071')
    meter=Meter();old_precision=ctx.prec;ctx.prec=192
    try:
        rows,polys,functions=_certificate(certificate,meter);d=len(rows)
        data,archive_H,parsed_entries=_archive(archive_path,H,meter)
        meter.charge(524)
        zeta=(arb(2)/3).zeta();zetav=(arb(4)/3).zeta()
        Ru=(arb(9)/2)*(zetav/(zeta*zeta)-1/zeta)
        if not Ru.is_finite() or not 1<=Ru<=5:raise ArithmeticError('actual R_u source domain1..5')
        weights=[arb(9)/2,-arb(9)/2,-Ru,-arb(9)/2]
        modes=[data['mode:'+name] for name in NAMES]
        audit=_Audit();prime=_sieve(H,meter)
        def vector(n):return [w*a[n] for w,a in zip(weights,modes)]
        def state(n):return [_dot(row,vector(n),meter) for row in rows]
        unit_vector=vector(1);unit=state(1)
        for name in NAMES:audit.overlap(data['mode:'+name][1],arb(1),meter)
        for i,row in enumerate(rows):
            a,b=_affine(row)[0];audit.overlap(unit[i],_real(a)+_real(b)*Ru,meter)
        valuations=0
        for p in (2,3,5,7,11,17):
            if p>H:continue
            z=1/arb(p).root(6);meter.charge(64)
            coefficients=[[ _series(f,z,3,meter) for f in row] for row in functions]
            for e in (1,2,3):
                pe=p**e
                for m in range(1,min(31,H//pe)+1):
                    meter.charge()
                    if m%p==0:continue
                    left=state(pe*m);right=state(m)
                    for i in range(d):
                        value=sum((coefficients[i][j][e]*right[j] for j in range(d)),arb(0))
                        meter.charge(2*d);audit.overlap(left[i],value,meter)
                    valuations+=1
        cutoffs={X:math.isqrt(2*X)+(math.isqrt(2*X)**2<2*X) for X in scales}
        wanted=set(cutoffs.values());at_cutoff={};active={};tables=[]
        cumulative=[arb(0)]*4;prime_cumulative=[arb(0)]*4
        prime_total=0;prime_counts={};prime_audits=0;block_entries=0
        meter.live(12*(H+1)+128*d*len(scales)+8192)
        for n in range(1,H+1):
            meter.charge(25)
            if n in cutoffs:
                y=cutoffs[n]
                if n-1>y:
                    rough=[u+a-b for u,a,b in zip(unit_vector,prime_cumulative,at_cutoff[y])]
                    count=prime_total-prime_counts[y]
                else:rough=unit_vector[:];count=0
                active[n]=dict(rough=rough,count=count,sums=[[arb(0)]*4 for _ in rows])
            weighted=vector(n)
            audit.overlap(sum(weighted,arb(0)),data['core'][n],meter)
            cumulative=[a+b for a,b in zip(cumulative,weighted)]
            audit.overlap(sum(cumulative,arb(0)),data['F'][n],meter)
            if prime[n]:
                prime_total+=1;prime_cumulative=[a+b for a,b in zip(prime_cumulative,weighted)]
                z=1/arb(n).root(6);meter.charge(64)
                for i,row in enumerate(rows):
                    expected=sum(((_real(a)+_real(b)*Ru)*z**power for power,(a,b) in polys[i].items()),arb(0))
                    meter.charge(16*len(polys[i]));audit.overlap(_dot(row,weighted,meter),expected,meter)
                prime_audits+=1
            if n in wanted:
                at_cutoff[n]=prime_cumulative[:];prime_counts[n]=prime_total
            for X,record in list(active.items()):
                if prime[n] and n>cutoffs[X]:
                    record['rough']=[a+b for a,b in zip(record['rough'],weighted)];record['count']+=1
                for i,row in enumerate(rows):
                    full=_dot(row,cumulative,meter);rough=_dot(row,record['rough'],meter)
                    comp=full-rough;sums=record['sums'][i]
                    sums[0]+=full*full;sums[1]+=rough*rough;sums[2]+=comp*comp;sums[3]+=2*rough*comp
                    meter.charge(14);block_entries+=1
                if n==2*X-1:
                    tables.extend(_energy_table(X,i,values,record['count'],audit,meter)
                                  for i,values in enumerate(record['sums']))
                    del active[X]
        if active:raise AssertionError('every full declared block completed')
        return dict(schema='prime-cofactor-observations-v1',verified=True,
            finite_evidence_only=True,whole_signed_bound_proved=False,RH_proved=False,
            source='original_complete_core_f',R_u=Ru.str(55),rows=sorted(tables,key=lambda r:(r['state'],r['X'])),
            audit=dict(verified=True,interval_overlap_checks=audit.checks,
                       all_prime_polynomial_checks=prime_audits,valuation_cofactor_cases=valuations,
                       valuation_primes=[p for p in (2,3,5,7,11,17) if p<=H],
                       valuation_exponents=[1,2,3],cofactor_maximum=31,
                       coefficient_and_prefix_checks=H,unit_verified=True,
                       max_interval_width=float(audit.max_width.upper())),
            exposure=dict(archive=str(archive_path),archive_H=archive_H,decoded_H=H,
                decoded_vectors=['core','F']+['mode:'+name for name in NAMES],
                decoded_scalar_entries=6*(H+1),parsed_scalar_strings=parsed_entries,
                complete_archive_structure_rows=12,generated_state_block_entries=block_entries,
                original_coefficients_accessed=[0,H],original_unit_included=True,
                all_primes_and_composites_through_H_retained=True,
                reused_previously_verified_data=True,new_source_data=False,held_out=False,
                basis_rows=[list(map(str,row)) for row in rows],scales=list(scales),
                stage033_residual_isolated=False),metadata=meter.counts())
    except BaseException as error:
        error.observation_counts=meter.counts()
        raise
    finally:
        ctx.prec=old_precision
