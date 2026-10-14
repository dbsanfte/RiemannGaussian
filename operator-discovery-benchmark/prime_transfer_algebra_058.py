"""Exact detector for valuation-complete prime transfer identities.

The finite signature is sufficient for all x>0,t>0. No norm, source value,
proof provider or existing scientific artifact is read or evaluated.
"""
from fractions import Fraction as Q
from itertools import product
import math
import time

MAX_UNIVERSE = 4
MAX_PRIME = 1_000_000
MAX_ATOMS = 512
MAX_EXPONENT = 16
MAX_ATTENUATION_DEGREE = 8
MAX_INTEGER_BITS = 4096
MAX_FRACTION_BITS = 8192
MAX_STATES = 4096
MAX_ROWS = 20000
MAX_SIGNATURE_TERMS = 2_000_000
MAX_CACHE_BYTES = 256*1024**2
MAX_WORKING_BYTES = 2*1024**3


class Meter:
    def __init__(self, cap=5_000_000_000, seconds=7200):
        if type(cap) is not int or cap < 0:
            raise ValueError('nonnegative work cap')
        if type(seconds) not in (int, float) or not math.isfinite(seconds) or seconds <= 0:
            raise ValueError('positive finite deadline')
        self.cap, self.operations = cap, 0
        self.deadline = time.monotonic()+seconds
        self.peak_bytes_estimate = 0
        self.primitives = {name: 0 for name in ('prime_trial_divisions','factor_divisions',
            'grammar_atoms','valuation_atom_cases','polynomial_terms','pivot_checks',
            'fraction_operations','row_updates','relation_replay_terms','cache_hits')}

    def charge(self, amount=1):
        if type(amount) is not int or amount < 0 or amount > self.cap-self.operations:
            raise OverflowError('transfer algebra work cap')
        self.operations += amount
        if time.monotonic() > self.deadline:
            raise TimeoutError('transfer algebra deadline')

    def reserve(self, amount):
        if type(amount) is not int or not 0 <= amount <= MAX_WORKING_BYTES:
            raise MemoryError('transfer algebra prospective memory cap')
        self.peak_bytes_estimate = max(self.peak_bytes_estimate, amount)
        self.charge()

    def counts(self):
        return {'operations': self.operations, 'peak_bytes_estimate': self.peak_bytes_estimate,
                'total_primitive_counts': dict(self.primitives)}


def _meter(meter):
    return Meter() if meter is None else meter


def _universe(universe, meter):
    if type(universe) is not list or not 1 <= len(universe) <= MAX_UNIVERSE:
        raise ValueError('bounded nonempty sorted prime universe')
    for p in universe:
        if type(p) is not int or not 2 <= p <= MAX_PRIME:
            raise ValueError('actual bounded prime')
        for d in range(2, math.isqrt(p)+1):
            meter.primitives['prime_trial_divisions'] += 1
            meter.charge(4)
            if p % d == 0:
                raise ValueError('actual prime required')
    if sorted(set(universe)) != universe:
        raise ValueError('canonical sorted distinct prime universe')
    return tuple(universe)


def _factor(integer, universe, meter):
    if type(integer) is not int or integer < 1:
        raise ValueError('positive actual integer atom parameter')
    if integer.bit_length() > MAX_INTEGER_BITS:
        raise OverflowError('atom parameter integer bit cap')
    rest, exponents = integer, []
    for p in universe:
        exponent = 0
        while rest % p == 0:
            rest //= p
            exponent += 1
            meter.primitives['factor_divisions'] += 1
            meter.charge(4+rest.bit_length())
            if exponent > MAX_EXPONENT:
                raise OverflowError('atom valuation resource cap')
        exponents.append(exponent)
    if rest != 1:
        raise ValueError('divisor/attenuation factors must lie in the universe')
    return tuple(exponents)


def _atoms(atoms, universe, meter):
    if type(atoms) is not list or not 1 <= len(atoms) <= MAX_ATOMS:
        raise ValueError('bounded nonempty atom list')
    result = []
    for atom in atoms:
        if type(atom) is not dict or set(atom) != {'primes','divisor','attenuation'}:
            raise ValueError('exact prime/divisor/attenuation atom schema')
        subset = atom['primes']
        if (type(subset) is not list or any(type(p) is not int for p in subset)
                or sorted(set(subset)) != subset or not set(subset) <= set(universe)):
            raise ValueError('canonical subset of actual universe primes')
        d = _factor(atom['divisor'], universe, meter)
        a = _factor(atom['attenuation'], universe, meter)
        result.append((tuple(subset), atom['divisor'], atom['attenuation'], d, a))
    if len(set(result)) != len(result):
        raise ValueError('distinct atom columns required')
    return tuple(result)


def grammar(universe, meter=None, max_attenuation_degree=2):
    """Declared complexity grammar, with no identities supplied as input."""
    meter = _meter(meter)
    before = meter.counts()
    primes = _universe(universe, meter)
    if (type(max_attenuation_degree) is not int
            or not 0 <= max_attenuation_degree <= MAX_ATTENUATION_DEGREE):
        raise ValueError('bounded nonnegative attenuation degree')
    count = (1 << len(primes))*(len(primes)+1)*math.comb(len(primes)+max_attenuation_degree,len(primes))
    if count > MAX_ATOMS:
        raise OverflowError('declared grammar atom cap')
    subsets = [tuple(p for j,p in enumerate(primes) if mask & (1 << j))
               for mask in range(1 << len(primes))]
    exponents = sorted((e for e in product(range(max_attenuation_degree+1), repeat=len(primes))
                        if sum(e) <= max_attenuation_degree),
                       key=lambda e:(sum(e),e))
    attenuations = [math.prod(p**e for p,e in zip(primes, powers)) for powers in exponents]
    meter.reserve(1024+count*1024)
    atoms = [{'primes':list(subset),'divisor':d,'attenuation':a}
             for subset in subsets for d in (1,*primes) for a in attenuations]
    for atom in atoms:
        _factor(atom['attenuation'],primes,meter)
    meter.primitives['grammar_atoms'] += count
    meter.charge(count*16)
    return {'schema':'prime-transfer-grammar-v1','universe':list(primes),'atoms':atoms,
            'metadata':{'subset_rule':'all subsets in ascending bit mask',
                'divisor_rule':'1 followed by all universe primes',
                'attenuation_rule':'all prime monomials up to declared total degree; degree then exponent lex order',
                'max_attenuation_degree':max_attenuation_degree,
                'atom_count':count,'scientific_source_values_evaluated':False,
                'winner_identity_supplied':False},'counts':_delta(before,meter.counts())}


class Context:
    def __init__(self,max_bytes=MAX_CACHE_BYTES):
        if type(max_bytes) is not int or not 0 <= max_bytes <= MAX_CACHE_BYTES:
            raise ValueError('bounded literal signature cache')
        self.max_bytes,self.bytes_estimate,self.signatures=max_bytes,0,{}


def prepare_context(meter=None,max_bytes=MAX_CACHE_BYTES):
    meter=_meter(meter)
    meter.reserve(1024)
    return Context(max_bytes)


def _delta(before,after):
    return {'operations':after['operations']-before['operations'],
            'peak_bytes_estimate':after['peak_bytes_estimate'],
            'total_primitive_counts':{k:after['total_primitive_counts'][k]-before['total_primitive_counts'][k]
                                      for k in after['total_primitive_counts']}}


def _build(universe,atoms,meter,context):
    primes=_universe(universe,meter)
    compiled=_atoms(atoms,primes,meter)
    key=(primes,compiled)
    if key in context.signatures:
        meter.primitives['cache_hits']+=1
        meter.charge()
        return primes,compiled,context.signatures[key]
    caps=tuple(max(atom[3][j] for atom in compiled)+1 for j in range(len(primes)))
    states=math.prod(cap+1 for cap in caps)
    worst_terms=states*len(compiled)*(1 << len(primes))
    if states>MAX_STATES or worst_terms>MAX_SIGNATURE_TERMS:
        raise OverflowError('complete valuation/polynomial signature resource cap')
    meter.reserve(context.bytes_estimate+1024+states*128+worst_terms*192)
    table={}
    for valuation in product(*(range(cap+1) for cap in caps)):
        for column,(subset,_,_,d,a) in enumerate(compiled):
            meter.primitives['valuation_atom_cases']+=1
            meter.charge(4+len(primes))
            if any(v<e for v,e in zip(valuation,d)):
                continue
            active=[j for j,p in enumerate(primes) if p in subset or valuation[j]>d[j]]
            polynomial=[(a,1)]
            for j in active:
                added=[]
                for powers,coefficient in polynomial:
                    shifted=list(powers);shifted[j]+=1
                    added.append((tuple(shifted),-coefficient))
                polynomial+=added
            for monomial,coefficient in polynomial:
                row=table.setdefault((valuation,monomial),{})
                row[column]=coefficient
                meter.primitives['polynomial_terms']+=1
                meter.charge(4+len(monomial))
    if len(table)>MAX_ROWS:
        raise OverflowError('signature row resource cap')
    rows=tuple((state,monomial,tuple(sorted(entries.items())))
               for (state,monomial),entries in sorted(table.items()))
    data=(caps,rows)
    size=1024+sum(256+len(entries)*96 for _,_,entries in rows)
    if size <= context.max_bytes-context.bytes_estimate:
        context.signatures[key]=data
        context.bytes_estimate+=size
    return primes,compiled,data


def _public_atoms(compiled):
    return [{'primes':list(s),'divisor':d,'attenuation':a} for s,d,a,_,_ in compiled]


def _summary(primes,compiled,data):
    caps,rows=data
    return {'valuation_caps':list(caps),
            'valuation_state_count':math.prod(cap+1 for cap in caps),
            'state_semantics':'0..cap inclusive; cap represents every valuation>=cap',
            'matrix_shape':[len(rows),len(compiled)],
            'nonzero_entries':sum(len(entries) for _,_,entries in rows),
            'row_order':'valuation tuple then monomial exponent tuple, lexicographic',
            'outside_prime_factors':'common product for primes outside universe',
            'unit_state_included':True,'x_domain':'all real x>0', 't_domain':'all real t>0'}


def signature(universe,atoms,meter=None,context=None):
    meter=_meter(meter);before=meter.counts()
    context=prepare_context(meter) if context is None else context
    if type(context) is not Context:
        raise ValueError('producer-owned signature context')
    primes,compiled,data=_build(universe,atoms,meter,context)
    return {'schema':'prime-transfer-signature-v1','universe':list(primes),
            'atoms':_public_atoms(compiled),**_summary(primes,compiled,data),
            'rows':[{'valuations':list(state),'monomial':list(monomial),
                     'entries':[{'column':column,'value':value} for column,value in entries]}
                    for state,monomial,entries in data[1]],'counts':_delta(before,meter.counts())}


def _fraction_op(a,b,operation,meter):
    meter.primitives['fraction_operations']+=1
    meter.charge(8+abs(a.numerator).bit_length()+a.denominator.bit_length()
                 +abs(b.numerator).bit_length()+b.denominator.bit_length())
    value=a*b if operation=='multiply' else a/b if operation=='divide' else a+b if operation=='add' else a-b
    if max(abs(value.numerator).bit_length(),value.denominator.bit_length())>MAX_FRACTION_BITS:
        raise OverflowError('exact elimination fraction bit cap')
    return value


def _subtract(row,pivot,factor,meter):
    for column,value in pivot.items():
        result=_fraction_op(row.get(column,Q(0)),
                            _fraction_op(factor,value,'multiply',meter),'subtract',meter)
        if result:
            row[column]=result
        else:
            row.pop(column,None)
    meter.primitives['row_updates']+=1


def _rref(rows,columns,meter,context_bytes):
    # Full Fraction numerator/denominator bit envelope plus serialized basis.
    cell_bytes=160+2*((MAX_FRACTION_BITS+7)//8)
    output_cell_bytes=128+(2*MAX_FRACTION_BITS*30103)//100000
    meter.reserve(context_bytes+1024+len(rows)*columns*cell_bytes
                  +columns*columns*output_cell_bytes)
    matrix=[{column:Q(value) for column,value in entries} for _,_,entries in rows]
    pivots=[]
    for column in range(columns):
        selected=None
        for j in range(len(pivots),len(matrix)):
            meter.primitives['pivot_checks']+=1
            meter.charge()
            if column in matrix[j]:
                selected=j;break
        if selected is None:
            continue
        rank=len(pivots)
        matrix[rank],matrix[selected]=matrix[selected],matrix[rank]
        pivot=matrix[rank]
        scale=pivot[column]
        if scale!=1:
            for c in list(pivot):
                pivot[c]=_fraction_op(pivot[c],scale,'divide',meter)
        for j in range(rank+1,len(matrix)):
            if column in matrix[j]:
                _subtract(matrix[j],pivot,matrix[j][column],meter)
        pivots.append(column)
    # Exact backward elimination, yielding unique RREF pivot rows.
    for i in reversed(range(len(pivots))):
        column=pivots[i]
        for j in range(i):
            if column in matrix[j]:
                _subtract(matrix[j],matrix[i],matrix[j][column],meter)
    if any(matrix[j] for j in range(len(pivots),len(matrix))):
        raise ArithmeticError('nonzero row without pivot')
    return tuple(pivots),matrix[:len(pivots)]


def discover(universe,atoms,meter=None,context=None):
    """Infer the complete rational nullspace of the declared finite signature."""
    meter=_meter(meter);before=meter.counts()
    context=prepare_context(meter) if context is None else context
    if type(context) is not Context:
        raise ValueError('producer-owned signature context')
    primes,compiled,data=_build(universe,atoms,meter,context)
    columns=len(compiled)
    pivots,rref=_rref(data[1],columns,meter,context.bytes_estimate)
    free=tuple(c for c in range(columns) if c not in pivots)
    relations=[]
    for column in free:
        vector=[Q(0)]*columns
        vector[column]=Q(1)
        for pivot,row in zip(pivots,rref):
            vector[pivot]=-row.get(column,Q(0))
        for _,_,entries in data[1]:
            total=Q(0)
            for c,value in entries:
                meter.primitives['relation_replay_terms']+=1
                meter.charge(2+abs(vector[c].numerator).bit_length()+vector[c].denominator.bit_length())
                term=vector[c] if value==1 else -vector[c] if value==-1 else _fraction_op(Q(value),vector[c],'multiply',meter)
                total=_fraction_op(total,term,'add',meter)
            if total:
                raise ArithmeticError('nullspace replay failed')
        relations.append({'coefficients':[str(v) for v in vector], 'free_column':column,
                          'nonzero_count':sum(bool(v) for v in vector)})
    return {'schema':'prime-transfer-discovery-v1','universe':list(primes),
            'atoms':_public_atoms(compiled),'rank':len(pivots),'nullity':len(free),
            'pivot_columns':list(pivots),'free_columns':list(free),'relations':relations,
            'signature_summary':_summary(primes,compiled,data),
            'rref_rows':[{'pivot_column':pivot,
                          'entries':[{'column':c,'value':str(v)} for c,v in sorted(row.items())]}
                         for pivot,row in zip(pivots,rref)],
            'identity_scope':'all x>0,t>0, inclusive n1; exact radical prime source',
            'complete_for_declared_signature':True,'all_arithmetic_identities_claimed':False,
            'norm_bound_proved':False,'rh_proved':False,
            'scientific_source_values_evaluated':False,'winner_identity_supplied':False,
            'artifact_hashes_used':False,'counts':_delta(before,meter.counts())}
