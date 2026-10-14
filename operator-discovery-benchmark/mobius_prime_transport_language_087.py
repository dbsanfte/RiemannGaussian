"""Exact source-profile atoms for generic prime transport, in original coordinates.

This is a local symbolic rewrite and atom compiler, not a remaining-kernel
bound. A certified prime p pairs each squarefree p-coprime m with pm. Source
weights are capped by pm<=N using max cutoffs. The separate endpoint atoms
are possible partners; only their PLUS sum is the arithmetic annihilator.
No unknown actual Mobius signs, null-basis rotation, or scientific search is
used. All cofactor and prime guards remain explicit, including complements.
"""
from fractions import Fraction as Q
from math import gcd, isqrt

from flint import fmpq_mat
import mobius_coupled_completion_083 as B

MAX_TERMS = 256
MAX_ATOMS = 64
MAX_RATIONAL_BITS = 4096
MAX_ARITHMETIC_BITS = 100000
MAX_PRIME_TRIALS = 1000000
ATOM_KEYS = {'schema','endpoint','prime','mask','kernel','cofactor_cut',
             'prime_cut','cofactor_gate_multiplier'}


def _reserve(meter, count=1, bits=64, work=0, resident=0):
    if bits > MAX_ARITHMETIC_BITS:
        raise B.ResourceLimit('transport prospective arithmetic bit gate')
    simultaneous = max(resident,getattr(meter,'_transport_context_resident',0))
    meter.reserve(simultaneous+65536+max(1,count)*(2048+8*bits))
    meter.charge(work)


def _rational(value):
    if type(value) is not str or len(value) > 2500:
        raise B.ResourceLimit('transport bounded canonical rational input')
    return B.OLD.rational(value)


def _checked(q):
    if max(abs(q.numerator).bit_length(),q.denominator.bit_length()) > MAX_RATIONAL_BITS:
        raise B.ResourceLimit('transport exact rational4096bit gate')
    return q


def _add(a, b, meter):
    common = gcd(a.denominator,b.denominator)
    left,right = b.denominator//common,a.denominator//common
    bits = max(abs(a.numerator).bit_length()+left.bit_length(),
               abs(b.numerator).bit_length()+right.bit_length())+1
    denbits = a.denominator.bit_length()+left.bit_length()
    if max(bits,denbits) > MAX_RATIONAL_BITS:
        raise B.ResourceLimit('transport prospective rational sum4096bit gate')
    _reserve(meter,bits=max(bits,denbits),work=bits+denbits)
    return _checked(a+b)


def _mul(a, b, meter):
    # Cross cancellation first, then estimate the actual reduced product.
    g = gcd(abs(a.numerator),b.denominator)
    h = gcd(abs(b.numerator),a.denominator)
    bits = (abs(a.numerator)//g).bit_length()+(abs(b.numerator)//h).bit_length()
    denbits = (a.denominator//h).bit_length()+(b.denominator//g).bit_length()
    if max(bits,denbits) > MAX_RATIONAL_BITS:
        raise B.ResourceLimit('transport prospective rational product4096bit gate')
    _reserve(meter,bits=max(bits,denbits),work=bits+denbits)
    return _checked(a*b)


def certify_prime(prime, meter=None):
    """Exact bounded trial division, with no probable-prime admission."""
    meter = meter or B.Meter()
    if type(prime) is not int or prime < 2:
        raise ValueError('literal integer actual prime>=2 required')
    if prime.bit_length() > MAX_RATIONAL_BITS:
        raise B.ResourceLimit('transport prime integer4096bit gate')
    root = isqrt(prime)
    trials = max(0,(root-1)//2)
    if trials > MAX_PRIME_TRIALS:
        raise B.ResourceLimit('transport prospective exact prime trial-count gate')
    _reserve(meter,bits=prime.bit_length(),work=(trials+1)*max(1,prime.bit_length())**2)
    if prime != 2 and prime % 2 == 0:raise ValueError('transport integer is composite')
    for divisor in range(3,root+1,2):
        if prime % divisor == 0:raise ValueError('transport integer is composite')
    return dict(prime=prime,method='EXACT_TRIAL_DIVISION',checked_through=root,
                odd_trial_count=trials,probable_prime_test_used=False)


def canonical_kernel(terms, meter=None):
    """Combine equal positive rational cutoffs exactly; remove zero weights."""
    meter = meter or B.Meter()
    if type(terms) is not list or len(terms) > MAX_TERMS:
        raise ValueError('transport complete step kernel<=256 terms')
    _reserve(meter,count=max(1,len(terms)),work=32*max(1,len(terms)))
    parsed = []
    for row in terms:
        if type(row) is not dict or set(row) != {'divisor','weight'}:
            raise ValueError('transport exact step kernel keys')
        divisor,weight = _rational(row['divisor']),_rational(row['weight'])
        if divisor <= 0:raise ValueError('transport positive rational cutoff divisor')
        parsed.append((divisor,weight))
    vals = [q for row in parsed for q in row]
    bits = B.OLD.rational_budget(vals,meter,terms=max(1,len(terms)))
    _reserve(meter,count=max(1,len(terms)),bits=bits,
             work=max(1,len(terms))*max(1,len(terms).bit_length())*max(1,bits))
    combined = {}
    for divisor,weight in parsed:
        combined[divisor] = _add(combined.get(divisor,Q(0)),weight,meter)
    return [dict(divisor=str(divisor),weight=str(combined[divisor]))
            for divisor in sorted(combined) if combined[divisor]]


def _kernel_budget(kernel, meter):
    weights = [_rational(row['weight']) for row in kernel]
    bits = B.OLD.rational_budget(weights,meter,terms=max(1,len(weights)))
    if bits > MAX_RATIONAL_BITS:
        raise B.ResourceLimit('transport prospective complete profile sum4096bit gate')
    return bits


def cap_profile(kernel, source_index, prime, d_min, *, memory, meter=None):
    """Generic max-cutoff rule, supporting rational step-kernel divisors."""
    meter = meter or B.Meter()
    if type(memory) is not int or not 1 <= memory <= 3 or type(source_index) is not int or not 0 <= source_index <= memory:
        raise ValueError('transport source index must be within source memory')
    certify_prime(prime,meter)
    minimum = _rational(d_min)
    if minimum <= 0:raise ValueError('transport positive full-horizon divisor')
    source = canonical_kernel(kernel,meter)
    if source and any(_rational(row['divisor']) < minimum for row in source):
        raise ValueError('transport d_min cannot exceed a source divisor')
    cap = _mul(minimum,Q(prime),meter)
    terms = []
    for row in source:
        shifted = _mul(_rational(row['divisor']),Q(1 << source_index),meter)
        terms.append(dict(divisor=str(max(shifted,cap)),weight=row['weight']))
    result = canonical_kernel(terms,meter)
    _kernel_budget(result,meter)
    return result


def parse_cut(descriptor):
    if descriptor is None:return None
    if type(descriptor) is not dict or set(descriptor) != {'scale','u_exponent','complement'}:
        raise ValueError('transport exact symbolic cut keys')
    scale,exponent = _rational(descriptor['scale']),_rational(descriptor['u_exponent'])
    if scale <= 0 or type(descriptor['complement']) is not bool:
        raise ValueError('transport positive cut scale and strict complement flag')
    return dict(scale=str(scale),u_exponent=str(exponent),complement=descriptor['complement'])


def compile_transport(program, source_index, prime, *, cofactor_cut=None,
                      prime_cut=None, meter=None):
    """Compile a source-bound local identity and its separate partner atoms."""
    meter = meter or B.Meter()
    p = B.parse_program(program)
    if type(source_index) is not int or not 0 <= source_index <= p['memory']:
        raise ValueError('transport source index must bind source memory')
    prime_certificate = certify_prime(prime,meter)
    cofactor_cut,prime_cut = parse_cut(cofactor_cut),parse_cut(prime_cut)
    source = [dict(divisor=str(Q(d)),weight=str(w)) for d,w in p['kernel']]
    d_min = str(Q(p['kernel'][0][0]))
    capped = cap_profile(source,source_index,prime,d_min,memory=p['memory'],meter=meter)
    product = canonical_kernel([dict(divisor=str(_mul(_rational(row['divisor']),Q(1,prime),meter)),weight=row['weight'])
                                for row in capped],meter)
    common = dict(schema='prime-transport-atom-v1',prime=prime,cofactor_cut=cofactor_cut,prime_cut=prime_cut)
    cofactor_atom = dict(common,endpoint='cofactor',mask='not_divisible',kernel=capped,cofactor_gate_multiplier='1')
    product_atom = dict(common,endpoint='product',mask='divisible',kernel=product,cofactor_gate_multiplier=str(prime))
    return dict(schema='prime-transport-language-v1',prime=prime,prime_certificate=prime_certificate,
                source_index=source_index,memory=p['memory'],d_min=d_min,source_kernel=source,
                cofactor_atom=cofactor_atom,product_atom=product_atom,
                identity_pairing='COFACTOR_PLUS_PRODUCT',local_max_cutoff_rewrite_proved=True,
                original_boolean_coordinates_retained=True,unknown_actual_Mobius_signs_used=False,
                uniform_remaining_bound_proved=False,RH_proved=False)


def _geometry_gate(model, atoms=1, bits=64, work=0):
    G,E = model['squarefree_count'],model['price_dimension']
    if type(atoms) is not int or not 0 <= atoms <= MAX_ATOMS:
        raise ValueError('transport atom roster<=64')
    if not model['program']['prime_anchor']:
        raise ValueError('transport original complete unit/prime anchor required')
    if not 0 <= G <= B.MAX_COORDINATES or not 0 <= E <= B.MAX_COORDINATES:
        raise B.ResourceLimit('transport complete raw/anchored coordinate gate')
    if len(model['coordinates']) != G or len(model['known_signs']) != G:
        raise ValueError('transport complete raw geometry shape')
    storage = max(1,atoms)*(G+E)*(2048+8*bits)
    model['meter']._transport_context_resident = model['resident_bytes']+model['extra_resident_bytes']+storage
    _reserve(model['meter'],bits=bits,work=work,
             resident=model['resident_bytes']+model['extra_resident_bytes']+storage)
    return storage


def _cut_value(model, descriptor):
    parsed = parse_cut(descriptor)
    if parsed is None:return None
    cut = dict(scale=_rational(parsed['scale']),u_exponent=_rational(parsed['u_exponent']),
               n_exponent=Q(0),complement=parsed['complement'],unit_balance=False)
    return B.cut_value(1,model['u'],model['N'],cut,model['meter'])


def _parse_atom(atom, meter):
    if type(atom) is not dict or set(atom) != ATOM_KEYS or atom['schema'] != 'prime-transport-atom-v1':
        raise ValueError('transport exact endpoint atom schema')
    prime = atom['prime']
    certify_prime(prime,meter)
    endpoint = atom['endpoint']
    if endpoint not in ('cofactor','product'):
        raise ValueError('transport endpoint domain')
    if atom['mask'] != ('not_divisible' if endpoint == 'cofactor' else 'divisible'):
        raise ValueError('transport endpoint divisibility mask binding')
    if atom['cofactor_gate_multiplier'] != ('1' if endpoint == 'cofactor' else str(prime)):
        raise ValueError('transport literal cofactor gate multiplier binding')
    canonical = canonical_kernel(atom['kernel'],meter)
    if atom['kernel'] != canonical:raise ValueError('transport kernel must be canonical')
    _kernel_budget(canonical,meter)
    cofactor,guard = parse_cut(atom['cofactor_cut']),parse_cut(atom['prime_cut'])
    return prime,endpoint,canonical,cofactor,guard


def _step_value(kernel, u, n, meter):
    total = Q(0)
    for divisor,weight in kernel:
        bits = max(abs(divisor.numerator).bit_length()+n.bit_length(),
                   u.bit_length()+divisor.denominator.bit_length())+1
        _reserve(meter,bits=bits,work=bits)
        if divisor.numerator*n <= u*divisor.denominator:
            total = _add(total,weight,meter)
    return total


def evaluate_step_kernel(kernel, u, n, meter=None):
    meter = meter or B.Meter()
    if type(u) is not int or type(n) is not int or min(u,n) < 1 or max(u.bit_length(),n.bit_length()) > MAX_RATIONAL_BITS:
        raise ValueError('transport positive bounded integer profile arguments')
    canonical = canonical_kernel(kernel,meter)
    _kernel_budget(canonical,meter)
    parsed = [(_rational(row['divisor']),_rational(row['weight'])) for row in canonical]
    return _step_value(parsed,u,n,meter)


def _anchor(model, raw):
    if len(raw) != model['squarefree_count']:
        raise ValueError('transport complete raw vector required')
    if not raw:return []
    first = Q(0)
    for value,known in zip(raw,model['known_signs']):
        if int(known):first = _add(first,_mul(value,Q(int(known)),model['meter']),model['meter'])
    return [first]+[raw[int(i)] for i in model['composite_indices']]


def evaluate_atom(model, atom):
    """Exact complete endpoint vector; it is not separately a zero identity."""
    _geometry_gate(model)
    prime,endpoint,kernel,cut,guard = _parse_atom(atom,model['meter'])
    bits = _kernel_budget(kernel,model['meter'])
    storage = _geometry_gate(model,bits=bits,work=32*model['squarefree_count']*max(1,len(kernel)))
    K,prime_K = _cut_value(model,cut),_cut_value(model,guard)
    enabled = prime_K is None or prime <= prime_K
    # Keep p*K exactly. floor(p*a*u^eta) would change the symbolic cut.
    gate_bound = None
    if K is not None:
        multiplier = prime if endpoint == 'product' else 1
        _reserve(model['meter'],bits=multiplier.bit_length()+max(1,K.bit_length()),work=16)
        gate_bound = multiplier*K
    parsed = [(_rational(row['divisor']),_rational(row['weight'])) for row in kernel]
    raw = []
    for coordinate in model['coordinates']:
        n = int(coordinate)
        mask = n % prime != 0 if endpoint == 'cofactor' else n % prime == 0
        allowed = enabled and mask and (gate_bound is None or n <= gate_bound)
        raw.append(_step_value(parsed,model['u'],n,model['meter']) if allowed else Q(0))
    anchored = _anchor(model,raw)
    model['extra_resident_bytes'] += storage
    return dict(raw_vector=list(map(str,raw)),anchored_vector=list(map(str,anchored)),
                squarefree_count=model['squarefree_count'],effective_dimension=model['price_dimension'],
                endpoint=endpoint,prime=prime,cofactor_cut_value=K,literal_cofactor_gate_bound=gate_bound,
                prime_cut_value=prime_K,prime_guard_enabled=enabled,
                original_boolean_coordinates_retained=True,separate_atom_zero_claimed=False)


def combine_evaluations(model, evaluations, coefficients):
    """Rational complete-vector combinations for a future partner search."""
    if type(evaluations) is not list or type(coefficients) is not list or len(evaluations) != len(coefficients):
        raise ValueError('transport complete rational atom coefficient shape')
    _geometry_gate(model,atoms=len(evaluations))
    weights = [_rational(value) for value in coefficients]
    G = model['squarefree_count']
    raw = [Q(0)]*G
    for evaluation,weight in zip(evaluations,weights):
        if type(evaluation) is not dict or type(evaluation.get('raw_vector')) is not list or len(evaluation['raw_vector']) != G:
            raise ValueError('transport complete raw atom evaluation binding')
        values = [_rational(value) for value in evaluation['raw_vector']]
        for i,value in enumerate(values):raw[i] = _add(raw[i],_mul(weight,value,model['meter']),model['meter'])
    anchored = _anchor(model,raw)
    storage = _geometry_gate(model,bits=max([64]+[max(abs(v.numerator).bit_length(),v.denominator.bit_length()) for v in raw]))
    model['extra_resident_bytes'] += storage
    return dict(raw_vector=list(map(str,raw)),anchored_vector=list(map(str,anchored)),
                squarefree_count=G,effective_dimension=model['price_dimension'],
                coefficients=list(coefficients),original_boolean_coordinates_retained=True,
                separate_atom_zero_claimed=False)


def evaluate_transport(model, transport):
    """Bind source and geometry, expose both partner atoms and their zero sum."""
    if type(transport) is not dict or transport.get('schema') != 'prime-transport-language-v1':
        raise ValueError('transport source-bound compiled schema')
    _geometry_gate(model,atoms=3)
    expected = compile_transport(model['raw'],transport['source_index'],transport['prime'],
                                 cofactor_cut=transport['cofactor_atom']['cofactor_cut'],
                                 prime_cut=transport['cofactor_atom']['prime_cut'],meter=model['meter'])
    if expected != transport:raise ValueError('transport complete source/endpoint compiler binding')
    cofactor = evaluate_atom(model,transport['cofactor_atom'])
    product = evaluate_atom(model,transport['product_atom'])
    identity = combine_evaluations(model,[cofactor,product],['1','1'])
    identity.update(identity_pairing='COFACTOR_PLUS_PRODUCT',
                    actual_Mobius_zero_by_local_prime_pair_rule=True,uniform_remaining_bound_proved=False,RH_proved=False)
    return dict(cofactor_atom=cofactor,product_atom=product,identity=identity,
                partner_atoms=[cofactor,product],ops=model['meter'].ops,
                prospective_peak_bytes=model['meter'].peak_bytes)


def combine_atoms(model, atoms, coefficients):
    if type(atoms) is not list or type(coefficients) is not list or len(atoms) != len(coefficients):
        raise ValueError('transport complete symbolic atom coefficient shape')
    _geometry_gate(model,atoms=len(atoms))
    # Validate coefficient inputs before creating any endpoint-vector arrays.
    for coefficient in coefficients:_rational(coefficient)
    return combine_evaluations(model,[evaluate_atom(model,atom) for atom in atoms],coefficients)


def native_vector(model, evaluation, *, anchored=True):
    if type(anchored) is not bool:raise ValueError('transport strict original coordinate choice')
    _geometry_gate(model)
    key = 'anchored_vector' if anchored else 'raw_vector'
    n = model['price_dimension'] if anchored else model['squarefree_count']
    if type(evaluation) is not dict or type(evaluation.get(key)) is not list or len(evaluation[key]) != n:
        raise ValueError('transport complete native vector binding')
    values = [_rational(v) for v in evaluation[key]]
    return fmpq_mat([[str(q)] for q in values]) if n else fmpq_mat(0,1)
