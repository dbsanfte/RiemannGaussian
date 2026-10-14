"""Private recursive calibration sources and the complete archived core.

Instances are materialized only after the orchestrator freezes the learner and
checker. A callable is an interface boundary, not a hostile-code sandbox.
No frozen producer, digest wrapper, or actual source reconstruction is used.
"""
from fractions import Fraction
import gzip
import json
from pathlib import Path
import random

from flint import arb, ctx

MAX_DIMENSION = 12
MAX_BITS = 4096
MAX_HORIZON = 262143
VECTOR_NAMES = ('core', 'F', 'log_prefix', 'log_abel') + tuple(
    prefix + name for prefix in ('mode:', 'prefix:')
    for name in ('nu0', 'nu1', 'nu2', 'mu'))


def _charge(meter, work=1):
    if meter is not None:
        meter.charge(work)


def _live(meter, cells):
    if meter is not None and hasattr(meter, 'live'):
        meter.live(cells)


def _rational(text, meter):
    if type(text) is not str or not 1 <= len(text) <= 2500:
        raise ValueError('bounded canonical rational string')
    _charge(meter, 1 + len(text) // 32)
    try:
        value = Fraction(text)
    except (ValueError, ZeroDivisionError) as error:
        raise ValueError('canonical rational string') from error
    if str(value) != text or max(abs(value.numerator).bit_length(),
                                 value.denominator.bit_length()) > MAX_BITS:
        raise ValueError('canonical rational within4096 bits')
    return value


def _compile(model, meter):
    if type(model) is not dict or set(model) != {'base', 'matrices', 'initial', 'output'}:
        raise ValueError('exact recursive model fields')
    base = model['base']
    if type(base) is not int or base not in (2, 3):
        raise ValueError('base2 or3')
    initial, output, matrices = model['initial'], model['output'], model['matrices']
    if type(initial) is not list or not 1 <= len(initial) <= MAX_DIMENSION:
        raise ValueError('dimension1..12')
    d = len(initial)
    if type(output) is not list or len(output) != d or type(matrices) is not list or len(matrices) != base:
        raise ValueError('full scalar output and every digit matrix')
    _live(meter, (base + 2)*d*d + 4*d)
    v = tuple(_rational(x, meter) for x in initial)
    t = tuple(_rational(x, meter) for x in output)
    parsed = []
    for matrix in matrices:
        if type(matrix) is not list or len(matrix) != d:
            raise ValueError('square digit matrices')
        rows = []
        for row in matrix:
            if type(row) is not list or len(row) != d:
                raise ValueError('square digit matrices')
            values = tuple(_rational(x, meter) for x in row)
            _charge(meter, 2*d)
            if sum(map(abs, values), Fraction(0)) > 1:
                raise ValueError('every matrix row L1<=1')
            rows.append(values)
        parsed.append(tuple(rows))
    _charge(meter, d*d)
    if tuple(sum((a*x for a, x in zip(row, v)), Fraction(0))
             for row in parsed[0]) != v:
        raise ValueError('unit consistency M0 initial=initial')
    return base, tuple(parsed), v, t


def validate_model(model, meter=None):
    """Strictly validate; bools and noncanonical rationals are rejected."""
    _compile(model, meter)
    return True


def _evaluate(compiled, n, meter):
    if type(n) is not int or n < 0 or n.bit_length() > MAX_BITS:
        raise ValueError('nonnegative integer index within4096 bits')
    base, matrices, initial, output = compiled
    digits = []
    while n:
        _charge(meter, 2)
        n, digit = divmod(n, base)
        digits.append(digit)
    state = initial
    d = len(initial)
    _live(meter, base*d*d + 4*d + len(digits))
    for digit in reversed(digits):
        _charge(meter, 2*d*d)
        state = tuple(sum((a*x for a, x in zip(row, state)), Fraction(0))
                      for row in matrices[digit])
        if any(max(abs(x.numerator).bit_length(), x.denominator.bit_length()) > MAX_BITS
               for x in state):
            raise OverflowError('evaluated rational4096-bit cap')
    _charge(meter, 2*d)
    value = sum((a*x for a, x in zip(output, state)), Fraction(0))
    if max(abs(value.numerator).bit_length(), value.denominator.bit_length()) > MAX_BITS:
        raise OverflowError('output rational4096-bit cap')
    return value


def evaluate_model(model, n, meter=None):
    """Return exact x(n)=output * M_digits * initial, including x(0)."""
    return _evaluate(_compile(model, meter), n, meter)


def model_source(model, meter=None):
    """Compile once and return an anonymous exact callable.

    The generator is never passed the model or private expected labels. Python
    callable introspection is not a security barrier against malicious code.
    """
    compiled = _compile(model, meter)
    def source(n):
        return _evaluate(compiled, n, meter)
    return source


def load_complete_core(path, H, meter=None):
    """Read previously verified full-core Arb vectors; return x(n)=f(n+1).

    The loader checks archive structure, not a new arithmetic proof. The runner
    must bind the archive to its frozen independent audit. No modes are removed
    and no current-stage residual or transport is substituted for f.
    """
    if type(H) is not int or not 1 <= H <= MAX_HORIZON:
        raise ValueError('complete requested horizon1..262143')
    path = Path(path)
    if not 128 <= ctx.prec <= 256:
        raise ValueError('128..256 bit Arb archive decode')
    expected, seen, length, core = set(VECTOR_NAMES), set(), None, None
    # Bound a single line before json allocation, including complete row text.
    max_line = 256*(MAX_HORIZON + 1) + 4096
    with gzip.open(path, 'rt', encoding='utf8') as stream:
        while True:
            line = stream.readline(max_line + 1)
            if not line:
                break
            _charge(meter, 1 + len(line)//32)
            _live(meter, 2*(H+1) + len(line)//4 + 4096)
            if len(line) > max_line or not line.endswith('\n'):
                raise ValueError('bounded complete JSONL record')
            row = json.loads(line)
            if type(row) is not dict or set(row) != {'name', 'values'}:
                raise ValueError('exact vector record fields')
            name, values = row['name'], row['values']
            if type(name) is not str or name not in expected or name in seen:
                raise ValueError('unique complete source vector names')
            if type(values) is not list or not H+1 <= len(values) <= MAX_HORIZON+1:
                raise ValueError('complete source vector horizon')
            if length is not None and len(values) != length:
                raise ValueError('same horizon for every signed source vector')
            length = len(values)
            _charge(meter, len(values))
            if any(type(x) is not str or not 1 <= len(x) <= 256 for x in values):
                raise ValueError('bounded Arb string values')
            seen.add(name)
            if name == 'core':
                _charge(meter, 8*(H+1))
                core = tuple(arb(x) for x in values[:H+1])
                if any(not x.is_finite() for x in core) or not core[0].is_zero():
                    raise ValueError('finite complete core, index0 padding zero')
    if seen != expected or core is None:
        raise ValueError('all four modes, prefixes, and complete core required')
    def source(n):
        if type(n) is not int or not 0 <= n < H:
            raise ValueError('source n in0..H-1; unit is core[1]')
        _charge(meter)
        return core[n+1]
    metadata = dict(schema='complete-core-source-adapter-v1', archive=str(path),
        H=H, archive_H=length-1, max_source_index=H-1, number_kind='arb_enclosure',
        precision=ctx.prec, source_index='x(n)=core[n+1]', includes_unit=True,
        includes_all_four_signed_modes=True, source='original_complete_core_f',
        source_formula='(9/2)K*(mu*mu)-(9/2)K*(mu*mu_(2/3))-R_u*K*mu_(2/3)-(9/2)mu',
        original_archive_input='candidate10_joint_preconditioner_obligation.json',
        current_parent_input='candidate10_moment_region_obligation.json',
        inherited_transport='g=f-e remains in the authoritative parent; this branch bounds f directly',
        stage033_component_isolated=False, new_source_observations=False,
        universal_closure_verified=False, whole_signed_bound_proved=False, RH_proved=False,
        source_binding='runner verifies archived independent audit and parent bytes')
    return source, metadata


def _identity(d):
    return [[Fraction(i == j) for j in range(d)] for i in range(d)]


def _multiply(a, b):
    return [[sum((x*y for x, y in zip(row, column)), Fraction(0))
             for column in zip(*b)] for row in a]


def _encode(base, matrices, initial, output):
    return dict(base=base, matrices=[[[str(x) for x in row] for row in a] for a in matrices],
                initial=list(map(str, initial)), output=list(map(str, output)))


def _coupled(rng, base, d, kind):
    """Private generic rational source constructor, not a target answer."""
    permutation = list(range(d)); rng.shuffle(permutation)
    P = [[Fraction(j == permutation[i]) for j in range(d)] for i in range(d)]
    order = list(range(d)); rng.shuffle(order)
    J = [[Fraction(0) for _ in range(d)] for _ in range(d)]
    for left, right in zip(order[::2], order[1::2]):
        sign = rng.choice((-1, 1)); J[left][right] = Fraction(sign); J[right][left] = Fraction(-sign)
    I = _identity(d)
    if kind == 'signed':
        a, b = Fraction(0), Fraction(1)
    else:
        a = rng.choice(tuple(map(Fraction, ('-1/2', '-1/3', '1/3', '1/2'))))
        b = 1-abs(a)
    branch = [[a*I[i][j]+b*J[i][j] for j in range(d)] for i in range(d)]
    matrices = [P, _multiply(P, branch)]
    if base == 3:
        reverse = [[a*I[i][j]-b*J[i][j] for j in range(d)] for i in range(d)]
        matrices.append(_multiply(P, reverse))
    output = [Fraction(rng.choice((-2, -1, 1, 2)), rng.choice((1, 2, 3))) for _ in range(d)]
    return _encode(base, matrices, [Fraction(1)]*d, output)


def _tensor(a, b):
    def matrix(x, y):
        return [[Fraction(x[i][j])*Fraction(y[k][l])
                 for j in range(len(x)) for l in range(len(y))]
                for i in range(len(x)) for k in range(len(y))]
    return _encode(a['base'], [matrix(x, y) for x, y in zip(a['matrices'], b['matrices'])],
        [Fraction(x)*Fraction(y) for x in a['initial'] for y in b['initial']],
        [Fraction(x)*Fraction(y) for x in a['output'] for y in b['output']])


def create_challenges(directory, seed, meter=None, *, frozen):
    """Materialize private instances ONLY after an external source freeze.

    Return anonymous {id,model_file,truth_file} rows, paths relative to directory.
    Expected labels are posthoc categories, not supplied proofs or exponents.
    This function cannot independently establish that the orchestrator froze.
    """
    if frozen is not True:
        raise ValueError('challenge materialization requires completed external freeze')
    if type(seed) is not int or not 0 <= seed < 2**64:
        raise ValueError('declared64-bit integer challenge seed')
    rng = random.Random(seed)
    private = Path(directory)/'private'
    private.mkdir(parents=True, exist_ok=False)
    entries = []
    kinds = [('signed',2,2),('signed',2,4),('fractional',2,2),('fractional',2,4),
             ('signed',3,2),('fractional',3,4)]
    cases = []
    for kind, base, d in kinds:
        cases.append((_coupled(rng,base,d,kind), dict(category='coupled_'+kind,
                      expected='global_admission_or_explicit_grammar_limit', source_is_recursive=True)))
    for base in (2,3):
        cases.append((_tensor(_coupled(rng,base,2,'signed'), _coupled(rng,base,2,'fractional')),
                      dict(category='tensor_mixed_channels', expected='admission_or_explicit_grammar_limit',
                           source_is_recursive=True)))
        cases.append((_encode(base,[[[Fraction(1)]]]*base,[Fraction(1)],[Fraction(1)]),
                      dict(category='noncancelling_control', expected='linear_prefix', source_is_recursive=True)))
    d = 10; I = _identity(d)
    advance = [[Fraction(j == min(i+1,d-1)) for j in range(d)] for i in range(d)]
    cases.append((_encode(3,[I,I,advance],[Fraction(1)]*(d-1)+[Fraction(-1)],
                         [Fraction(1)]+[Fraction(0)]*(d-1)),
                  dict(category='long_transient_control', expected='reject_false_finite_closure_or_linear_prefix',
                       source_is_recursive=True)))
    rng.shuffle(cases)
    for index, (model, truth) in enumerate(cases, 1):
        validate_model(model, meter)
        _charge(meter, 32*model['base']*len(model['initial'])**3)
        name = 'challenge-%03d' % index
        row = dict(id=name,model_file='private/'+name+'.json',truth_file='private/'+name+'.truth.json')
        for relative, data in ((row['model_file'], model), (row['truth_file'], truth)):
            encoded = json.dumps(data, sort_keys=True, indent=2)+'\n'
            _charge(meter, len(encoded))
            with (Path(directory)/relative).open('x', encoding='utf8') as stream:
                stream.write(encoded)
        entries.append(row)
    return entries
