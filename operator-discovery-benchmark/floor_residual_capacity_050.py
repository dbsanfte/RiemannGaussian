"""Capacity configuration for isolated, unchanged 044 norm proof engines.

Resource constants and bounded decimal serialization/parsing calls change.
Arithmetic and proof formulas remain unchanged. This module makes no source-
binding claim and does not extend the separate 047 identity checker. Fixed-
vector norm certificates retain the original schema and mathematical providers.
"""
import ast
import importlib.util
from fractions import Fraction
from pathlib import Path
import resource
import time

ROOT = Path(__file__).resolve().parent
INDEX_LIMIT = 5000
SUPPORT_LIMIT = 4096
INPUT_BITS = 4096
WORKING_BITS = 16384
AGGREGATE_BYTES = 16 * 1024**3
PARENT_ALLOWANCE_BYTES = 2 * 1024**3
CONVERSION_OPERATIONS = 0


def _format_integer(value):
    global CONVERSION_OPERATIONS
    if type(value) is not int or abs(value).bit_length() > WORKING_BITS:
        raise OverflowError('bounded exact formatter integer cap')
    negative, value = value < 0, abs(value)
    chunks = []
    while value:
        CONVERSION_OPERATIONS += max(1, value.bit_length())
        value, remainder = divmod(value, 10**18)
        chunks.append(remainder)
    if not chunks:
        return '0'
    return ('-' if negative else '') + str(chunks[-1]) + ''.join(
        str(chunk).zfill(18) for chunk in reversed(chunks[:-1]))


def format_exact(value):
    """Canonical bounded int/Fraction formatting without global guard changes."""
    if type(value) is int:
        return _format_integer(value)
    if type(value) is Fraction:
        numerator = _format_integer(value.numerator)
        return numerator if value.denominator == 1 else numerator+'/'+_format_integer(value.denominator)
    return str(value)


def _parse_integer(text):
    global CONVERSION_OPERATIONS
    if type(text) is not str or not text or len(text) > 5000:
        raise ValueError('bounded canonical decimal integer')
    negative = text.startswith('-')
    digits = text[1:] if negative else text
    if (not digits or not digits.isascii() or not digits.isdecimal() or
            (len(digits) > 1 and digits[0] == '0') or (negative and digits == '0')):
        raise ValueError('canonical decimal integer')
    value = 0
    first = len(digits) % 18 or 18
    for start in range(0, len(digits), 18):
        # A short initial chunk is followed by fixed18-digit chunks.
        offset = 0 if start == 0 else first+(start//18-1)*18
        width = first if start == 0 else 18
        chunk = digits[offset:offset+width]
        value = value*10**len(chunk)+int(chunk)
        CONVERSION_OPERATIONS += max(1, value.bit_length())
        if value.bit_length() > WORKING_BITS:
            raise OverflowError('bounded exact parser integer cap')
    return -value if negative else value


def parse_exact(text):
    """Parse a canonical rational output, with each integer bounded to16384bits."""
    if type(text) is not str or text.count('/') > 1:
        raise ValueError('canonical bounded rational text')
    if '/' not in text:
        return Fraction(_parse_integer(text))
    numerator, denominator = text.split('/')
    a, b = _parse_integer(numerator), _parse_integer(denominator)
    if b <= 1:
        raise ValueError('canonical rational denominator')
    value = Fraction(a, b)
    if format_exact(value) != text:
        raise ValueError('reduced canonical rational')
    return value


def _bounded_int(value=0, *args, **kwargs):
    return _parse_integer(value) if type(value) is str and not args and not kwargs else int(value, *args, **kwargs)


def _bounded_fraction(*args, **kwargs):
    return parse_exact(args[0]) if len(args) == 1 and type(args[0]) is str and not kwargs else Fraction(*args, **kwargs)


def isolated(filename, name):
    spec = importlib.util.spec_from_file_location(name, ROOT / filename)
    module = importlib.util.module_from_spec(spec)
    # Only decimal constructor/formatter calls are redirected. Type names,
    # checks, arithmetic, providers and diagnostic .str calls stay unchanged.
    replacements = {'str': '_bounded_str_050', 'int': '_bounded_int_050',
                    'F': '_bounded_fraction_050'}
    class Conversions(ast.NodeTransformer):
        def visit_Call(self, node):
            self.generic_visit(node)
            if isinstance(node.func, ast.Name) and node.func.id in replacements:
                node.func.id = replacements[node.func.id]
            return node
    tree = Conversions().visit(ast.parse((ROOT / filename).read_text(), filename=str(ROOT / filename)))
    ast.fix_missing_locations(tree)
    module.__dict__.update(_bounded_str_050=format_exact,
                           _bounded_int_050=_bounded_int,
                           _bounded_fraction_050=_bounded_fraction)
    exec(compile(tree, str(ROOT / filename), 'exec'), module.__dict__)
    return module


INTERVAL = isolated('floor_residual_interval_044.py', 'floor_capacity_interval_050')
CHECK = isolated('check_floor_residual_arguments_044.py', 'floor_capacity_checker_050')
if (INTERVAL.MAX_SUPPORT, INTERVAL.MAX_INDEX, INTERVAL.MAX_PARAMETER_BITS,
        INTERVAL.MAX_INTEGER_BITS, CHECK.MAX_SUPPORT, CHECK.MAX_INDEX,
        CHECK.MAX_BITS, CHECK.MAX_RESULT_BITS) != (2048, 4096, 4096, 8192,
                                                  2048, 4096, 4096, 8192):
    raise ValueError('expected frozen 044 resource configuration')
INTERVAL.MAX_SUPPORT = CHECK.MAX_SUPPORT = SUPPORT_LIMIT
INTERVAL.MAX_INDEX = CHECK.MAX_INDEX = INDEX_LIMIT
INTERVAL.MAX_INTEGER_BITS = CHECK.MAX_RESULT_BITS = WORKING_BITS

_preflight_operations = 0
_worker_kernel = None


def memory_preflight(programs, H, workers=2):
    """Return prospective aggregate bytes; never allocate the event arrays.

    Workers execute one program at a time. The retained Jordan sieve is charged
    at the configured maximum index, including when a prior task had larger K.
    This is an estimate with parent allowance, not an operating-system quota.
    Every later arithmetic, memory and time guard remains active. Decimal
    adapters have their own16384-bit cap and leave the native global guard
    active; preflight alone does not certify that a program can be evaluated.
    """
    global _preflight_operations
    if type(H) is not int or not 0 <= H <= INTERVAL.MAX_H:
        raise ValueError('integer horizon within unchanged 044 limit')
    if type(workers) is not int or not 1 <= workers <= 2:
        raise ValueError('one or two workers within aggregate budget')
    reserves = []
    for program in programs:
        meter = INTERVAL.Meter()
        try:
            lattice = INTERVAL.integer_lattice(program, meter)
            if any(q > H for q, _ in lattice['steps']):
                raise ValueError('horizon must cover all step thresholds')
            support = len(program['coefficients']) + len(program['steps'])
            K = program['coefficients'][-1]['n'] if program['coefficients'] else 1
            extra = ((INDEX_LIMIT + 1) * 64 +
                     (K + 1) * (384 + (lattice['early_bound_num'].bit_length()+7)//8))
            meter.reserve(H, lattice['event_abs'].bit_length(), support, extra)
            reserves.append(meter.counts()['peak_bytes_estimate'])
        finally:
            _preflight_operations += meter.operations
    aggregate = workers * max(reserves, default=0) + PARENT_ALLOWANCE_BYTES
    if aggregate > AGGREGATE_BYTES:
        raise MemoryError('aggregate worker/parent memory preflight exceeds16GiB')
    return aggregate


def audit_one(task):
    """Certify one supplied fixed vector; independently replay at256 bits.

    Safe for fork workers. The coefficient-free Jordan cache is local to each
    worker; it contains no source coefficients or previous norm observations.
    """
    global _worker_kernel
    if type(task) is not dict or set(task) != {'program', 'H'}:
        raise ValueError('task requires exactly program,H')
    program, H = task['program'], task['H']
    started = time.monotonic()
    conversions_before = CONVERSION_OPERATIONS
    preflight_before = _preflight_operations
    memory_preflight([program], H, workers=2)
    if _worker_kernel is None:
        _worker_kernel = INTERVAL.JordanKernel()
    meter = INTERVAL.Meter(cap=6_000_000_000, seconds=7200)
    certificate = INTERVAL.certify(program, H=H, precision=192, meter=meter,
                                   kernel=_worker_kernel)
    proof_meter = CHECK.Meter(cap=18_000_000_000)
    checked = CHECK.verify_norm(program, certificate, meter=proof_meter)
    if not checked['verified'] or not checked['all_domain_included'] or checked['convergence_proved']:
        raise ValueError('whole-domain admission failed')
    return dict(id=program['id'], certificate=certificate, verification=checked,
                producer_counts=meter.counts(), checker_operations=proof_meter.operations,
                conversion_operations=CONVERSION_OPERATIONS-conversions_before,
                preflight_operations=_preflight_operations-preflight_before,
                elapsed_seconds=time.monotonic()-started,
                worker_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
