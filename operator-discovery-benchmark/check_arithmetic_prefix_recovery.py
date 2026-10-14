"""Independent exact certificates for arithmetic prefix recovery.

The certificate proves a uniform operator bound, not a residual estimate.
No candidate/source evaluation or producer import belongs in this checker.
"""
from fractions import Fraction


SCHEMA = 'arithmetic-prefix-recovery-v1'
MAX_WITNESS = 64
MAX_DIVISOR = 4096
MAX_BITS = 4096


def _require(condition, message):
    if not condition:
        raise ValueError(message)


def _rational(value, meter):
    """Read canonical bounded rational text, rejecting bool/coercion aliases."""
    meter.charge()
    _require(type(value) is str and 1 <= len(value) <= 2500,
             'bounded canonical recovery rational string')
    meter.charge(len(value) // 32 + 1)
    parts = value.split('/')
    _require(1 <= len(parts) <= 2, 'integer or reduced rational syntax')
    integers = []
    for part in parts:
        digits = part[1:] if part.startswith('-') else part
        _require(bool(digits) and len(digits) <= 1234
                 and all('0' <= c <= '9' for c in digits),
                 'bounded decimal rational component')
        meter.charge(len(digits))
        number = int(part)
        _require(abs(number).bit_length() <= MAX_BITS, 'recovery integer bit cap')
        integers.append(meter.number(number))
    if len(integers) == 2:
        _require(integers[1] > 0, 'positive recovery denominator')
    result = meter.number(Fraction(*integers))
    _require(str(result) == value, 'canonical reduced recovery rational')
    return result


def _json_cells(value, meter, depth=0):
    meter.charge()
    if depth > 32:
        raise OverflowError('recovery metadata depth cap')
    if type(value) is dict:
        _require(len(value) <= 32, 'bounded recovery object')
        total = 1
        for key, item in value.items():
            _require(type(key) is str and len(key) <= 128,
                     'bounded recovery JSON keys')
            total += _json_cells(key, meter, depth + 1)
            total += _json_cells(item, meter, depth + 1)
    elif type(value) is list:
        _require(len(value) <= 4096, 'bounded recovery JSON list')
        total = 1
        for item in value:
            total += _json_cells(item, meter, depth + 1)
    elif type(value) is str:
        _require(len(value) <= 2500, 'bounded recovery JSON text')
        meter.charge(len(value) // 32)
        total = 1 + len(value) // 32
    elif type(value) is int:
        _require(abs(value).bit_length() <= MAX_BITS, 'recovery JSON bit cap')
        meter.number(value)
        total = 1
    else:
        _require(value is None or type(value) is bool, 'strict recovery JSON scalar')
        total = 1
    if total > 20000:
        raise OverflowError('recovery metadata cell cap')
    return total


def verify_witness(divisors, meter):
    """Recompute the conservative infinite-tail coefficient independently.

    Sequence linkage is a separate required certificate check. This helper
    verifies only the bounded ordered witness and its exact rational bounds.
    """
    meter.charge()
    _require(type(divisors) is list and 1 <= len(divisors) <= MAX_WITNESS,
             'one to64 recovery divisors')
    meter.live(8 * len(divisors) + 64)
    previous = 1
    coefficient = Fraction(0)
    for j, divisor in enumerate(divisors, 1):
        meter.charge(4)
        _require(type(divisor) is int and previous < divisor <= MAX_DIVISOR,
                 'strict increasing integer dilations in2..4096')
        meter.number(divisor)
        term = meter.number(Fraction(1, meter.number(j * divisor)))
        coefficient = meter.number(coefficient + term)
        previous = divisor
    coefficient = meter.number(coefficient + Fraction(1, len(divisors) + 1))
    _require(0 < coefficient < 1, 'strict recovery contraction witness')
    margin = meter.number(1 - coefficient)
    norm_bound = meter.number(Fraction(2) / margin)
    squared_bound = meter.number(norm_bound * norm_bound)
    return dict(c=str(coefficient), norm_bound=str(norm_bound),
                squared_bound=str(squared_bound))
