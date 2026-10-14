"""Independent, exact admission for signed prime/composite storage (073).

No producer, search code, or prior checker is imported.  Source admission
uses an Eratosthenes factor sieve and an offline two-coordinate prefix sum.
Finite evidence never establishes a uniform recurrence or an RH theorem.
"""
from array import array
from fractions import Fraction
from math import gcd, isqrt
import re
import sys


MAX_BITS = 100000
MAX_INTEGER = (1 << MAX_BITS) - 1
INPUT_BITS = 4096
# Formatting admitted exact witnesses needs up to 30103 decimal digits.
if hasattr(sys, "set_int_max_str_digits") and 0 < sys.get_int_max_str_digits() < 31000:
    sys.set_int_max_str_digits(31000)
# This process's conservative allocation budget leaves room under the 16 GiB
# aggregate gate for the producer, learner, runner, and loaded JSON inputs.
MEMORY_BUDGET = 2 * 1024**3
_RATIONAL = re.compile(r"(?:0|-?[1-9][0-9]*)(?:/[1-9][0-9]*)?\Z")
_BASE_LABELS = ["Z", "unit", "omega1", "omega2", "omega3", "omega_ge4"]
_FLAGS = {"uniform_domination_proved": True,
          "uniform_recurrence_proved": False,
          "uniform_head_bound_proved": False, "RH_proved": False}


class AdmissionError(ValueError):
    pass


class ResourceLimit(AdmissionError):
    pass


class Meter:
    """Count elementary integer/array actions, including sieve/root/Fenwick work."""
    def __init__(self, limit=500000000):
        if type(limit) is not int or limit < 0:
            raise ValueError("meter limit must be a nonnegative integer")
        self.limit = limit
        self.ops = 0

    def charge(self, count=1):
        if type(count) is not int or count < 0:
            raise ValueError("invalid operation charge")
        self.ops += count
        if self.ops > self.limit:
            raise ResourceLimit("operation limit exceeded")


def _integer(value, name, minimum=None):
    if type(value) is not int:
        raise AdmissionError(name + " must be an integer (not bool)")
    if minimum is not None and value < minimum:
        raise AdmissionError(name + " below its minimum")
    if value.bit_length() > MAX_BITS:
        raise ResourceLimit(name + " exceeds the integer bit limit")
    return value


def _rational(value, name, meter):
    if type(value) is not str or len(value) > 2500 or not _RATIONAL.fullmatch(value):
        raise AdmissionError(name + " must be a canonical rational string")
    parts = value.split("/")
    numerator = int(parts[0])
    denominator = int(parts[1]) if len(parts) == 2 else 1
    if max(numerator.bit_length(), denominator.bit_length()) > INPUT_BITS:
        raise ResourceLimit(name + " exceeds the rational input bit limit")
    meter.charge(1)
    result = Fraction(numerator, denominator)
    if str(result) != value:
        raise AdmissionError(name + " is not canonical")
    return result


def _bounded(value, meter):
    meter.charge()
    if max(value.numerator.bit_length(), value.denominator.bit_length()) > MAX_BITS:
        raise ResourceLimit("rational intermediate exceeds 100000 bits")
    return value


def _int_mul(left, right, meter):
    meter.charge(2)
    if right and left and left.bit_length() + right.bit_length() > MAX_BITS and abs(left) > MAX_INTEGER // abs(right):
        raise ResourceLimit("integer product exceeds 100000 bits")
    return left * right


def _int_add(left, right, meter):
    meter.charge(2)
    if max(left.bit_length(), right.bit_length()) < MAX_BITS:
        return left + right
    if left >= 0 and right >= 0 and left > MAX_INTEGER - right:
        raise ResourceLimit("integer sum exceeds 100000 bits")
    if left <= 0 and right <= 0 and -left > MAX_INTEGER + right:
        raise ResourceLimit("integer sum exceeds 100000 bits")
    return left + right


def _mul(left, right, meter):
    # Guard unreduced products too: reduction does not license oversize work.
    numerator = _int_mul(left.numerator, right.numerator, meter)
    denominator = _int_mul(left.denominator, right.denominator, meter)
    return _bounded(Fraction(numerator, denominator), meter)


def _add(left, right, meter):
    common = gcd(left.denominator, right.denominator)
    a = right.denominator // common
    b = left.denominator // common
    numerator = _int_add(_int_mul(left.numerator, a, meter),
                         _int_mul(right.numerator, b, meter), meter)
    denominator = _int_mul(left.denominator, a, meter)
    return _bounded(Fraction(numerator, denominator), meter)


def _divide(left, right, meter):
    if right == 0:
        raise AdmissionError("division by zero")
    return _mul(left, Fraction(right.denominator, right.numerator), meter)


def _power_target(k, a, b, precision, meter):
    # A safe upper bound is checked before exponentiation or allocating shifts.
    shift = precision * b
    estimate = k.bit_length() * a + shift
    meter.charge(3)
    if shift >= MAX_BITS:
        raise ResourceLimit("power enclosure exceeds the 100000-bit budget")
    if k == 1:
        return 1 << shift
    if (k.bit_length() - 1) * a + shift >= MAX_BITS:
        raise ResourceLimit("power enclosure exceeds the 100000-bit budget")
    if estimate <= MAX_BITS:
        meter.charge(max(1, a.bit_length()))
        power = pow(k, a)
    else:
        # Borderline estimates use capped repeated squaring, accepting every
        # actual power within the limit without allocating an oversize value.
        cap = (1 << (MAX_BITS - shift)) - 1
        power, factor, remaining = 1, k, a
        while remaining:
            if remaining & 1:
                meter.charge(2)
                if factor is None or power > cap // factor:
                    raise ResourceLimit("power enclosure exceeds the 100000-bit budget")
                power *= factor
            remaining >>= 1
            if remaining:
                meter.charge(2)
                factor = None if factor is None or factor > cap // factor else factor * factor
    target = power << shift
    if target.bit_length() > MAX_BITS:
        raise ResourceLimit("power enclosure exceeds the 100000-bit budget")
    return target


def _power_compare(base, exponent, target, meter):
    """Compare base**exponent to target without ever forming an oversize power."""
    value = 1
    factor = base
    remaining = exponent
    while remaining:
        meter.charge(2)
        if remaining & 1:
            if factor is None or value > target // factor:
                return 1
            value *= factor
            meter.charge(2)
        remaining >>= 1
        if remaining:
            if factor is None or factor > target // factor:
                factor = None
            else:
                factor *= factor
            meter.charge(2)
    return (value > target) - (value < target)


def _integer_root(target, exponent, meter):
    if target < 2 or exponent == 1:
        meter.charge()
        return target
    if exponent == 2:
        meter.charge(target.bit_length())
        return isqrt(target)
    low = 0
    high = 1 << ((target.bit_length() + exponent - 1) // exponent)
    while high - low > 1:
        mid = (low + high) // 2
        meter.charge(2)
        if _power_compare(mid, exponent, target, meter) <= 0:
            low = mid
        else:
            high = mid
    return low


def power_enclosure(k, q, precision, meter=None):
    """Exact rational endpoints of k**q; exported for independent synthetic tests."""
    meter = meter if meter is not None else Meter()
    _integer(k, "power k", 1)
    _integer(precision, "precision", 0)
    if not isinstance(q, Fraction) or q <= 0:
        raise AdmissionError("power exponent must be a positive Fraction")
    if q.denominator == 1:
        target = _power_target(k, q.numerator, 1, 0, meter)
        result = Fraction(target)
        return result, result
    target = _power_target(k, q.numerator, q.denominator, precision, meter)
    root = _integer_root(target, q.denominator, meter)
    exact = _power_compare(root, q.denominator, target, meter) == 0
    grid = 1 << precision
    return Fraction(root, grid), Fraction(root if exact else root + 1, grid)


def _parse_spec(spec, meter):
    if type(spec) is not dict or set(spec) != {"profile", "theta"}:
        raise AdmissionError("spec must contain exactly profile and theta")
    profile = spec["profile"]
    theta = spec["theta"]
    if type(profile) is not list or not 1 <= len(profile) <= 16:
        raise AdmissionError("profile must have 1..16 bands")
    if type(theta) is not list:
        raise AdmissionError("theta must be a list")
    if len(theta) > 4096:
        raise ResourceLimit("too many smooth coordinates")
    bands = []
    previous = Fraction(0)
    denominator = 1
    for index, band in enumerate(profile):
        if type(band) is not list or len(band) != 3:
            raise AdmissionError("profile band must have three rational strings")
        lo, hi, weight = [_rational(x, "profile", meter) for x in band]
        if not 0 <= lo < hi <= 100 or (index and lo < previous) or weight == 0:
            raise AdmissionError("profile bands must be increasing, disjoint, nonzero, in [0,100]")
        previous = hi
        denominator = _int_mul(denominator // gcd(denominator, weight.denominator), weight.denominator, meter)
        if denominator.bit_length() > MAX_BITS:
            raise ResourceLimit("source denominator exceeds 100000 bits")
        bands.append((lo, hi, weight))
    exponents = [_rational(x, "theta", meter) for x in theta]
    if any(not 0 < x < 1 for x in exponents) or any(a >= b for a, b in zip(exponents, exponents[1:])):
        raise AdmissionError("theta must be strictly increasing in (0,1)")
    labels = _BASE_LABELS + ["smooth:" + x for x in theta]
    scaled = [(lo, hi, _int_mul(weight.numerator, denominator // weight.denominator, meter))
              for lo, hi, weight in bands]
    return scaled, exponents, denominator, labels


def _floor_scaled(value, k, meter):
    product = _int_mul(value.numerator, k, meter)
    return product // value.denominator


def _data_structure(data, meter, check_cuts=True):
    required = {"schema", "spec", "labels", "denominator", "rows", "operations"}
    if type(data) is not dict or set(data) != required:
        raise AdmissionError("dataset keys do not match schema")
    if data["schema"] != "signed-prime-storage-data-v1":
        raise AdmissionError("wrong dataset schema")
    bands, theta, denominator, labels = _parse_spec(data["spec"], meter)
    if data["labels"] != labels:
        raise AdmissionError("state labels or their order are incorrect")
    if _integer(data["denominator"], "denominator", 1) != denominator:
        raise AdmissionError("source denominator is not the profile lcm")
    _integer(data["operations"], "producer operations", 0)
    rows = data["rows"]
    if type(rows) is not list or not rows:
        raise AdmissionError("dataset rows must be a nonempty list")
    rough_bytes = len(rows) * (256 + len(labels) * (48 + (denominator.bit_length() + 7)//8))
    if rough_bytes > MEMORY_BUDGET:
        raise ResourceLimit("dataset exceeds checker allocation budget")
    mapping = {}
    endpoints = []
    cut_cache = {}
    previous = 0
    for row in rows:
        if type(row) is not dict or set(row) != {"k", "X", "cuts", "state"}:
            raise AdmissionError("row keys do not match schema")
        k = _integer(row["k"], "row k", 1)
        if k <= previous:
            raise AdmissionError("rows must have strictly increasing distinct k")
        previous = k
        X = _integer(row["X"], "row X", 1)
        intervals = [(_floor_scaled(lo, k, meter), _floor_scaled(hi, k, meter), weight)
                     for lo, hi, weight in bands]
        if X != intervals[-1][1]:
            raise AdmissionError("row X does not equal floor(max_hi*k)")
        cuts = row["cuts"]
        if type(cuts) is not list or len(cuts) != len(theta):
            raise AdmissionError("incorrect smooth cutoff count")
        for cut in cuts:
            _integer(cut, "smooth cutoff", 1)
            if cut > X:
                raise AdmissionError("smooth cutoff exceeds X")
        if check_cuts:
            if X not in cut_cache:
                cut_cache[X] = [_integer_root(_power_target(X, t.numerator, t.denominator, 0, meter),
                                              t.denominator, meter) for t in theta]
            if cuts != cut_cache[X]:
                raise AdmissionError("smooth cutoffs fail exact integer-power comparison")
        state = row["state"]
        if type(state) is not list or len(state) != len(labels):
            raise AdmissionError("incorrect state dimension")
        for value in state:
            _integer(value, "state coordinate")
        sector_sum = 0
        for value in state[1:6]:
            sector_sum = _int_add(sector_sum, value, meter)
        if sector_sum != state[0]:
            raise AdmissionError("signed factor-count sectors do not sum to Z")
        meter.charge(len(state) + 5)
        mapping[k] = row
        endpoints.append(intervals)
    return bands, theta, denominator, labels, mapping, endpoints, rough_bytes


def _source_values(data, structure, meter):
    bands, theta, denominator, labels, mapping, endpoints, rough_bytes = structure
    rows = data["rows"]
    max_x = rows[-1]["X"]
    query_count = sum(2 * len(intervals) * len(theta) for intervals in endpoints)
    # Arrays, squarefree sorted events, expected states, tuples, sorting scratch.
    estimate = rough_bytes + (max_x + 1) * 160 + query_count * 160
    if estimate > MEMORY_BUDGET or max_x > 2**31 - 1:
        raise ResourceLimit("source sieve/query allocation exceeds checker memory budget")
    omega = bytearray(max_x + 1)
    pplus = array("I", [0]) * (max_x + 1)
    mu = array("b", [1]) * (max_x + 1)
    mu[0] = 0
    pplus[1] = 1
    # Every prime is recognized by the absence of previous prime factors.
    # Squareful numbers are explicitly zeroed and retain that zero thereafter.
    for p in range(2, max_x + 1):
        meter.charge()
        if omega[p] == 0:
            for n in range(p, max_x + 1, p):
                omega[n] += 1
                pplus[n] = p
                mu[n] = -mu[n]
                meter.charge(3)
            square = p * p
            if square <= max_x:
                for n in range(square, max_x + 1, square):
                    mu[n] = 0
                    meter.charge()
    prefixes = [array("q", [0]) * (max_x + 1) for _ in range(5)]
    totals = [0] * 5
    events = []
    for n in range(1, max_x + 1):
        if mu[n]:
            category = min(omega[n], 4)
            totals[category] += mu[n]
            if theta:
                events.append((pplus[n], n, mu[n]))
        for category in range(5):
            prefixes[category][n] = totals[category]
        meter.charge(7)
    expected = [[0] * len(labels) for _ in rows]
    queries = []
    for row_index, (row, intervals) in enumerate(zip(rows, endpoints)):
        target = expected[row_index]
        for lo, hi, weight in intervals:
            for category in range(5):
                target[category + 1] = _int_add(target[category + 1],
                    _int_mul(weight, prefixes[category][hi] - prefixes[category][lo], meter), meter)
            for j, cut in enumerate(row["cuts"]):
                if hi:
                    queries.append((cut, hi, row_index, j + 6, weight))
                if lo:
                    queries.append((cut, lo, row_index, j + 6, -weight))
        for value in target[1:6]:
            target[0] = _int_add(target[0], value, meter)
        if any(abs(value).bit_length() > MAX_BITS for value in target):
            raise ResourceLimit("source sum exceeds integer bit limit")
    del prefixes, omega, pplus
    events.sort()
    queries.sort()
    meter.charge(len(events) * max(1, len(events).bit_length()) +
                 len(queries) * max(1, len(queries).bit_length()))
    tree = array("q", [0]) * (max_x + 1)
    cursor = 0
    for cutoff, endpoint, row_index, coordinate, weight in queries:
        while cursor < len(events) and events[cursor][0] <= cutoff:
            _, n, sign = events[cursor]
            while n <= max_x:
                tree[n] += sign
                n += n & -n
                meter.charge(3)
            cursor += 1
        value = 0
        n = endpoint
        while n:
            value += tree[n]
            n -= n & -n
            meter.charge(3)
        expected[row_index][coordinate] = _int_add(expected[row_index][coordinate],
                                                 _int_mul(weight, value, meter), meter)
    for row, actual in zip(rows, expected):
        if any(abs(value).bit_length() > MAX_BITS for value in actual):
            raise ResourceLimit("smooth source sum exceeds integer bit limit")
        if row["state"] != actual:
            mismatch = next(i for i, (a, b) in enumerate(zip(row["state"], actual)) if a != b)
            raise AdmissionError("source mismatch at k=%s label=%s: supplied=%s expected=%s" %
                                 (row["k"], labels[mismatch], row["state"][mismatch], actual[mismatch]))
        meter.charge(len(actual))
    return max_x, estimate


def _failure(error, meter, start, **extra):
    return {"verified": False, "error": str(error),
            "error_type": type(error).__name__, "operations": meter.ops - start, **extra}


def verify_data(data, meter=None):
    meter = meter if meter is not None else Meter()
    start = meter.ops
    try:
        structure = _data_structure(data, meter)
        max_x, estimate = _source_values(data, structure, meter)
        return {"verified": True, "operations": meter.ops - start,
                "rows": len(data["rows"]), "max_X": max_x,
                "estimated_peak_bytes": estimate,
                "source_semantics": "actual_signed_mobius_profile_factor_sectors_and_smooth_cutoffs"}
    except (AdmissionError, OverflowError, MemoryError) as error:
        return _failure(error, meter, start)


def _parse_candidate(candidate, data, meter):
    required = {"schema", "spec", "labels", "q", "precision", "rays", "C", "base_upper",
                "training_scales", "training_upper", "search_metadata", *_FLAGS}
    if type(candidate) is not dict or set(candidate) != required:
        raise AdmissionError("candidate keys do not match schema")
    if candidate["schema"] != "signed-prime-storage-candidate-v1":
        raise AdmissionError("wrong candidate schema")
    if candidate["spec"] != data["spec"] or candidate["labels"] != data["labels"]:
        raise AdmissionError("candidate/source spec or labels mismatch")
    for flag, expected in _FLAGS.items():
        if candidate[flag] is not expected:
            raise AdmissionError("invalid proof scope flag: " + flag)
    q = _rational(candidate["q"], "q", meter)
    if not 1 <= q <= 2:
        raise AdmissionError("q must lie in [1,2]")
    precision = _integer(candidate["precision"], "precision", 8)
    if precision > 24:
        raise AdmissionError("precision must lie in 8..24")
    rays = candidate["rays"]
    if type(rays) is not list or len(rays) > 256:
        raise AdmissionError("candidate must have at most 256 rays")
    parsed_rays = []
    dimension = len(data["labels"])
    for ray in rays:
        if type(ray) is not dict or set(ray) != {"weight", "direction"}:
            raise AdmissionError("ray keys do not match schema")
        weight = _rational(ray["weight"], "ray weight", meter)
        if weight <= 0:
            raise AdmissionError("ray weights must be positive; omit zero-weight rays")
        direction = ray["direction"]
        if type(direction) is not list or len(direction) != dimension:
            raise AdmissionError("incorrect ray direction dimension")
        parsed_rays.append((weight, [_rational(x, "ray direction", meter) for x in direction]))
    C = _rational(candidate["C"], "C", meter)
    base = _rational(candidate["base_upper"], "base_upper", meter)
    training_upper = _rational(candidate["training_upper"], "training_upper", meter)
    if min(C, base, training_upper) < 0:
        raise AdmissionError("C/base/training upper must be nonnegative")
    if training_upper > C:
        raise AdmissionError("declared training_upper exceeds C")
    training_scales = candidate["training_scales"]
    _scales(training_scales)
    if type(candidate["search_metadata"]) is not dict:
        raise AdmissionError("search_metadata must be a dict; it is not theorem evidence")
    return q, precision, parsed_rays, C, base, training_upper, training_scales


def _scales(scales):
    if type(scales) is not list:
        raise AdmissionError("scales must be a sorted unique integer list")
    previous = 1
    for k in scales:
        _integer(k, "scale", 2)
        if k <= previous:
            raise AdmissionError("scales must be sorted and unique")
        previous = k


def _require_rows(mapping, scales):
    if 1 not in mapping:
        raise AdmissionError("actual base k=1 is required")
    for k in scales:
        if k not in mapping or k // 2 not in mapping:
            raise AdmissionError("missing child or floor(k/2) parent for k=%s" % k)


def _energy(row, denominator, rays, meter):
    state = [Fraction(value, denominator) for value in row["state"]]
    result = _mul(state[0], state[0], meter)
    for weight, direction in rays:
        dot = Fraction(0)
        for coefficient, value in zip(direction, state):
            if coefficient and value:
                dot = _add(dot, _mul(coefficient, value, meter), meter)
        result = _add(result, _mul(weight, _mul(dot, dot, meter), meter), meter)
    return result


def _drifts(mapping, scales, denominator, q, precision, rays, meter):
    cache = {}
    def normalized(k):
        if k not in cache:
            energy = _energy(mapping[k], denominator, rays, meter)
            lower_power, upper_power = power_enclosure(k, q, precision, meter)
            if lower_power <= 0:
                raise AdmissionError("normalization lower endpoint must be positive")
            cache[k] = (_divide(energy, upper_power, meter),
                        _divide(energy, lower_power, meter))
        return cache[k]
    for k in scales:
        lower, upper = normalized(k)
        parent_lower, parent_upper = normalized(k // 2)
        yield k, _add(lower, -parent_upper, meter), _add(upper, -parent_lower, meter)


def verify_candidate(candidate, training_data, meter=None):
    meter = meter if meter is not None else Meter()
    start = meter.ops
    try:
        structure = _data_structure(training_data, meter)
        _, _, denominator, _, mapping, _, _ = structure
        q, precision, rays, C, base, declared_upper, scales = _parse_candidate(candidate, training_data, meter)
        _require_rows(mapping, scales)
        actual_base = _energy(mapping[1], denominator, rays, meter)
        if actual_base != base:
            raise AdmissionError("base_upper must equal the actual exact E(1)")
        actual_upper = Fraction(0)
        bounds = []
        for k, lower, upper in _drifts(mapping, scales, denominator, q, precision, rays, meter):
            actual_upper = max(actual_upper, upper)
            bounds.append({"k": k, "parent": k // 2, "lower": str(lower), "upper": str(upper)})
        if actual_upper != declared_upper:
            raise AdmissionError("training_upper must be the exact maximum of zero and every training upper enclosure")
        if actual_upper > C:
            raise AdmissionError("a training upper drift enclosure exceeds C")
        return {"verified": True, "operations": meter.ops - start,
                **_FLAGS, "base_upper": str(actual_base), "training_upper": str(actual_upper),
                "training_bounds": bounds, "training_scales_checked": len(scales),
                "source_admission_required_separately": True,
                "domination_reason": "Z^2 plus a finite sum of nonnegative rational weighted squares",
                "open_assertion": "F(k)-F(floor(k/2))<=C for every integer k>=2"}
    except (AdmissionError, OverflowError, MemoryError) as error:
        return _failure(error, meter, start, uniform_domination_proved=False,
                        uniform_recurrence_proved=False, uniform_head_bound_proved=False, RH_proved=False)


def evaluate_candidate(candidate, evaluation_data, meter=None, scales=None):
    meter = meter if meter is not None else Meter()
    start = meter.ops
    try:
        structure = _data_structure(evaluation_data, meter)
        _, _, denominator, _, mapping, _, _ = structure
        q, precision, rays, C, base, _, _ = _parse_candidate(candidate, evaluation_data, meter)
        selected = [k for k in mapping if k >= 2] if scales is None else scales
        _scales(selected)
        _require_rows(mapping, selected)
        if _energy(mapping[1], denominator, rays, meter) != base:
            raise AdmissionError("evaluation base does not equal candidate E(1)")
        witnesses = []
        inconclusive = []
        worst_lower = None
        worst_upper = None
        for k, lower, upper in _drifts(mapping, selected, denominator, q, precision, rays, meter):
            record = {"k": k, "parent": k // 2, "lower": str(lower), "upper": str(upper), "C": str(C)}
            if worst_lower is None or lower > worst_lower[0]:
                worst_lower = (lower, record)
            if worst_upper is None or upper > worst_upper[0]:
                worst_upper = (upper, record)
            if lower > C:
                witnesses.append(record)
            elif upper > C:
                inconclusive.append(record)
        status = ("REFUTED" if witnesses else "UNRESOLVED_ROUNDING" if inconclusive
                  else "VERIFIED_ON_FINITE_DOMAIN")
        return {"verified": status == "VERIFIED_ON_FINITE_DOMAIN", "status": status,
                "operations": meter.ops - start, "scales_checked": len(selected),
                "evaluated_scales": selected,
                "violating_scales": [x["k"] for x in witnesses],
                "inconclusive_scales": [x["k"] for x in inconclusive],
                "witnesses": witnesses, "inconclusive": inconclusive,
                "worst_lower": str(worst_lower[0]) if worst_lower else None,
                "worst_upper": str(worst_upper[0]) if worst_upper else None,
                "worst_lower_witness": worst_lower[1] if worst_lower else None,
                "worst_upper_witness": worst_upper[1] if worst_upper else None,
                **_FLAGS, "finite_only": True,
                "source_admission_required_separately": True,
                "open_assertion": "F(k)-F(floor(k/2))<=C for every integer k>=2"}
    except (AdmissionError, OverflowError, MemoryError) as error:
        return _failure(error, meter, start, status="INVALID", uniform_domination_proved=False,
                        uniform_recurrence_proved=False, uniform_head_bound_proved=False, RH_proved=False)
