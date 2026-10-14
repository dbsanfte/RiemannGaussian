"""Independent exact verification of the uniform exchange packing law (072).

No optimization and no scale-dependent Mobius data enter verification.
Only evaluate_law constructs ordinary Mobius values.
"""
from fractions import Fraction
from itertools import combinations
from math import gcd, isqrt
from time import monotonic

GRID = 1 << 20
MAX_FAMILIES = 20000
MAX_ROWS = 200000
MAX_BITS = 4096
CERTIFICATE_FIELDS = frozenset({
    "schema", "profile", "cap", "primes", "candidates", "capacity_rows",
    "lambda_denominator", "lambda_numerators", "dual_denominator", "dual_numerators",
    "objective_gain", "objective_upper", "leading_upper", "leading_lower", "sqrt_error_upper",
    "selected_family_indices", "solver", "uniform_profile_bound_proved",
    "sublinear_profile_bound_proved", "uniform_head_bound_proved", "RH_proved",
})


class Meter:
    def __init__(self, limit=300_000_000_000, seconds=7200):
        self.limit = limit
        self.seconds = seconds
        self.ops = 0
        self.started = monotonic()

    @property
    def elapsed_seconds(self):
        return monotonic() - self.started

    def tick(self, count=1):
        self.ops += count
        if self.ops > self.limit:
            raise RuntimeError("checker work limit exceeded")
        if self.elapsed_seconds > self.seconds:
            raise RuntimeError("checker elapsed-time limit exceeded")


def _require(condition, message):
    if not condition:
        raise ValueError(message)


def _integer(value, name, minimum=0):
    _require(type(value) is int and value >= minimum, name + " must be an integer in range")
    _require(value.bit_length() <= MAX_BITS, name + " exceeds integer bit cap")
    return value


def _rational(value, name):
    _require(type(value) is str and len(value) <= 2500, name + " must be a bounded canonical rational string")
    try:
        result = Fraction(value)
    except (ValueError, ZeroDivisionError):
        raise ValueError(name + " is not rational") from None
    _require(str(result) == value, name + " is not canonical")
    _require(max(abs(result.numerator).bit_length(), result.denominator.bit_length()) <= MAX_BITS,
             name + " exceeds rational bit cap")
    return result


def _profile(raw, meter):
    _require(type(raw) is list, "profile must be a list")
    # A declared prospective 2 GiB checker budget requires an explicit input cap.
    _require(1 <= len(raw) <= 16, "profile must have 1..16 bands (prospective resource cap)")
    profile = []
    previous_hi = Fraction(0)
    for i, band in enumerate(raw):
        meter.tick()
        _require(type(band) is dict and set(band) == {"lo", "hi", "value"}, "invalid profile band")
        lo, hi, value = (_rational(band[key], "profile." + key) for key in ("lo", "hi", "value"))
        _require(0 <= lo < hi <= 100 and value != 0, "invalid profile interval/value")
        _require(i == 0 or previous_hi <= lo, "profile must be sorted and disjoint")
        profile.append((lo, hi, value))
        previous_hi = hi
    return profile


def _factor_set(n, meter):
    factors = set()
    p = 2
    while p * p <= n:
        meter.tick()
        if n % p == 0:
            n //= p
            factors.add(p)
            if n % p == 0:
                return None
        p += 1
    if n > 1:
        factors.add(n)
    return frozenset(factors)


def _rebuild(profile, cap, meter):
    """Use prime factor sets, not the producer's divisibility bit masks."""
    factors = {n: _factor_set(n, meter) for n in range(1, cap + 1)}
    primes = [n for n in range(2, cap + 1) if factors[n] == frozenset({n})]
    families, internal = [], []
    for a in range(1, cap + 1):
        if factors[a] is None:
            continue
        for b in range(a + 1, cap + 1):
            if factors[b] is None or factors[a] & factors[b]:
                continue
            union = factors[a] | factors[b]
            density = Fraction(1)
            for p in sorted(union):
                density *= Fraction(p, p + 1)
            sign_a, sign_b = (-1) ** len(factors[a]), (-1) ** len(factors[b])
            for left_lo, left_hi, left_value in profile:
                for right_lo, right_hi, right_value in profile:
                    meter.tick()
                    lo, hi = max(left_lo / a, right_lo / b), min(left_hi / a, right_hi / b)
                    gain = abs(left_value) + abs(right_value) - abs(sign_a * left_value + sign_b * right_value)
                    if lo < hi and gain > 0:
                        _require(len(families) < MAX_FAMILIES, "candidate family resource cap exceeded")
                        families.append(dict(a=a, b=b, lo=str(lo), hi=str(hi),
                                             left_value=str(left_value), right_value=str(right_value),
                                             gain=str(gain), density_ratio=str(density)))
                        internal.append((a, b, lo, hi, gain, density, factors[a], factors[b], union))
    subsets = [frozenset(items) for size in range(len(primes) + 1)
               for items in combinations(primes, size)]
    # Exact endpoint sweep maintains precisely the midpoint incidences. At each
    # left endpoint, end events are removed and start events inserted, so the
    # open-left, closed-right cell has exactly the interior pattern.
    events = {}
    for i, (a, b, lo, hi, gain, density, fa, fb, union) in enumerate(internal):
        for multiplier, required in ((a, fa), (b, fb)):
            compatible = [j for j, subset in enumerate(subsets) if subset & union == required]
            meter.tick(len(subsets))
            events.setdefault(multiplier * lo, []).append((True, i, compatible))
            events.setdefault(multiplier * hi, []).append((False, i, compatible))
    endpoints = sorted(events)
    active = [set() for _ in subsets]
    rows = set()
    row_entries = 0
    for left in endpoints[:-1]:
        for adding, i, compatible in sorted(events[left], key=lambda event: event[0]):
            for j in compatible:
                meter.tick()
                if adding:
                    active[j].add(i)
                else:
                    active[j].discard(i)
        for incidence in active:
            meter.tick(1 + len(incidence))
            if incidence:
                pattern = tuple(sorted(incidence))
                if pattern not in rows:
                    row_entries += len(pattern)
                    _require(row_entries <= 8_000_000, "capacity incidence 2 GiB resource cap exceeded")
                    rows.add(pattern)
                _require(len(rows) <= MAX_ROWS, "capacity row resource cap exceeded")
    return primes, families, internal, [list(row) for row in sorted(rows)]


def _root_upper(x, meter):
    meter.tick()
    _require(x >= 0, "negative root argument")
    scaled_numerator = x.numerator * GRID * GRID
    root = isqrt(scaled_numerator // x.denominator)
    if root * root * x.denominator < scaled_numerator:
        root += 1
    _require(root * root * x.denominator >= scaled_numerator and
             (root == 0 or (root - 1) ** 2 * x.denominator < scaled_numerator), "root certification failed")
    return Fraction(root, GRID)


def _verify(cert, meter):
    meter.tick()
    _require(type(cert) is dict and cert.get("schema") == "mobius-uniform-exchange-law-v1", "invalid certificate schema")
    _require(set(cert) == CERTIFICATE_FIELDS, "certificate fields mismatch")
    supplied_candidates = cert.get("candidates")
    supplied_rows = cert.get("capacity_rows")
    _require(type(supplied_candidates) is list and len(supplied_candidates) <= MAX_FAMILIES, "invalid candidates")
    _require(type(supplied_rows) is list and len(supplied_rows) <= MAX_ROWS, "invalid capacity rows")
    _require(all(type(row) is list for row in supplied_rows), "invalid capacity rows")
    _require(sum(len(row) for row in supplied_rows) <= 8_000_000,
             "input capacity incidence 2 GiB resource cap exceeded")
    profile = _profile(cert.get("profile"), meter)
    cap = _integer(cert.get("cap"), "cap", 2)
    _require(cap <= 23, "cap exceeds dictionary scope")
    primes, candidates, internal, rows = _rebuild(profile, cap, meter)
    supplied_primes = cert.get("primes")
    _require(type(supplied_primes) is list and all(type(p) is int for p in supplied_primes) and supplied_primes == primes,
             "prime scope mismatch")
    for candidate in supplied_candidates:
        _require(type(candidate) is dict and type(candidate.get("a")) is int and type(candidate.get("b")) is int,
                 "invalid candidate multiplier")
        for field in ("lo", "hi", "left_value", "right_value", "gain", "density_ratio"):
            _rational(candidate.get(field), "candidate." + field)
    _require(supplied_candidates == candidates, "complete candidate reconstruction mismatch")
    _require(all(type(row) is list and all(type(i) is int for i in row) for row in supplied_rows), "invalid capacity row indices")
    _require(supplied_rows == rows, "complete capacity reconstruction mismatch")
    denominator = _integer(cert.get("lambda_denominator"), "lambda denominator", GRID)
    dual_denominator = _integer(cert.get("dual_denominator"), "dual denominator", 1)
    _require(dual_denominator == GRID, "dual denominator must equal fixed grid")
    numerators, dual_numerators = cert.get("lambda_numerators"), cert.get("dual_numerators")
    _require(type(numerators) is list and len(numerators) == len(candidates), "primal vector length mismatch")
    _require(type(dual_numerators) is list and len(dual_numerators) == len(rows), "dual vector length mismatch")
    for n in numerators:
        _integer(n, "primal numerator")
        _require(n <= denominator, "primal bound lambda<=1 violated")
    for n in dual_numerators:
        _integer(n, "dual numerator")
    for row in rows:
        meter.tick(len(row))
        _require(sum(numerators[i] for i in row) <= denominator, "primal capacity violated")
    weights = [Fraction(n, denominator) for n in numerators]
    rewards = [gain * density * (hi - lo) for a, b, lo, hi, gain, density, fa, fb, union in internal]
    gain = sum((weight * reward for weight, reward in zip(weights, rewards)), Fraction(0))
    cover = [0] * len(candidates)
    for row, y in zip(rows, dual_numerators):
        meter.tick(len(row))
        for i in row:
            cover[i] += y
    upper = Fraction(sum(dual_numerators), GRID) + sum(
        (max(reward - Fraction(c, GRID), Fraction(0)) for reward, c in zip(rewards, cover)), Fraction(0))
    baseline = sum((abs(value) * (hi - lo) for lo, hi, value in profile), Fraction(0))
    leading_upper, leading_lower = baseline - gain, baseline - upper
    _require(leading_upper >= 0, "negative leading upper violates uniform mass density")
    _require(upper >= gain, "dual upper below feasible objective")
    error = sum((3 * abs(value) * (_root_upper(hi, meter) + _root_upper(lo, meter))
                 for lo, hi, value in profile), Fraction(0))
    error += sum((weight * family[4] * ((1 << len(family[8])) + 2) *
                  (_root_upper(family[3], meter) + _root_upper(family[2], meter))
                  for weight, family in zip(weights, internal)), Fraction(0))
    for name, expected in (("objective_gain", gain), ("objective_upper", upper),
                           ("leading_upper", leading_upper), ("leading_lower", leading_lower),
                           ("sqrt_error_upper", error)):
        _require(_rational(cert.get(name), name) == expected, name + " mismatch")
    selected = cert.get("selected_family_indices")
    _require(type(selected) is list and all(type(i) is int for i in selected) and
             selected == [i for i, n in enumerate(numerators) if n > 0], "selected family mismatch")
    _require(type(cert.get("solver")) is dict, "solver metadata must be a dictionary")
    flags = dict(uniform_profile_bound_proved=True, sublinear_profile_bound_proved=leading_upper == 0,
                 uniform_head_bound_proved=False, RH_proved=False)
    for key, value in flags.items():
        _require(cert.get(key) is value, key + " scope mismatch")
    result = dict(verified=True, leading_upper=str(leading_upper), leading_lower=str(leading_lower),
                  sqrt_error_upper=str(error), family_count=len(candidates), capacity_row_count=len(rows),
                  work_ops=meter.ops, **flags)
    return result, profile, internal, weights


def verify_law(cert, meter=None):
    """Check the exact, all-scales theorem certificate or raise ValueError."""
    return _verify(cert, meter if meter is not None else Meter())[0]


def _ordinary_mu(bound, meter):
    # Elementary divisor sieve, independent of any producer arithmetic routine.
    mu = [1] * (bound + 1)
    mu[0] = 0
    composite = bytearray(bound + 1)
    for p in range(2, bound + 1):
        meter.tick()
        if not composite[p]:
            for n in range(p, bound + 1, p):
                meter.tick()
                mu[n] = -mu[n]
                if n > p:
                    composite[n] = 1
            square = p * p
            for n in range(square, bound + 1, square):
                meter.tick()
                mu[n] = 0
    return mu


def evaluate_law(cert, k, meter=None):
    """Verify, then check the full finite packing price using actual ordinary mu."""
    meter = meter if meter is not None else Meter()
    verified, profile, internal, weights = _verify(cert, meter)
    _integer(k, "scale k", 1)
    bound = int(k * max((hi for lo, hi, value in profile), default=Fraction(0)))
    # Conservative explicit prospective memory limit, never a truncation.
    _require(bound <= 50_000_000, "finite evaluator 2 GiB resource cap exceeded")
    mu = _ordinary_mu(bound, meter)
    signed, baseline = Fraction(0), Fraction(0)
    for lo, hi, value in profile:
        for n in range(int(k * lo) + 1, int(k * hi) + 1):
            meter.tick()
            signed += mu[n] * value
            baseline += mu[n] * mu[n] * abs(value)
    counts = []
    for a, b, lo, hi, gain, density, fa, fb, union in internal:
        count = 0
        for m in range(int(k * lo) + 1, int(k * hi) + 1):
            meter.tick()
            if mu[m] != 0 and gcd(m, a * b) == 1:
                count += 1
        counts.append(count)
    finite = baseline - sum((weight * family[4] * count for weight, family, count in
                             zip(weights, internal, counts)), Fraction(0))
    _require(abs(signed) <= finite, "actual target exceeds complete finite price")
    return dict(k=k, actual_signed_target=str(signed), baseline_squarefree_price=str(baseline),
                certified_finite_price=str(finite), actual_absolute_target=str(abs(signed)),
                family_counts=counts, verified=True, uniform_head_bound_proved=False, RH_proved=False,
                work_ops=meter.ops)
