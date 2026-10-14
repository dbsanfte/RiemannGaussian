"""Independent necessary grammar admission; this module evaluates no source.

The source-specific theta=1/2 boundary belongs to the registered bulk
family.  Unknown theta<1/2 mixtures remain open in the open_mixed branch.
Ordinary source, domination, and finite recurrence admission remain with
the frozen independent073 checker.
"""
from fractions import Fraction
from math import gcd
import re
import sys


_PROFILE = [["8", "10", "1"], ["16", "20", "-1"]]
_BASE_LABELS = ["Z", "unit", "omega1", "omega2", "omega3", "omega_ge4"]
_RATIONAL = re.compile(r"(?:0|-?[1-9][0-9]*)(?:/[1-9][0-9]*)?\Z")
_KEYS = {"schema", "spec", "labels", "q", "precision", "rays", "C", "base_upper",
         "training_scales", "training_upper", "search_metadata",
         "uniform_domination_proved", "uniform_recurrence_proved",
         "uniform_head_bound_proved", "RH_proved"}
_FALSE_SCOPE = {"uniform_recurrence_proved": False,
                "uniform_head_bound_proved": False, "RH_proved": False}
_MAX_BITS = 100000
_INPUT_BITS = 4096
if hasattr(sys, "set_int_max_str_digits") and 0 < sys.get_int_max_str_digits() < 31000:
    sys.set_int_max_str_digits(31000)


class GrammarError(ValueError):
    pass


class ResourceLimit(GrammarError):
    pass


class _Counter:
    def __init__(self):
        self.ops = 0

    def charge(self, amount=1):
        self.ops += amount
        if self.ops > 5000000:
            raise ResourceLimit("grammar operation limit exceeded")


def _rational(value, field, counter):
    if type(value) is not str or len(value) > 2500 or not _RATIONAL.fullmatch(value):
        raise GrammarError(field + " must be a canonical rational string")
    pieces = value.split("/")
    numerator = int(pieces[0])
    denominator = int(pieces[1]) if len(pieces) == 2 else 1
    if max(numerator.bit_length(), denominator.bit_length()) > _INPUT_BITS:
        raise ResourceLimit(field + " exceeds the4096-bit input limit")
    counter.charge()
    parsed = Fraction(numerator, denominator)
    if str(parsed) != value:
        raise GrammarError(field + " is not canonical")
    return parsed


def _sum_rationals(values, counter):
    """Guard the exact grammar sum; no source/energy arithmetic is performed."""
    result = Fraction(0)
    for value in values:
        common = gcd(result.denominator, value.denominator)
        left_scale = value.denominator // common
        right_scale = result.denominator // common
        for a, b in ((result.numerator, left_scale),
                     (value.numerator, right_scale),
                     (result.denominator, left_scale)):
            # The sum needs one additional carry bit.  This conservative
            # preflight resource rejection never substitutes an approximation.
            if a and b and a.bit_length() + b.bit_length() > _MAX_BITS - 1:
                raise ResourceLimit("grammar sum exceeds integer bit budget")
        result += value
        counter.charge(4)
        if max(result.numerator.bit_length(), result.denominator.bit_length()) > _MAX_BITS:
            raise ResourceLimit("grammar sum exceeds integer bit budget")
    return result


def verify_grammar(candidate, branch):
    """Check the exact requested necessary branch conditions, never a theorem.

    ``centered_high``: every factor coefficient is balanced, all unknown
    theta<1/2 coefficients vanish, and known smooth coefficients sum to0.
    ``open_mixed``: balanced factors and, per physical ray, either a nonzero
    unknown coefficient or zero sum of every smooth coefficient.
    Metadata is ignored.  All actual source/finite checks must follow073.
    """
    counter = _Counter()
    common = {"branch": branch if type(branch) is str else None,
              **_FALSE_SCOPE,
              "necessary_filter_only": True,
              "ordinary_073_admission_required": True,
              "uniform_control_remains_open": True,
              "registered_smooth_range": "1/2<=theta<1",
              "unknown_smooth_range": "0<theta<1/2"}
    try:
        if branch not in ("centered_high", "open_mixed") or type(branch) is not str:
            raise GrammarError("branch must be centered_high or open_mixed")
        if type(candidate) is not dict or set(candidate) != _KEYS:
            raise GrammarError("candidate keys do not match the frozen073 schema")
        if candidate["schema"] != "signed-prime-storage-candidate-v1":
            raise GrammarError("wrong candidate schema")
        spec = candidate["spec"]
        if type(spec) is not dict or set(spec) != {"profile", "theta"}:
            raise GrammarError("spec must contain exactly profile and theta")
        if spec["profile"] != _PROFILE:
            raise GrammarError("candidate is not bound to the registered signed source profile")
        theta = spec["theta"]
        if type(theta) is not list:
            raise GrammarError("theta must be a finite ordered list")
        if len(theta) > 4096:
            raise ResourceLimit("too many smooth coordinates")
        exponents = [_rational(value, "theta", counter) for value in theta]
        if any(not 0 < value < 1 for value in exponents):
            raise GrammarError("theta must lie strictly in(0,1)")
        if any(a >= b for a, b in zip(exponents, exponents[1:])):
            raise GrammarError("theta must be strictly increasing")
        labels = _BASE_LABELS + ["smooth:" + value for value in theta]
        if candidate["labels"] != labels:
            raise GrammarError("labels must completely match the physical source-state order")
        q = _rational(candidate["q"], "q", counter)
        if not 1 <= q < 2:
            raise GrammarError("stage074 requires a fixed rational1<=q<2")
        for flag in _FALSE_SCOPE:
            if candidate[flag] is not False:
                raise GrammarError("false proof claim in candidate field " + flag)
        if candidate["uniform_domination_proved"] is not True:
            raise GrammarError("candidate lacks the required073 domination declaration")
        rays = candidate["rays"]
        if type(rays) is not list or len(rays) > 256:
            raise GrammarError("rays must be a list of at most256 positive rays")
        unknown = [i + 6 for i, value in enumerate(exponents) if value < Fraction(1, 2)]
        known = [i + 6 for i, value in enumerate(exponents) if value >= Fraction(1, 2)]
        checks, violations = [], []
        for index, ray in enumerate(rays):
            if type(ray) is not dict or set(ray) != {"weight", "direction"}:
                raise GrammarError("ray keys must be weight and direction")
            weight = _rational(ray["weight"], "ray weight", counter)
            if weight <= 0:
                raise GrammarError("every listed ray must have strictly positive weight")
            direction = ray["direction"]
            if type(direction) is not list or len(direction) != len(labels):
                raise GrammarError("ray direction must have the complete physical state dimension")
            coefficients = [_rational(value, "ray coefficient", counter) for value in direction]
            factor_balanced = all(coefficients[i] == coefficients[5] for i in (2, 3, 4))
            unknown_nonzero = [labels[i] for i in unknown if coefficients[i] != 0]
            known_sum = _sum_rationals((coefficients[i] for i in known), counter)
            all_sum = _sum_rationals(coefficients[6:], counter)
            counter.charge(len(coefficients) + 3)
            reasons = []
            if not factor_balanced:
                reasons.append("unbalanced_factor_sector_bulk")
            if branch == "centered_high":
                if unknown_nonzero:
                    reasons.append("unknown_smooth_coefficient_in_centered_high")
                if known_sum != 0:
                    reasons.append("nonzero_registered_smooth_bulk_sum")
                mode = "registered_bulk_annihilation"
            elif unknown_nonzero:
                # Deliberately do not impose a high-only sum constraint on
                # unknown mixtures: their second-order cancellation is open.
                mode = "unregistered_mixture_retained_open"
            else:
                if all_sum != 0:
                    reasons.append("nonzero_pure_registered_smooth_bulk_sum")
                mode = "registered_bulk_annihilation"
            record = {"ray": index, "factor_balanced": factor_balanced,
                      "unknown_nonzero_labels": unknown_nonzero,
                      "registered_smooth_sum": str(known_sum),
                      "all_smooth_sum": str(all_sum), "mode": mode,
                      "admitted": not reasons, "reasons": reasons}
            checks.append(record)
            if reasons:
                violations.append(record)
        admitted = not violations
        return {**common, "verified": admitted,
                "status": "NECESSARY_GRAMMAR_ADMITTED" if admitted else "GRAMMAR_REJECTED",
                "operations": counter.ops, "rays_checked": len(rays),
                "ray_checks": checks, "violations": violations,
                "unknown_mixture_rays": [x["ray"] for x in checks
                    if x["mode"] == "unregistered_mixture_retained_open"],
                "q": str(q)}
    except (GrammarError, OverflowError, MemoryError) as error:
        return {**common, "verified": False, "status": "GRAMMAR_REJECTED",
                "operations": counter.ops, "error": str(error),
                "error_type": type(error).__name__, "ray_checks": [], "violations": []}
