"""Exact, source-free obstruction guard for a restricted floor-residual AST.

This module evaluates no Mobius values, floor-residual norms, or candidate scores.
Imported analytic facts are identified in the certificate.  It does not refute a
fixed geometric subsequence.  See FLOOR_RESIDUAL_CUTOFF_ARGUMENT_REVIEW_044.txt.
"""
from copy import deepcopy
from fractions import Fraction as Q
import json
import time


VERSION = "convex_mu_power_cutoff_guard_044_v1"
REFUTED = "REFUTED_ALL_INTEGER_VANISHING_FORCING"
UNSUPPORTED = "UNSUPPORTED"
ROUNDING = {"kind": "dyadic_power_floor", "bits_multiplier": 4,
            "scale": "ceil_log2_N"}
IMPORTED = [
    {"fact": "L2 unitary U commutes with positive dilations; U rho(1/x)=rho(x)/x; U chi=sin(2*pi*x)/(pi*x)",
     "source": "https://arxiv.org/pdf/math/0011254", "location": "section 4, equations 4.1-4.4"},
    {"fact": "The ordinary Riemann zeta function has a zero with real part 1/2",
     "status": "known imported theorem; no simplicity or RH assumption"},
]


class Unsupported(ValueError):
    pass


class ResourceLimit(RuntimeError):
    pass


class Meter:
    """Small exact-algebra proxy; counts are not machine instruction counts."""
    def __init__(self, max_operations=1_000_000, seconds=60, max_bits=4096):
        self.operations = 0
        self.max_operations = max_operations
        self.deadline = time.monotonic() + seconds
        self.max_bits = max_bits

    def charge(self, count=1):
        if count < 0 or self.operations + count > self.max_operations:
            raise ResourceLimit("exact-algebra operation cap")
        self.operations += count
        if time.monotonic() > self.deadline:
            raise ResourceLimit("exact-algebra deadline")

    def rational(self, value):
        if not isinstance(value, Q):
            value = Q(value)
        bits = max(abs(value.numerator).bit_length(), value.denominator.bit_length())
        self.charge(1 + bits // 64)
        if bits > self.max_bits:
            raise ResourceLimit("exact rational bit cap")
        return value


def _encoded(obj):
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), allow_nan=False)


def _same(a, b):
    # JSON identity is type strict: True is not the integer 1.
    return _encoded(a) == _encoded(b)


def _keys(obj, names):
    if type(obj) is not dict or set(obj) != set(names):
        raise Unsupported("unexpected AST fields")


def _rational(value, meter):
    if type(value) is not str or not value or len(value) > 2500:
        raise Unsupported("canonical rational string required")
    try:
        out = Q(value)
    except (ValueError, ZeroDivisionError):
        raise Unsupported("invalid rational") from None
    if str(out) != value:
        raise Unsupported("noncanonical rational")
    return meter.rational(out)


def _power(ast, meter):
    _keys(ast, ("kind", "coordinate", "alpha", "gamma"))
    if ast["kind"] != "taper" or ast["coordinate"] != "cutoff" or ast["gamma"] != "1":
        raise Unsupported("only fixed cutoff power tapers with outer gamma=1 are supported")
    a = _rational(ast["alpha"], meter)
    if a <= 0:
        raise Unsupported("cutoff power must be positive")
    return a


def _parse_request(request, meter):
    _keys(request, ("recipe", "q", "b", "domain", "rounding"))
    try:
        size = len(_encoded(request))
    except (ValueError, TypeError):
        raise Unsupported("finite JSON payload required") from None
    if size > 65536:
        raise ResourceLimit("input JSON exceeds 64 KiB")
    meter.charge(1 + size // 64)
    recipe = request["recipe"]
    _keys(recipe, ("id", "base", "auxiliary"))
    if type(recipe["id"]) is not str or len(recipe["id"]) > 256:
        raise Unsupported("bounded ordinal label required")
    q = request["q"]
    if type(q) is not int or not 2 <= q <= 4096:
        raise Unsupported("integer dilation 2<=q<=4096 required")
    b = _rational(request["b"], meter)
    margin = meter.rational(q - meter.rational(b*b))
    if margin <= 0:
        raise Unsupported("strict |b|<sqrt(q) required")
    domain = request["domain"]
    _keys(domain, ("kind", "minimum"))
    if domain["kind"] != "all_integer":
        raise Unsupported("the obstruction requires all integers, not a geometric subsequence")
    if type(domain["minimum"]) is not int or not 2 <= domain["minimum"] <= 2**31:
        raise Unsupported("integer eventual-domain minimum required")
    if not _same(request["rounding"], ROUNDING):
        raise Unsupported("exact 4*ceil(log2 N) dyadic power-floor policy required")
    base = _power(recipe["base"], meter)
    terms = [(base, Q(1))]
    aux = recipe["auxiliary"]
    if aux is not None:
        _keys(aux, ("channel", "coefficient", "envelope"))
        if aux["channel"] != "mu":
            raise Unsupported("only actual Mobius auxiliary source is supported")
        coefficient = _rational(aux["coefficient"], meter)
        envelope = aux["envelope"]
        _keys(envelope, ("kind", "left", "right"))
        if envelope["kind"] != "difference":
            raise Unsupported("only the literal difference-of-tapers envelope is supported")
        # c=-mu*base + coefficient*mu*(left-right), hence effective
        # cutoff weight base-coefficient*left+coefficient*right.
        terms += [(_power(envelope["left"], meter), -coefficient),
                  (_power(envelope["right"], meter), coefficient)]
    return q, b, margin, terms


def _add(a, b, meter):
    out = [Q(0)] * max(len(a), len(b))
    for i in range(len(out)):
        out[i] = meter.rational((a[i] if i < len(a) else 0) +
                                (b[i] if i < len(b) else 0))
    return _trim(out)


def _trim(poly):
    while len(poly) > 1 and poly[-1] == 0:
        poly.pop()
    return poly


def _mul(a, b, meter):
    out = [Q(0)] * (len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            product = meter.rational(x*y)
            out[i+j] = meter.rational(out[i+j]+product)
    return _trim(out)


def _serialize(poly):
    return [str(x) for x in poly]


def _mixture(terms, meter):
    combined = {}
    for alpha, weight in terms:
        combined[alpha] = meter.rational(combined.get(alpha, Q(0))+weight)
    result = sorted((a, w) for a, w in combined.items() if w != 0)
    if not result or any(w < 0 for _, w in result) or sum(w for _, w in result) != 1:
        raise Unsupported("effective source weight is not a convex mixture")
    return result


def _kernel(mixture, meter):
    denominator = [Q(0), Q(1)]
    for a, _ in mixture:
        denominator = _mul(denominator, [a, Q(1)], meter)
    numerator = [Q(0)]
    for i, (a, w) in enumerate(mixture):
        term = [meter.rational(w*a)]
        for j, (other, _) in enumerate(mixture):
            if j != i:
                term = _mul(term, [other, Q(1)], meter)
        numerator = _add(numerator, term, meter)
    return numerator, denominator


def _facts(request, q, b, margin, mixture, meter):
    lip = Q(0)
    for a, w in mixture:
        lip = meter.rational(lip + meter.rational(a*w))
    return {
        "request": deepcopy(request),
        "status": REFUTED,
        "uniform_vanishing_forcing_impossible": True,
        "individual_geometric_subsequence_status": "OPEN",
        "original_019_041_core_and_RH_status": "OPEN",
        "claims_RH": False,
        "uses_actual_source_evaluation": False,
        "imported_facts": deepcopy(IMPORTED),
        "mixture": [{"alpha": str(a), "weight": str(w)} for a, w in mixture],
        "contraction_margin_q_minus_b_squared": str(margin),
        "kernel_nonvanishing": {
            "domain": "Re(s)>0", "argument": "positive Stieltjes real parts",
            "identity": "s*K(s)=sum_i weight_i*alpha_i/(s+alpha_i)",
            "positive_real_part_formula": "sum_i weight_i*alpha_i*(Re(s)+alpha_i)/|s+alpha_i|^2 > 0",
        },
        "rounding": {
            "precision": "4*ceil(log2 N)", "per_weight_absolute_error_bound": "N^-4",
            "constant_T_absolute_error_bound": "N^-3",
            "duplicate_power_floors_are_identical": True,
            "outer_gamma_one_floor_is_exact_on_the_inner_dyadic": True,
        },
        "integer_real_transfer": {
            "cutoff_weight_at_one": "0", "weighted_sum_lipschitz_constant": str(lip),
            "scale_difference_lipschitz_constant": str(meter.rational((q+abs(b))*lip)),
            "new_integer_term_has_zero_endpoint_weight": True,
        },
        "unit_and_harmonic": {
            "unit_term": "c_1=0 through cancellation of -M_w+m_w; no unit basis term inserted",
            "harmonic_bound": "|m_w(N)|<=1+log N",
        },
        "scalar_transfer": {
            "interval": "0<x<1/(q*N)",
            "identity": "U*h_N=S(x)-b*S(q*x)-T_(q*N)+b*T_N",
            "T_identity": "T_N=-M_w(N)+m_w(N)+delta_N",
            "bound": "|T_(q*N)-b*T_N|/sqrt(N)<=sqrt(q)*||h_N||+2*(1+|b|)/sqrt(N)",
            "all_integer_vanishing_implies": "M_w(q*N)-b*M_w(N)=o(sqrt(N))",
        },
        "mellin_transfer": {
            "identity": "M_G(s)=(q^s-b)*K(s)/zeta(s)-q^s*integral_1^q F_w(t)*t^(-s-1)dt",
            "compact_endpoint_correction": "retained and entire",
            "critical_line_multiplier": "|q^rho|=sqrt(q)>|b|",
            "abel_limit": "G=o(sqrt(x)) implies delta*M_G(rho+delta)->0",
            "zero_multiplicity": "any positive multiplicity; zeta(rho+delta)=O(delta)",
        },
        "covered_bound": "||h_N||^2<=A/(1+floor(log2 N))^eta for every integer N>=N0, any finite A>=0 and eta>0",
        "scope": "logical all-integer asymptotic obstruction; no finite norm failure, no subsequence rejection",
    }


def build_guard(request, meter=None):
    """Generate a certificate or an explicitly unsupported result.

    ResourceLimit propagates. Unsupported never means the recipe is false.
    No candidate ID enters the mathematical decision.
    """
    meter = meter or Meter()
    try:
        q, b, margin, terms = _parse_request(request, meter)
        mixture = _mixture(terms, meter)
        numerator, denominator = _kernel(mixture, meter)
        certificate = _facts(request, q, b, margin, mixture, meter)
        certificate["version"] = VERSION
        certificate["mellin_kernel"] = {
            "coefficient_order": "ascending powers of s",
            "numerator": _serialize(numerator), "denominator": _serialize(denominator),
        }
        meter.charge(1+len(_encoded(certificate))//64)
        return certificate
    except Unsupported as exc:
        return {"version": VERSION, "status": UNSUPPORTED, "reason": str(exc),
                "uniform_vanishing_forcing_impossible": False,
                "individual_geometric_subsequence_status": "OPEN"}


def _verifier_mixture(terms, meter):
    # Separate list-based coefficient normalization, without producer dict merge.
    pending = sorted(terms)
    normalized = []
    while pending:
        alpha = pending[0][0]
        weights = [w for a, w in pending if a == alpha]
        pending = [(a, w) for a, w in pending if a != alpha]
        total = Q(0)
        for w in weights:
            total = meter.rational(total+w)
        if total:
            if total < 0:
                raise ValueError("negative effective cutoff weight")
            normalized.append((alpha, total))
    if not normalized or sum(w for _, w in normalized) != 1:
        raise ValueError("nonconvex effective cutoff mixture")
    return normalized


def verify_guard(request, certificate, meter=None):
    """Verify a REFUTED certificate. Reject unsupported requests or tampering.

    The checker does not call build_guard or the producer kernel constructor.
    It recomposes the literal Stieltjes fractions by exact cross multiplication.
    Analytic imported facts are theorem dependencies, not numerically replayed.
    """
    meter = meter or Meter()
    try:
        q, b, margin, terms = _parse_request(request, meter)
    except Unsupported as exc:
        raise ValueError("unsupported proof request: "+str(exc)) from None
    mixture = _verifier_mixture(terms, meter)
    if type(certificate) is not dict or len(_encoded(certificate)) > 65536:
        raise ValueError("bounded certificate object required")
    expected = _facts(request, q, b, margin, mixture, meter)
    expected["version"] = VERSION
    if set(certificate) != set(expected) | {"mellin_kernel"}:
        raise ValueError("certificate fields differ from scoped proof schema")
    for name, value in expected.items():
        if not _same(certificate[name], value):
            raise ValueError("certificate mismatch: "+name)
    saved = certificate["mellin_kernel"]
    try:
        _keys(saved, ("coefficient_order", "numerator", "denominator"))
    except Unsupported as exc:
        raise ValueError(str(exc)) from None
    if saved["coefficient_order"] != "ascending powers of s":
        raise ValueError("polynomial order mismatch")
    def poly(values):
        if type(values) is not list or not 1 <= len(values) <= 5:
            raise ValueError("bounded polynomial list required")
        try:
            out = [_rational(x, meter) for x in values]
        except Unsupported as exc:
            raise ValueError(str(exc)) from None
        if out != _trim(out[:]):
            raise ValueError("noncanonical trailing polynomial zeros")
        return out
    numerator, denominator = poly(saved["numerator"]), poly(saved["denominator"])
    # Check the declared denominator is s*product(s+alpha), then verify
    # P(s)*product_i s(s+alpha_i) = Q(s)*sum_i w_i alpha_i product_(j!=i) s(s+alpha_j).
    # No polynomial division or reuse of _kernel is needed.
    denominator_expected = [Q(1)]
    for a, _ in mixture:
        denominator_expected = _mul(denominator_expected, [a, Q(1)], meter)
    denominator_expected = [Q(0)] + denominator_expected
    if denominator != denominator_expected:
        raise ValueError("denominator does not bind the positive Stieltjes terms")
    fraction_denominators = [[Q(0), a, Q(1)] for a, _ in mixture]
    common = [Q(1)]
    for term_denominator in fraction_denominators:
        common = _mul(common, term_denominator, meter)
    total = [Q(0)]
    for i, (a, w) in enumerate(mixture):
        product = [meter.rational(a*w)]
        for j, term_denominator in enumerate(fraction_denominators):
            if j != i:
                product = _mul(product, term_denominator, meter)
        total = _add(total, product, meter)
    if _mul(numerator, common, meter) != _mul(denominator, total, meter):
        raise ValueError("Mellin kernel recomposition failed")
    meter.charge(1+len(_encoded(certificate))//64)
    return {"verified": True, "status": REFUTED,
            "uniform_vanishing_forcing_impossible": True,
            "individual_geometric_subsequence_status": "OPEN",
            "original_019_041_core_and_RH_status": "OPEN",
            "claims_RH": False}
