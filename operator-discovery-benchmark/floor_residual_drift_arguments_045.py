"""Source-free exact argument generation for moving Mobius drift profiles.

No norm/source data are evaluated. Certificates expose conditional leaves;
neither numerical calibration nor RH is an admitted premise.
"""
from copy import deepcopy
from fractions import Fraction as Q
import json
import math
import time

SCHEMA = "floor-residual-drift-arguments-045-v1"
ROUNDING = {"kind": "dyadic_power_floor", "bits_multiplier": 4,
            "scale": "ceil_log2_N", "drift": "round_each_exponential_before_signed_sum",
            "product": "multiply_rounded_children_exactly"}


class Unsupported(ValueError):
    pass


class Meter:
    def __init__(self, cap=10_000_000, seconds=60, max_bits=4096):
        self.cap, self.operations, self.deadline = cap, 0, time.monotonic()+seconds
        self.max_bits = max_bits

    def charge(self, count=1):
        if type(count) is not int or count < 0 or count > self.cap-self.operations:
            raise OverflowError("argument operation cap")
        self.operations += count
        if time.monotonic() > self.deadline:
            raise TimeoutError("argument deadline")

    def rational(self, value):
        value = Q(value)
        bits = max(abs(value.numerator).bit_length(), value.denominator.bit_length())
        self.charge(1+bits)
        if bits > self.max_bits:
            raise OverflowError("argument rational bit cap")
        return value


def _json(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), allow_nan=False)


def _keys(value, names):
    if type(value) is not dict or set(value) != set(names):
        raise Unsupported("exact AST fields required")


def _rat(value, meter):
    if type(value) is not str or not 1 <= len(value) <= 2500:
        raise Unsupported("bounded canonical rational required")
    try:
        q = Q(value)
    except (ValueError, ZeroDivisionError):
        raise Unsupported("invalid rational") from None
    if str(q) != value:
        raise Unsupported("canonical rational required")
    return meter.rational(q)


def _parse(request, meter):
    _keys(request, ("recipe", "q", "b", "domain", "rounding"))
    try:
        size = len(_json(request))
    except (TypeError, ValueError):
        raise Unsupported("finite JSON request required") from None
    if size > 65536:
        raise OverflowError("argument input size cap")
    meter.charge(1+size//64)
    recipe = request["recipe"]
    _keys(recipe, ("id", "base", "auxiliary"))
    if type(recipe["id"]) is not str or len(recipe["id"]) > 256 or recipe["auxiliary"] is not None:
        raise Unsupported("ordinal label and null external auxiliary required")
    base, taper = recipe["base"], None
    if type(base) is dict and base.get("kind") == "product":
        _keys(base, ("kind", "left", "right"))
        left, right = base["left"], base["right"]
        if type(left) is dict and left.get("kind") == "drift_mixture":
            drift, taper = left, right
        elif type(right) is dict and right.get("kind") == "drift_mixture":
            drift, taper = right, left
        else:
            raise Unsupported("product needs exactly one drift and one taper")
    else:
        drift = base
    _keys(drift, ("kind", "a", "theta", "terms"))
    if drift["kind"] != "drift_mixture":
        raise Unsupported("legacy controls are unsupported by this argument generator")
    a, theta = _rat(drift["a"], meter), _rat(drift["theta"], meter)
    if a <= 0 or not 0 < theta < 1:
        raise Unsupported("a>0 and 0<theta<1 required")
    if type(drift["terms"]) is not list or not 1 <= len(drift["terms"]) <= 8:
        raise Unsupported("one to eight drift terms required")
    terms, previous = [], Q(0)
    for term in drift["terms"]:
        _keys(term, ("rate", "weight"))
        rate, weight = _rat(term["rate"], meter), _rat(term["weight"], meter)
        if rate <= previous or weight == 0:
            raise Unsupported("sorted distinct positive rates and nonzero weights required")
        terms.append((rate, weight)); previous = rate
    if sum(w for _, w in terms) != 1:
        raise Unsupported("signed weights must sum to one")
    taper_data = None
    if taper is not None:
        _keys(taper, ("kind", "coordinate", "alpha", "gamma"))
        if taper["kind"] != "taper" or taper["coordinate"] not in ("cutoff", "log"):
            raise Unsupported("one frozen044 cutoff or log taper required")
        alpha, gamma = _rat(taper["alpha"], meter), _rat(taper["gamma"], meter)
        if alpha <= 0 or gamma <= 0:
            raise Unsupported("positive taper powers required")
        taper_data = (taper["coordinate"], alpha, gamma)
    q, b = request["q"], _rat(request["b"], meter)
    if type(q) is not int or not 2 <= q <= 4096:
        raise Unsupported("bounded integer q>=2 required")
    if meter.rational(b*b) >= q:
        raise Unsupported("RH-bearing contraction requires |b|<sqrt(q)")
    _keys(request["domain"], ("kind", "minimum"))
    if request["domain"]["kind"] not in ("all_integer", "geometric_chain"):
        raise Unsupported("explicit all_integer or geometric_chain domain required")
    minimum = request["domain"]["minimum"]
    if type(minimum) is not int or not 2 <= minimum <= 2**31:
        raise Unsupported("bounded integer domain minimum required")
    if _json(request["rounding"]) != _json(ROUNDING):
        raise Unsupported("exact drift and child-product rounding policy required")
    return a, theta, terms, taper_data, q, b


def _mul(a, b, meter):
    out = [Q(0)]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i+j] = meter.rational(out[i+j]+meter.rational(x*y))
    return out


def _moments(terms, meter):
    out = []
    for k in range(len(terms)+1):
        value = Q(0)
        for r, w in terms:
            power = Q(1)
            for _ in range(k):
                power = meter.rational(power*r)
            value = meter.rational(value+meter.rational(w*power))
        out.append(value)
    return out


def _profile_kernel(terms, meter):
    denominator = [Q(1)]
    for r, _ in terms:
        denominator = _mul(denominator, [r, Q(1)], meter)
    numerator = [Q(0)]*len(terms)
    for i, (r, w) in enumerate(terms):
        term = [meter.rational(w*r)]
        for j, (other, _) in enumerate(terms):
            if j != i:
                term = _mul(term, [other, Q(1)], meter)
        numerator = [meter.rational(x+y) for x, y in zip(numerator, term)]
    return numerator, denominator


def _power(value, exponent, meter):
    answer = Q(1)
    for _ in range(exponent):
        answer = meter.rational(answer*value)
    return answer


def _ceil(value):
    return (value.numerator+value.denominator-1)//value.denominator


def _level_envelope(a, theta, terms, taper, m, H, d, Cround, b, meter):
    """Rational all-large-level harmonic majorant; never constructs huge N."""
    if taper is not None and taper[0] == "log":
        return {"status": "OPEN_LOG_TAPER_HARMONIC", "fixed_domain_budget_proved": False}
    kappa = meter.rational(1-theta)
    tau = meter.rational(m*kappa)
    kt = max(1, _ceil(meter.rational((m+1)*kappa/theta)))
    kc = max(1, _ceil(meter.rational(tau/theta)))
    kr = max(1, _ceil(meter.rational(tau+1)))
    if max(kt, kc, kr) > 64:
        return {"status": "UNSUPPORTED_FACTORIAL_DEPTH", "requested_depth": max(kt, kc, kr),
                "fixed_domain_budget_proved": False}
    meter.charge(kt+kc+kr)
    cbias = meter.rational(H*_power(a+1, m, meter))
    ctail = Q(0)
    for r, w in terms:
        ra = meter.rational(r*a)
        contribution = meter.rational(abs(w)*math.factorial(kt)*_power(Q(4), kt, meter)/_power(ra, kt+1, meter))
        ctail = meter.rational(ctail+contribution)
    cround = meter.rational(2*Cround*math.factorial(kr)/_power(d, kr, meter))
    ccut = Q(0)
    constraints = [{"left": "L^(1-theta)", "right": str(meter.rational(8*terms[-1][0]*(a+1))),
                    "purpose": "rmax*beta_N<=1/8"}]
    if taper is not None:
        _, alpha, gamma = taper
        cut_constant = meter.rational(max(Q(1), gamma)*sum(abs(w) for _, w in terms)*(1+2/alpha))
        ra = meter.rational(terms[0][0]*a)
        ccut = meter.rational(cut_constant*math.factorial(kc)*_power(Q(4)/ra, kc, meter))
        constraints.append({"left": "L^(1-theta)",
                            "right": str(meter.rational(2*terms[0][0]*(a+1)/alpha)),
                            "purpose": "rmin*beta_N<=alpha/2"})
    scalar = meter.rational(cbias+ctail+cround+ccut)
    energy = meter.rational(2*scalar*scalar*(1+abs(b))**2)
    return {"status": "EXPLICIT_CONDITIONAL_LEVEL_THRESHOLD",
            "level_variable": "L=1+floor(log2 N)", "minimum_level": 2,
            "level_constraints": constraints, "scalar_exponent": str(tau),
            "factorial_depths": {"harmonic_tail": kt, "cutoff": kc, "rounding": kr},
            "constants": {"local_bias": str(cbias), "absolute_harmonic_tail": str(ctail),
                          "rounding_harmonic": str(cround), "cutoff_harmonic": str(ccut)},
            "scalar_constant": str(scalar), "scalar_bound": "|A_N(1)|<=scalar_constant*L^(-scalar_exponent)",
            "energy_constant": str(energy), "energy_exponent": str(meter.rational(2*tau)),
            "energy_bound": "E_harmonic(N)<=energy_constant*L^(-energy_exponent)",
            "elementary_rules": ["log 2>=1/2", "log N>=L/4 and 1+log N<=2L for L>=2",
                                 "exp(-x)<=k!/x^k for x>0 and integer k>=1",
                                 "beta_N>=a*L^(theta-1) and beta_N<=(a+1)*L^(theta-1)",
                                 "L(qN)>=L(N), so child scalar rate does not grow"],
            "fixed_domain_budget_proved": False,
            "remaining": "verify level constraints and target constant/exponent budget; separately price earlier domain levels"}


def _defs(request, a, theta, terms, taper, q, b, m, Cw, H, d, Cround, meter):
    drift = request["recipe"]["base"]
    scalar_status = "EXPLICIT_UNCONDITIONAL_ENVELOPE" if taper is None or taper[0] == "cutoff" else "OPEN_TAPER_HARMONIC_DISCREPANCY"
    comparison = {"op": "signed_sum", "terms": [
        {"weight": str(w), "expr": {"op": "reciprocal_zeta", "argument":
         {"op": "add", "left": "s", "right": {"op": "multiply", "left": str(r), "right": "beta_N"}}}}
        for r, w in terms]}
    scale = {"op": "scale_difference", "child_substitution": "N -> q*N",
             "q": q, "b": str(b), "dilation_multiplier": "q^(-s)",
             "child_level_beta_cutoff_precision_recomputed": True}
    bias = {**scale, "operand": {"op": "divide", "numerator":
            {"op": "subtract", "left": "1", "right": {"op": "multiply", "left": "zeta(s)", "right": "S_N(s)"}}, "denominator": "s"}}
    truncation = {**scale, "operand": {"op": "divide", "numerator":
                  {"op": "multiply", "left": "-zeta(s)", "right": "Delta_N(s)"}, "denominator": "s"}}
    harmonic = {**scale, "operand": {"op": "divide", "numerator":
                {"op": "multiply", "left": "zeta(s)", "right": "A_N(1)"}, "denominator": "s"}}
    data = {
        "request": deepcopy(request), "schema": SCHEMA, "status": "CONDITIONAL_ARGUMENT_GENERATED",
        "uniform_forcing_bound_proved": False, "norm_convergence_proved": False,
        "RH_proved": False, "RH_refuted": False, "source_values_evaluated": False,
        "fixed_program_norms_evaluated": False,
        "beta": {"level": "L(N)=1+floor(log2 N)", "definition": "ceil(a*L(N)^theta)/L(N)",
                 "a": str(a), "theta": str(theta), "bounds": "a*L^(theta-1)<=beta_N<a*L^(theta-1)+L^(-1)",
                 "limit": "beta_N->0; beta_N*log N->infinity"},
        "finite_source": {"symbol": "A_N(s)", "op": "finite_dirichlet_sum",
                          "source": "actual ordinary mu", "range": "1<=n<=N", "unit": "included",
                          "coefficient": {"op": "exact_rounded_recipe", "AST": deepcopy(drift)},
                          "identity": "A_N(s)=sum_(n<=N) mu(n)*V_N(n)*n^(-s)"},
        "comparison": {"symbol": "S_N(s)", "AST": comparison,
                       "definition_scope": "meromorphic expression; NOT an assumed convergent critical-line mu series"},
        "discrepancy": {"symbol": "Delta_N(s)", "identity": "A_N(s)-S_N(s)",
                        "finite_decomposition": "rounded finite - unrounded tapered finite + unrounded tapered finite - unrounded bare finite + unrounded bare finite - S_N(s)",
                        "rounding_and_taper_and_truncation_retained": True},
        "whole_mellin": {
            "basis": "Mellin(f_n)(s)=-zeta(s)*(n^(-s)-1/n)/s",
            "target": "Mellin(e_N)(s)=[1-zeta(s)*(A_N(s)-A_N(1))]/s",
            "forcing": "Mellin(h_N)(s)=[1-b*q^(-s)-zeta(s)*(A_(qN)(s)-A_(qN)(1)-b*q^(-s)*(A_N(s)-A_N(1)))]/s",
            "indicator": "chi-b*D_q chi retained as 1-b*q^(-s)",
            "unit": "the n=1 term cancels identically in A_N(s)-A_N(1), including optional taper",
            "at_s_one": "removable zeta pole because A_N(s)-A_N(1) vanishes there",
            "plancherel": "||h_N||^2=(1/(2*pi))*integral_R |Mellin(h_N)(1/2+i*t)|^2 dt",
        },
        "finite_partial_summation": {
            "M": "M(x)=sum_(n<=x) actual_mu(n)",
            "bare_component": "sum_(n<=N) mu(n)*n^(-z)=M(N)*N^(-z)+z*integral_1^N M(x)*x^(-z-1)dx",
            "weighted_component": "A_N^unrounded(s)=M(N)*V_N^unrounded(N)*N^(-s)-integral_1^N M(x)*d[V_N^unrounded(x)*x^(-s)]",
            "unit": "M(1) is retained by the endpoint convention",
            "warning": "an absolute M(x)<=C_epsilon*x^(1/2+epsilon) premise for every epsilon would imply RH and supplies no uniform constants as epsilon->0",
        },
        "joint_components": {"bias": bias, "truncation": truncation, "harmonic": harmonic},
        "energies": {
            "measure": "(1/(2*pi))*dt on s=1/2+i*t", "sum_before_square": True,
            "full": "E_bias+E_truncation+E_harmonic+2*Re(cross_bias_truncation+cross_bias_harmonic+cross_truncation_harmonic)",
            "joint_bias_truncation": "energy of bias+truncation, before absolute values; meromorphic comparison cancels exactly",
            "joint_status": "OPEN; with harmonic added this is endpoint-equivalent to whole forcing, not a smaller-scale theorem",
        },
        "leaves": [
            {"id": "BIAS", "status": "OPEN", "expression": "E_bias(N)",
             "integrability": "OPEN: shifted reciprocal-zeta poles on the critical contour must be absent/cancelled within this block",
             "arithmetic": "requires uniform small drift transfer, not supplied by moment cancellation"},
            {"id": "TRUNCATION", "status": "OPEN", "expression": "E_truncation(N)",
             "integrability": "OPEN independently; poles introduced by comparison may cancel only against BIAS",
             "arithmetic": "complete finite tail, both parent/child endpoints, taper and rounding discrepancy; do not replace by assumed RH companion bounds"},
            {"id": "HARMONIC", "status": scalar_status, "expression": "E_harmonic(N)",
             "fixed_A_eta_all_N_budget_status": "UNPAID_FINITE_HEAD_AND_CONSTANT_MATCH",
             "norm_bound": "<=2*(|A_(qN)(1)|+|b|*q^(-1/2)*|A_N(1)|)^2"},
        ],
        "paid_harmonic_scalar": {
            "order": m, "constant_H": str(H), "Cw": str(Cw), "condition": "rmax*beta_N<=1/8",
            "bare_unrounded_bound": "|A_N^bare,unrounded(1)|<=H*beta_N^m+sum_j |w_j|*N^(-r_j*beta_N)/(r_j*beta_N)",
            "actual_complete_bound_rule": "bare_unrounded_bound + cutoff_extra (when present and its condition holds) + Cround*N^(-4*d)*(1+log N); log_taper_extra remains OPEN",
            "reciprocal_zeta_local": "on |z|<=1/4, |z*zeta(1+z)-1|<=2/3 and |1/zeta(1+z)|<=3/4",
            "cauchy_and_moments": "H=(3/2)*4^m*sum_j |w_j|*r_j^m, valid rmax*beta<=1/8",
            "tail_scope": "absolute n>N harmonic tail converges since r_j*beta>0; no critical-line Dirichlet convergence assumed",
            "cutoff_extra": None if taper is None or taper[0] != "cutoff" else
                {"constant": str(meter.rational(max(Q(1), taper[2])*Cw*(1+2/taper[1]))),
                 "condition": "rmin*beta_N<=alpha/2", "bound": "constant*N^(-rmin*beta_N)"},
            "log_taper_extra": "OPEN: actual taper-harmonic discrepancy retained" if taper is not None and taper[0] == "log" else None,
            "asymptotic_energy_rate": str(meter.rational(2*m*(1-theta))) if taper is None or taper[0] == "cutoff" else None,
            "critical_norm_reference": "||zeta(s)/s||^2 on Re(s)=1/2 = ||rho(1/x)||_L2(0,infinity)^2<=2",
        },
        "rounding": {"precision": "p=4*ceil(log2 N)", "d": str(d), "Cround": str(Cround),
                     "pointwise_coefficient_error": "<=Cround*N^(-4*d)",
                     "target_error_squared_norm": "<=8*Cround^2*N^(1-8*d)",
                     "forcing_error_squared_norm": "<=8*Cround^2*(q+|b|)^2*N^(1-8*d)",
                     "norm_exponent": str(meter.rational(8*d-1)),
                     "source_bound": "||f_n||^2<=2/n; sum_(n<=N) n^(-1/2)<=2*sqrt N",
                     "negative_rounded_profile_possible": True, "no_clamp_or_unrounded_range_substitution": True,
                     "included_inside_discrepancy": True},
        "proof_guards": {
            "finite_identity_unconditional": True, "separate_blocks_L2_unconditional": False,
            "uniform_RH_or_Mertens_companion_assumed": False,
            "lost_cancellation": "positive split drops cross terms between BIAS/TRUNCATION/HARMONIC; signed mixture and parent-child crosses remain inside every leaf",
            "closure_rule": "admit only after every integrability and exact all-domain budget premise is independently proved",
            "subsequence_scope": "no chain convergence or all-integer forcing bound claimed",
        },
    }
    data["harmonic_level_envelope"] = _level_envelope(a, theta, terms, taper, m, H, d, Cround, b, meter)
    return data


def build_arguments(request, meter=None):
    meter = meter or Meter()
    try:
        a, theta, terms, taper, q, b = _parse(request, meter)
    except Unsupported as exc:
        return {"schema": SCHEMA, "status": "UNSUPPORTED", "reason": str(exc),
                "uniform_forcing_bound_proved": False, "RH_proved": False}
    moments = _moments(terms, meter)
    m = next(k for k in range(1, len(terms)+1) if moments[k])
    Cw = meter.rational(sum(abs(w) for _, w in terms))
    H = meter.rational(Q(3, 2)*4**m*sum(abs(w)*r**m for r, w in terms))
    if taper is None:
        d, Cround = Q(1), Cw
    else:
        coord, alpha, gamma = taper
        d = min(Q(1), gamma)
        factor = max(Q(1), gamma)
        if coord == "log":
            d = meter.rational(d*min(Q(1), alpha))
            factor = meter.rational(factor*(max(Q(1), alpha)+1))
        Cround = meter.rational(Cw*(2+factor))
    certificate = _defs(request, a, theta, terms, taper, q, b, m, Cw, H, d, Cround, meter)
    numerator, denominator = _profile_kernel(terms, meter)
    product = meter.rational(math.prod(r for r, _ in terms))
    maximal = m == len(terms)
    if maximal and numerator != [product]+[Q(0)]*(len(terms)-1):
        raise ArithmeticError("maximal-order Laplace numerator mismatch")
    certificate["profile"] = {
        "order": m, "moments": [str(x) for x in moments], "maximal_order": maximal,
        "laplace_numerator_ascending": [str(x) for x in numerator],
        "laplace_denominator_ascending": [str(x) for x in denominator],
        "rate_product": str(product),
        "raw_survival_range_proved": maximal,
        "raw_survival_identity": "-Laplace(P')=product_j r_j/(s+r_j)" if maximal else None,
        "simplex_coefficient": str(meter.rational(product/Q(math.factorial(m)))) if maximal else None,
        "signed_taylor_coefficient": str(meter.rational(sum(abs(w)*r**m for r, w in terms)/math.factorial(m))),
        "coefficient_control_only": True,
    }
    meter.charge(1+len(_json(certificate))//64)
    return certificate


def verify_arguments(request, certificate, meter=None):
    """Independent moment/kernel arithmetic and strict theorem-schema replay."""
    meter = meter or Meter()
    try:
        a, theta, terms, taper, q, b = _parse(request, meter)
    except Unsupported as exc:
        raise ValueError("unsupported argument request: "+str(exc)) from None
    if type(certificate) is not dict or len(_json(certificate)) > 262144:
        raise ValueError("bounded certificate required")
    profile = certificate.get("profile")
    if type(profile) is not dict:
        raise ValueError("profile proof required")
    # Independent simultaneous-power accumulation, not _moments.
    moments = [Q(0)]*(len(terms)+1)
    for r, w in terms:
        power = Q(1)
        for k in range(len(moments)):
            moments[k] = meter.rational(moments[k]+meter.rational(w*power))
            if k+1 < len(moments):
                power = meter.rational(power*r)
    m = next(k for k in range(1, len(moments)) if moments[k])
    numerator_values, denominator_values = profile.get("laplace_numerator_ascending"), profile.get("laplace_denominator_ascending")
    if type(numerator_values) is not list or len(numerator_values) != len(terms) or type(denominator_values) is not list or len(denominator_values) != len(terms)+1:
        raise ValueError("kernel polynomial dimensions")
    try:
        numerator = [_rat(x, meter) for x in numerator_values]
        denominator = [_rat(x, meter) for x in denominator_values]
    except Unsupported as exc:
        raise ValueError(str(exc)) from None
    # A degree-m denominator and degree-(m-1) numerator are identified by
    # m+1 literal rational sample values; no producer coefficient construction.
    def evaluate(poly, x):
        answer = Q(0)
        for c in reversed(poly):
            answer = meter.rational(meter.rational(answer*x)+c)
        return answer
    for k in range(len(terms)+1):
        x = Q(k)
        den_literal, sum_literal = Q(1), Q(0)
        for r, w in terms:
            den_literal = meter.rational(den_literal*(x+r))
            sum_literal = meter.rational(sum_literal+meter.rational(w*r/(x+r)))
        if evaluate(denominator, x) != den_literal or evaluate(numerator, x) != meter.rational(den_literal*sum_literal):
            raise ValueError("literal profile rational-kernel verification failed")
    Cw = meter.rational(sum(abs(w) for _, w in terms))
    H = meter.rational(Q(3, 2)*4**m*sum(abs(w)*r**m for r, w in terms))
    if taper is None:
        d, Cround = Q(1), Cw
    else:
        coord, alpha, gamma = taper
        d, factor = min(Q(1), gamma), max(Q(1), gamma)
        if coord == "log":
            d, factor = meter.rational(d*min(Q(1), alpha)), meter.rational(factor*(max(Q(1), alpha)+1))
        Cround = meter.rational(Cw*(2+factor))
    expected = _defs(request, a, theta, terms, taper, q, b, m, Cw, H, d, Cround, meter)
    product = meter.rational(math.prod(r for r, _ in terms))
    maximal = m == len(terms)
    if maximal and numerator != [product]+[Q(0)]*(len(terms)-1):
        raise ValueError("maximal-order survival-kernel identity failed")
    expected["profile"] = {
        "order": m, "moments": [str(x) for x in moments], "maximal_order": maximal,
        "laplace_numerator_ascending": numerator_values, "laplace_denominator_ascending": denominator_values,
        "rate_product": str(product), "raw_survival_range_proved": maximal,
        "raw_survival_identity": "-Laplace(P')=product_j r_j/(s+r_j)" if maximal else None,
        "simplex_coefficient": str(meter.rational(product/Q(math.factorial(m)))) if maximal else None,
        "signed_taylor_coefficient": str(meter.rational(sum(abs(w)*r**m for r, w in terms)/math.factorial(m))),
        "coefficient_control_only": True,
    }
    if _json(certificate) != _json(expected):
        raise ValueError("argument/source/proof-scope payload mismatch")
    meter.charge(1+len(_json(certificate))//64)
    return {"verified": True, "status": "CONDITIONAL_ARGUMENT_GENERATED",
            "uniform_forcing_bound_proved": False, "RH_proved": False,
            "whole_joint_energy_status": "OPEN"}


def enumerate_allocations(max_denominator=6):
    if type(max_denominator) is not int or not 3 <= max_denominator <= 32:
        raise ValueError("allocation denominator cap 3..32")
    found = set()
    for den in range(3, max_denominator+1):
        for i in range(1, den-1):
            for j in range(1, den-i):
                found.add((Q(i, den), Q(j, den), Q(den-i-j, den)))
    return [[str(x) for x in row] for row in sorted(found)]


def instantiate_bound(certificate, A, eta, allocation=None, meter=None):
    """Synthesize a sufficient Young argument; every global budget stays unpaid."""
    meter = meter or Meter()
    if type(certificate) is not dict or "request" not in certificate:
        raise ValueError("verified-shape argument certificate required")
    verify_arguments(certificate["request"], certificate, meter)
    try:
        A, eta = _rat(A, meter), _rat(eta, meter)
        allocation = ["1/3", "1/3", "1/3"] if allocation is None else allocation
        if type(allocation) is not list:
            raise ValueError("allocation list required")
        weights = [_rat(x, meter) for x in allocation]
    except Unsupported as exc:
        raise ValueError(str(exc)) from None
    if A <= 0 or not 0 < eta <= 1 or len(weights) != 3 or any(x <= 0 for x in weights) or sum(weights) != 1:
        raise ValueError("positive target A, 0<eta<=1, positive unit-sum three-way allocation required")
    premises = []
    for name, weight in zip(("BIAS", "TRUNCATION", "HARMONIC"), weights):
        premises.append({"leaf": name, "energy_upper_constant": str(meter.rational(A*weight*weight)),
                         "eta": str(eta), "all_domain_required": deepcopy(certificate["request"]["domain"]),
                         "status": "OPEN_ALL_DOMAIN_BUDGET", "young_weight": str(weight)})
    paid_rate = certificate["paid_harmonic_scalar"]["asymptotic_energy_rate"]
    level = certificate["harmonic_level_envelope"]
    harmonic_budget = None
    if level["status"] == "EXPLICIT_CONDITIONAL_LEVEL_THRESHOLD":
        harmonic_budget = {"energy_exponent_minus_eta": str(meter.rational(Q(level["energy_exponent"])-eta)),
                           "energy_constant_over_allocated_budget": str(meter.rational(Q(level["energy_constant"])/(A*weights[2]**2))),
                           "condition": "if exponent gap>0 require L^gap>=ratio; if gap=0 require ratio<=1; negative gap is not paid by this envelope",
                           "also_required": deepcopy(level["level_constraints"]),
                           "earlier_levels": "OPEN finite-domain scalar pricing", "status": "CONDITIONAL_EXACT_LEVEL_BUDGET"}
    return {"schema": "floor-residual-drift-young-route-045-v1", "A": str(A), "eta": str(eta),
            "premises": premises, "identity": "E_h<=sum_i E_i/young_weight_i",
            "constant_recomposition": str(meter.rational(sum(Q(p["energy_upper_constant"])/w for p, w in zip(premises, weights)))),
            "integrability_premises": ["BIAS and TRUNCATION are L2 independently; comparison poles absent or cancelled inside each block"],
            "harmonic_rate_can_pay_eventually": paid_rate is not None and Q(paid_rate) > eta,
            "harmonic_explicit_budget_reduction": harmonic_budget,
            "eventual_is_not_fixed_domain": True, "uniform_forcing_bound_proved": False,
            "lost_crosses": ["BIAS/TRUNCATION", "BIAS/HARMONIC", "TRUNCATION/HARMONIC"],
            "alternative": "retain joint BIAS+TRUNCATION energy if their poles or cancellations prevent separate bounds"}
