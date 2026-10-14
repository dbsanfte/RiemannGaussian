"""Typed asymptotic rate obstruction for bare moving Mobius profiles.

No source values, zeta values, residual norms, or selected applications are
evaluated. The analytic rule depends on the explicitly imported conditional
Soundararajan theorem and the reviewed local-zero proof in the 046 memo.
An independent verifier is supplied separately; this producer imports none.
"""
from copy import deepcopy
from fractions import Fraction as Q
import json
import time

SCHEMA = "floor-residual-global-rate-guard-046-v1"
REFUTED = "REFUTED_UNIFORM_LOG_RATE"
ROUNDING = {"kind": "dyadic_power_floor", "bits_multiplier": 4,
            "scale": "ceil_log2_N", "drift": "round_each_exponential_before_signed_sum",
            "product": "multiply_rounded_children_exactly"}


class Unsupported(ValueError):
    pass


class Meter:
    def __init__(self, cap=1_000_000, seconds=60, max_bits=4096):
        self.cap, self.operations, self.deadline = cap, 0, time.monotonic()+seconds
        self.max_bits = max_bits

    def charge(self, count=1):
        if type(count) is not int or count < 0 or count > self.cap-self.operations:
            raise OverflowError("046 exact-algebra operation cap")
        self.operations += count
        if time.monotonic() > self.deadline:
            raise TimeoutError("046 argument deadline")

    def rational(self, value):
        value = Q(value)
        bits = max(abs(value.numerator).bit_length(), value.denominator.bit_length())
        self.charge(1+bits)
        if bits > self.max_bits:
            raise OverflowError("046 exact rational bit cap")
        return value


def _json(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), allow_nan=False)


def _keys(value, names):
    if type(value) is not dict or set(value) != set(names):
        raise Unsupported("exact request/AST fields required")


def _rat(value, meter):
    if type(value) is not str or not 1 <= len(value) <= 2500:
        raise Unsupported("bounded canonical rational string required")
    try:
        result = Q(value)
    except (ValueError, ZeroDivisionError):
        raise Unsupported("invalid rational") from None
    if str(result) != value:
        raise Unsupported("canonical rational string required")
    return meter.rational(result)


def _parse(request, meter):
    _keys(request, ("recipe", "q", "b", "domain", "rounding", "bound"))
    try:
        size = len(_json(request))
    except (TypeError, ValueError):
        raise Unsupported("finite JSON request required") from None
    if size > 65536:
        raise OverflowError("046 bounded input size")
    meter.charge(1+size//64)
    recipe = request["recipe"]
    _keys(recipe, ("id", "base", "auxiliary"))
    if type(recipe["id"]) is not str or len(recipe["id"]) > 256 or recipe["auxiliary"] is not None:
        raise Unsupported("bounded ordinal label and null auxiliary required")
    spec = recipe["base"]
    _keys(spec, ("kind", "a", "theta", "terms"))
    if spec["kind"] != "drift_mixture":
        raise Unsupported("bare drift_mixture only; tapers and other channels remain OPEN")
    a, theta = _rat(spec["a"], meter), _rat(spec["theta"], meter)
    if a <= 0 or not Q(1, 2) < theta < 1:
        raise Unsupported("requires a>0 and strictly 1/2<theta<1; other theta ranges remain OPEN")
    if type(spec["terms"]) is not list or not 1 <= len(spec["terms"]) <= 8:
        raise Unsupported("one to eight fixed terms required")
    terms, previous, total, Cw, weighted_rates = [], Q(0), Q(0), Q(0), Q(0)
    for term in spec["terms"]:
        _keys(term, ("rate", "weight"))
        rate, weight = _rat(term["rate"], meter), _rat(term["weight"], meter)
        if rate <= previous or weight == 0:
            raise Unsupported("sorted distinct positive rates and nonzero fixed signed weights required")
        previous = rate
        total = meter.rational(total+weight)
        Cw = meter.rational(Cw+abs(weight))
        weighted_rates = meter.rational(weighted_rates+meter.rational(abs(weight)*rate))
        terms.append((rate, weight))
    if total != 1:
        raise Unsupported("unit normalization sum(weights)=1 required")
    q, b = request["q"], _rat(request["b"], meter)
    if type(q) is not int or not 2 <= q <= 4096:
        raise Unsupported("fixed bounded integer q>=2 required")
    margin = meter.rational(q-meter.rational(b*b))
    if margin <= 0:
        raise Unsupported("strict |b|<sqrt(q) required")
    _keys(request["domain"], ("kind", "minimum"))
    if request["domain"]["kind"] not in ("all_integer", "geometric_chain"):
        raise Unsupported("all_integer or specified unbounded geometric_chain domain required")
    minimum = request["domain"]["minimum"]
    if type(minimum) is not int or not 2 <= minimum <= 2**31:
        raise Unsupported("integer domain minimum within schema cap required")
    if _json(request["rounding"]) != _json(ROUNDING):
        raise Unsupported("exact separate-exponential dyadic floor policy required")
    _keys(request["bound"], ("A", "eta"))
    A, eta = _rat(request["bound"]["A"], meter), _rat(request["bound"]["eta"], meter)
    kappa = meter.rational(1-theta)
    gap = meter.rational(eta-kappa)
    if A <= 0 or gap <= 0:
        raise Unsupported("requires finite A>0 and eta>1-theta; equality/slower rates remain OPEN")
    return a, theta, terms, q, b, A, eta, kappa, gap, margin, Cw, weighted_rates


def build_guard(request, meter=None):
    """Generate a scoped rate refutation or UNSUPPORTED; never a norm result."""
    meter = meter or Meter()
    try:
        a, theta, terms, q, b, A, eta, kappa, gap, margin, Cw, weighted_rates = _parse(request, meter)
    except Unsupported as exc:
        return {"schema": SCHEMA, "status": "UNSUPPORTED", "reason": str(exc),
                "advertised_uniform_rate_refuted": False, "unpaid_rate_status": "OPEN",
                "norm_convergence_status": "OPEN", "RH_status": "OPEN"}
    certificate = {
        "schema": SCHEMA, "status": REFUTED, "request": deepcopy(request),
        "advertised_uniform_rate_refuted": True, "norm_convergence_status": "OPEN", "RH_status": "OPEN",
        "RH_proved": False, "RH_refuted": False, "source_values_evaluated": False,
        "norms_evaluated": False, "numerical_lower_constant_claimed": False,
        "explicit_failing_support_claimed": False,
        "source_binding": {
            "source": "actual ordinary Mobius mu; not an arbitrary sign source",
            "basis": "f_n(x)=floor(1/x)/n-floor(1/(n*x)) on 0<x<=1, zero beyond1",
            "coefficients": "c_n(N)=-mu(n)*sum_j w_j*floor_dyadic(n^(-r_j*beta_N)); 2<=n<=N",
            "external_taper_or_auxiliary": False,
        },
        "exact_conditions": {
            "a": str(a), "theta": str(theta), "beta_power": str(kappa),
            "tail_dominance_gap_theta_minus_half": str(meter.rational(theta-Q(1, 2))),
            "rate_gap_eta_minus_beta_power": str(gap),
            "contraction_margin_q_minus_b_squared": str(margin),
            "squared_recurrence_ratio": str(meter.rational(b*b/q)),
            "sum_weights": "1", "sum_abs_weights": str(Cw),
            "sum_abs_weighted_rates": str(weighted_rates),
            "rmin": str(terms[0][0]), "rmax": str(terms[-1][0]),
        },
        "beta_transfer": {
            "level": "L(N)=1+floor(log2 N)", "definition": "ceil(a*L(N)^theta)/L(N)",
            "asymptotic": "beta_N~a*L(N)^(-(1-theta))",
            "child_level_gap_upper_bound": (q-1).bit_length(),
            "child_recomputed": True, "child_beta_ratio": "beta_(qN)/beta_N->1",
            "precision": "4*ceil(log2 N), recomputed at qN",
            "ceiling_relative_error": "O(L^(-theta)); no beta monotonicity assumed",
        },
        "whole_mellin": {
            "finite_source": "A_N(s)=sum_(1<=n<=N) mu(n)*V_N^rounded(n)*n^(-s)",
            "unit": "n=1 cancels identically in A_N(s)-A_N(1)",
            "target": "M e_N(s)=[1-zeta(s)*(A_N(s)-A_N(1))]/s",
            "forcing": "M h_N(s)=[1-b*q^(-s)-zeta(s)*(A_(qN)(s)-A_(qN)(1)-b*q^(-s)*(A_N(s)-A_N(1)))]/s",
            "indicator_and_signed_parent_child_terms_retained": True,
        },
        "RH_false_branch": {
            "off_line_zero": "rho with Re(rho)>1/2 exists if RH is false, by zeta zero symmetry",
            "exact_response": "M h_N(rho)=(1-b*q^(-rho))/rho",
            "Cauchy_lower_bound": "||h_N||^2>=(2*Re(rho)-1)*|1-b*q^(-rho)|^2/|rho|^2>0 for every N",
            "reason_multiplier_nonzero": "|b|*q^(-Re(rho))<1",
            "no_source_tail_or_RH_assumption": True,
        },
        "RH_true_branch": {
            "imported_theorem": {
                "author": "K. Soundararajan", "title": "Partial sums of the Mobius function",
                "primary_source": "https://arxiv.org/pdf/0705.0723", "location": "Theorem1",
                "hypothesis": "RH", "bound": "|M(x)|<=C*sqrt(x)*exp(sqrt(log x)*(loglog x)^14), eventually",
                "imported_not_discovered": True,
            },
            "tail": {
                "exact_formula": "sum_(n>K) mu(n)*n^(-z)=-M(K)*K^(-z)+z*integral_K^infinity M(x)*x^(-z-1)dx",
                "scope": "Re(z)=1/2+r*beta_K, K=N or qN, bounded imaginary part",
                "monotonicity": "y^(-1/2)*(log y)^14 decreases once log y>28",
                "eventual_condition": "rmin*beta_K>=2*(log K)^(-1/2)*(loglog K)^14",
                "why_condition_holds": "theta>1/2, beta_K*log K~constant*(log K)^theta",
                "bound": "O((1+|z|/beta_K)*exp(-rmin*beta_K*log K/2))=o(1)",
                "uniformity": "uniform on a bounded beta_N-scaled frequency window; NOT a global critical-line tail energy bound",
                "series_scope": "shifted source series convergence follows here from the imported RH bound, never assumed on Re(s)=1/2",
            },
            "paid_harmonic": {
                "bound": "|A_N(1)|<=beta_N*sum_j|w_j|r_j+sum_j|w_j|*N^(-r_j*beta_N)/(r_j*beta_N)+Cw*N^(-4)*(1+log N)=O(beta_N)",
                "reason": "zeta(1+kappa)>=1/kappa and absolute harmonic tails; no RH needed",
            },
            "rounding": {
                "coefficient_error": "<=Cw*N^(-4)",
                "local_Dirichlet_error": "<=2*Cw*N^(-7/2) on Re(s)=1/2",
                "harmonic_error": "<=Cw*N^(-4)*(1+log N)",
                "child_rounding_recomputed": True,
            },
            "critical_zero": "choose one known ordinary critical-line zero rho, with any finite multiplicity d>=1",
            "local_zero_expansion": "zeta(rho+z)=C*z^d*(1+O(z)), C!=0",
            "scaled_frequency": "s=rho+i*beta_N*v",
            "boundary_layer": "F_d(v)=1-(i*v)^d*sum_j w_j/(r_j+i*v)^d; F_d(0)=1",
            "full_uniform_limit": "M h_N(rho+i*beta_N*v)->(1-b*q^(-rho))*F_d(v)/rho uniformly for v in any fixed compact interval",
            "nonzero_scale_factor": "|1-b*q^(-rho)|>=1-|b|/sqrt(q)>0",
            "local_energy": "a nonzero fixed v-window and Mellin Plancherel give ||h_N||^2>=c*beta_N eventually, c>0",
            "all_crosses_retained": True, "zero_simplicity_assumed": False,
        },
        "unconditional_lower_bound": {
            "statement": "there exist c>0 and N_star such that ||h_N||^2>=c*beta_N for every integer N>=N_star",
            "argument": "RH true: local boundary layer; RH false: uniform positive zero witness and beta_N->0",
            "constants": "symbolic/non-effective in this certificate; no computed c or N_star",
            "geometric_scope": "therefore the same lower rate holds on every specified unbounded geometric chain",
        },
        "rate_contradiction": {
            "advertised_bound": "||h_N||^2<=A*L(N)^(-eta)",
            "comparison": "A*L^(-eta)/beta_N<=(A/a)*L^(-(eta-(1-theta)))->0",
            "constant_A_over_a": str(meter.rational(A/a)),
            "uniform_domain_refuted": deepcopy(request["domain"]),
            "equality_or_slower_rate": "OPEN; this guard proves no attainability or uniform upper bound",
        },
        "stable_recurrence": {
            "identity": "e_(qN)=b*D_q e_N+h_N, ||D_q||=q^(-1/2)",
            "hypothetical_vanishing_forcing": "would imply e_N->0 on the specified q-chain; all_integer domains contain such chains",
            "role": "valid implication, but not needed for the stronger direct RH-false/true case split",
        },
        "proof_guards": {
            "bare_profile_only": True, "finite_cutoff_paid_locally": True,
            "global_truncation_energy_paid": False, "moment_cancellation_required_for_lower_rate": False,
            "known_zero_and_RH_Mertens_facts_imported": True,
            "RH_not_used_to_prove_an_upper_bound": True,
            "finite_certified_norms_unchanged": True,
            "theta_at_most_half_or_eta_equality_not_refuted": True,
        },
    }
    meter.charge(1+len(_json(certificate))//64)
    return certificate
