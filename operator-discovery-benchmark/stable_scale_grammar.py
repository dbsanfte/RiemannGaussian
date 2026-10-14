"""Rational signed dilation polynomials, without a contraction restriction.

Discovery may keep unsupported polynomials. The exact Schur recursion is a
certificate of an operator property, never a certificate of cancellation.
"""
from fractions import Fraction as Q
from math import isqrt
import flint


def real(x):
    x = Q(x)
    return flint.arb(x.numerator) / x.denominator


def polynomial(encoded):
    if not isinstance(encoded, (tuple, list)) or not encoded:
        raise ValueError("A nonempty rational polynomial is required")
    p = [Q(x) for x in encoded]
    if p[0] != 1:
        raise ValueError("The constant coefficient must equal one")
    while len(p) > 1 and not p[-1]:
        p.pop()
    return p


def scale_rows(base, encoded):
    if type(base) is not int or base < 2:
        raise ValueError("An integer dilation base >=2 is required")
    p = polynomial(encoded)
    return [[base**k, str(-c)] for k, c in enumerate(p) if k and c]


def multiply(left, right):
    left, right = polynomial(left), polynomial(right)
    result = [Q(0)] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            result[i+j] += a*b
    return polynomial(result)


def outer_radii(base):
    # Strictly above 1/sqrt(base), without a floating point square root.
    denominator = 4096
    numerator = isqrt(denominator**2 // base) + 1
    critical_upper = Q(numerator, denominator)
    return [critical_upper * q for q in (Q(5,4), Q(9,8), Q(17,16), Q(65,64))]


def schur_certificate(encoded, radius):
    p = polynomial(encoded)
    radius = Q(radius)
    if radius <= 0:
        raise ValueError("The certificate radius must be positive")
    scaled = [c*radius**k for k,c in enumerate(p)]
    steps, margin = [], Q(1)
    while len(scaled) > 1:
        leading = scaled[-1]
        if abs(leading) >= 1:
            return {"certified": False, "radius": str(radius), "steps": steps,
                    "reason": "Schur stage does not have strict |leading|<constant",
                    "failed_leading_coefficient": str(leading)}
        denominator = 1-leading*leading
        reduced = [(scaled[k]-leading*scaled[-1-k])/denominator
                   for k in range(len(scaled)-1)]
        assert reduced[0] == 1
        steps.append({"polynomial": [str(c) for c in scaled],
                      "reflection_coefficient": str(leading),
                      "reduced": [str(c) for c in reduced]})
        margin *= 1-abs(leading)
        scaled = reduced
    return {"certified": True, "radius": str(radius), "steps": steps,
            "uniform_multiplier_lower_bound": str(margin),
            "scope": "Every |z|<=radius, including the boundary"}


def operator_certificate(base, encoded):
    p = polynomial(encoded)
    rows = scale_rows(base,p)
    attempts = [schur_certificate(p,r) for r in outer_radii(base)]
    successful = [a for a in attempts if a["certified"]]
    L = sum((abs(c)/base**k for k,c in enumerate(p)),Q(0))
    triangle = sum((real(abs(c))/real(base**k).sqrt()
                    for k,c in enumerate(p) if k),flint.arb(0))
    answer = {"base":base,"polynomial":[str(c) for c in p],"atoms":rows,
              "lipschitz_constant":str(L),"triangle_critical_cost_ball":triangle.str(35),
              "triangle_certificate_available":bool(triangle < 1),
              "schur_attempts":attempts,
              "inverse_prefix_length":64,
              "all_height_critical_multiplier_certified":bool(successful),
              "ordinary_zeta_bridge":"F(b^(-s))/(s*zeta(s)) plus a term holomorphic for Re(s)>0",
              "uniform_signed_arithmetic_estimate_proved":False}
    if successful:
        def cost(a):
            return inverse_bound(base,p,a,Q(1,2),answer["inverse_prefix_length"])
        best = successful[0]
        for trial in successful[1:]:
            if cost(trial) < cost(best):
                best = trial
        answer["selected_schur_certificate"] = best
        answer["outside_triangle_domain_certified"] = not answer["triangle_certificate_available"]
        inverse = cost(best)
        answer["critical_weight_inverse_norm_upper_ball"] = inverse.str(35)
    else:
        answer["status"] = "retained_without_available_all_height_certificate"
    return answer


def inverse_coefficients(encoded, count):
    p = polynomial(encoded)
    if type(count) is not int or count < 1:
        raise ValueError("A positive integer coefficient count is required")
    result = [Q(1)]
    for n in range(1,count):
        result.append(-sum((p[j]*result[n-j] for j in range(1,min(n,len(p)-1)+1)),Q(0)))
    return result


def inverse_bound(base, encoded, schur, theta, count=64):
    p = polynomial(encoded)
    if len(p) == 1:
        return real(1)
    radius = real(Q(schur["radius"]))
    delta = real(Q(schur["uniform_multiplier_lower_bound"]))
    weight = real(base)**real(-Q(theta))
    ratio = weight/radius
    if not ratio < 1:
        raise ValueError("The contour must exceed the requested weight")
    coefficients = inverse_coefficients(p,count)
    explicit = sum((real(abs(d))*weight**k for k,d in enumerate(coefficients)),flint.arb(0))
    return explicit + ratio**count/(delta*(1-ratio))


def transfer_certificate(cert, order, beta, constant):
    if type(order) is not int or order < 2 or order % 2:
        raise ValueError("An even integer moment order is required")
    theta, C = Q(beta)/(order+1), Q(constant)
    if C < 0:
        raise ValueError("A moment constant cannot be negative")
    answer = {"order":order,"beta":str(Q(beta)),"pointwise_exponent":str(theta),
              "premise":"For every dyadic X>=1, integral_X^(2X) |F(S_b) M_tilde(t)|^q dt <= C X^beta",
              "uniform_premise_proved":False,
              "historical_priority_is_acceptance_gate":False,
              "RH_proved":False}
    if not cert["all_height_critical_multiplier_certified"] or not Q(1,2) <= theta <= 1:
        answer["inverse_transfer_certified"] = False
        return answer
    chosen = cert["selected_schur_certificate"]
    inverse = inverse_bound(cert["base"],cert["polynomial"],chosen,theta,cert["inverse_prefix_length"])
    L = real(Q(cert["lipschitz_constant"]))
    residual_constant = (2**(order+2)*L*real(C))**(real(Q(1,order+1)))
    small_and_large = (residual_constant+L+abs(residual_constant-L))/2
    full_constant = inverse*small_and_large
    answer.update({"inverse_transfer_certified":True,
                   "inverse_norm_upper_ball":inverse.str(35),
                   "residual_pointwise_constant_ball":residual_constant.str(35),
                   "original_M_pointwise_constant_upper_ball":full_constant.str(35),
                   "conclusion":"The stated uniform premise implies |M_tilde(t)|<=B t^theta at every t>=1 and excludes ordinary zeta zeros Re(s)>theta"})
    return answer
