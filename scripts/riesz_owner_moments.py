"""Local moments of the literal conditional binomial band (optional numerics).

The Pearson equation for the two beta endpoint densities supplies moments
on an arbitrary subinterval. Integration by parts then gives the moments
of the whole binomial band, retaining both exterior boundary terms. This
is used to integrate the varying signed Riesz polynomial BEFORE norms.
"""
from functools import lru_cache

from flint import arb, ctx, fmpz


@lru_cache(maxsize=64)
def log_choose(n, k, precision):
    with ctx.workprec(precision):
        return arb(fmpz.bin_uiui(n, k)).log()


def integer_beta_cdf(x, a, b):
    """Positive binomial recurrence, at the caller's full working precision."""
    n = a+b-1
    forward = x < arb(a)/n
    k = a if forward else a-1
    term = (log_choose(n, k, ctx.prec)+k*x.log()+(n-k)*(1-x).log()).exp()
    odds = x/(1-x) if forward else (1-x)/x
    total, steps = arb(0), 0
    tolerance = arb(2)**(-ctx.prec+48)
    while True:
        total += term
        if (forward and k == n) or (not forward and k == 0):
            break
        ratio = odds*(n-k)/(k+1) if forward else odds*k/(n-k+1)
        if steps % 16 == 0:
            upper = ratio.upper()
            assert 0 <= upper < 1
            remainder = abs(term).upper()*upper/(1-upper)
            if remainder < tolerance:
                total += arb(0, remainder.upper())
                break
        term *= ratio
        k += 1 if forward else -1
        steps += 1
    return total if forward else 1-total


def beta_moments(a, b, center, scale, count):
    """Normalized beta-density moments in y=(x-center)/scale, -1<=y<=1."""
    left, right = center-scale, center+scale
    assert 0 < left < right < 1 and a > 0 and b > 0
    cdf_left = integer_beta_cdf(left, a, b)
    cdf_right = integer_beta_cdf(right, a, b)
    assert cdf_left.is_finite() and cdf_right.is_finite()
    norm = arb(a+b).lgamma()-arb(a).lgamma()-arb(b).lgamma()
    q_left = (a*left.log()+b*(1-left).log()+norm).exp()
    q_right = (a*right.log()+b*(1-right).log()+norm).exp()
    moments = [cdf_right-cdf_left]
    for k in range(count-1):
        previous = moments[k-1] if k else arb(0)
        numerator = (k*center*(1-center)/scale*previous
                     +(k*(1-2*center)+a-(a+b)*center)*moments[k]
                     -q_right+(-1)**k*q_left)
        moments.append(numerator/((k+a+b)*scale))
    return moments, (cdf_left, cdf_right)


def band_moments(M, lo, hi, center, scale, count):
    """Integral of y^k sum_{j=lo}^hi binom(M,j)x^j(1-x)^(M-j) dx."""
    assert 1 <= lo <= hi < M
    low, low_cdf = beta_moments(lo, M-lo+1, center, scale, count+1)
    high, high_cdf = beta_moments(hi+1, M-hi, center, scale, count+1)
    at_left, at_right = low_cdf[0]-high_cdf[0], low_cdf[1]-high_cdf[1]
    moments = [scale/(k+1)*(at_right-(-1)**(k+1)*at_left-low[k+1]+high[k+1])
               for k in range(count)]
    assert moments[0] > 0, 'Insufficient precision for positive band mass'
    return moments
