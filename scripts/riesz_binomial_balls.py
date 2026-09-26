"""Positive-term binomial tails for the optional Riesz ball diagnostic.

An exact integer binomial coefficient starts a monotone tail recurrence.
The omitted positive tail is enclosed by its decreasing geometric ratio.
All operations use Arb; branch selection only chooses which exact tail to
sum. This is a numerical helper, not a Lean theorem or prime-sum estimate.
"""
from functools import lru_cache
from flint import arb, ctx, fmpz


@lru_cache(maxsize=128)
def _log_choose(n, k, precision):
    # precision is part of the cache key, not a replacement for workprec.
    with ctx.workprec(precision):
        return arb(fmpz.bin_uiui(n, k)).log()


def binomial_tail(q, n, j):
    """Enclose P[Bin(n,q)>=j], including the truncation remainder."""
    if j <= 0:
        return arb(1)
    if j > n:
        return arb(0)
    if q <= 0:
        return arb(0)
    if q >= 1:
        return arb(1)
    assert 0 < q and q < 1
    with ctx.workprec(224):
        # Even when q straddles j/n, either chosen tail is valid. The
        # decreasing-ratio condition is checked before bounding its rest.
        forward = q < arb(j)/n
        k = j if forward else j-1
        term = (_log_choose(n, k, ctx.prec) + k*q.log()
                + (n-k)*(1-q).log()).exp()
        total = arb(0)
        odds = q/(1-q) if forward else (1-q)/q
        tolerance = arb(2)**(-200)
        steps = 0
        while True:
            total += term
            if (forward and k == n) or (not forward and k == 0):
                break
            ratio = odds*(n-k)/(k+1) if forward else odds*k/(n-k+1)
            # Remaining successive ratios only decrease as this tail is
            # traversed. This enclosure is therefore for the entire rest.
            if steps % 16 == 0:
                upper = ratio.upper()
                assert 0 <= upper and upper < 1
                remainder = abs(term).upper()*upper/(1-upper)
                if remainder < tolerance:
                    total += arb(0, remainder.upper())
                    break
            term *= ratio
            k += 1 if forward else -1
            steps += 1
        answer = total if forward else 1-total
        assert answer.is_finite()
        return answer
