# Paying the positive five-prime head

[`ZetaRieszFivePositiveHead.lean`](../RiemannGaussian/ZetaRieszFivePositiveHead.lean)
proves a sharper coefficient bound and uses it to pay another actual
population inside the unchanged `coreResponse`. No zero hypothesis,
simplicity assumption, prime-density approximation or new carrier is used.

Write `T=log n`, `P=largestPrime n`, and `d=L-log P`. For a squarefree
five-prime label, in the existing length range `2T<=3L` and `4L<=3T`, the
already proved exact positive coefficient is

```math
\max(0,\operatorname{Re}c_L(n))
=\frac TL\max\left(0,
  \sum_{\substack{q\mid n/P\\q\text{ prime}}}\min(d,\log q)-3d\right).
```

There are four cofactor primes. Bounding the other three clipped logs by
`d` proves `positiveAllowance_le_cofactor_log`. The companion theorem
`positiveAllowance_le_marked_log` includes **any** prime factor, including
the largest:

```math
\max(0,\operatorname{Re}c_L(n))\le\frac TL\log r
\qquad(r\mid n,\ r\text{ prime}).
```

This improves the old factor-three least-prime cap to factor one. The
other exact largest-prime gap restrictions remain available.

More strongly, if two distinct cofactor primes satisfy
`log r+log q<=d`, `positiveAllowance_eq_zero_of_pair` proves that the entire
positive part vanishes. This does **not** assert that the negative
coefficient vanishes. On the original radial slabs, the hypotheses

```math
2M\le T\le2M+2,\qquad
\frac{271}{200}M\le L\le\frac{143}{100}M,\qquad
\log p\le\frac54M\quad(p\mid n)
```

imply that a surviving positive coefficient with a marked prime
`log r<=M/32` has every other prime logarithm greater than `M/16`.
`coefficient_nonpos_of_two_small` proves the contrapositive, including the
fact that neither small prime can be the largest.

## An actual population bound

`small_five_positive_norm_upper` covers every selected positive-coefficient
five-prime label in those slabs having some prime at most `Q`, for
`log Q<=M/32`, `M>=100` and `N<=2M`. It retains the original allocation,
moment order, full complex phase and arbitrary inherited finite support.
Writing `f_N` for the original residual atom, its exact bound is

```math
\left\|\sum_{n\in S}f_N(n)\right\|
\le B_5(1+\log Q)\frac{e^{2M}}{M+1}
    \operatorname{radialEnvelope}(N,M),
\qquad B_5=113246208(\log4)^5e^4.
```

Four large prime legs give three reciprocal-prime sums and one literal
last-prime counting interval. The marked `log r` cancels the problematic
small-prime weight in the remaining Chebyshev sum. This counts the whole
eligible population, not one chosen cofactor fibre.

`eventually_small_five_positive_cost` makes this an arbitrarily small
fraction of the existing supply's radial scale when `Q=N^2`.
`eventually_small_five_positive_log_cost` also allows a **fixed positive**
exponential width `log Q<=delta*N`, chosen according to the desired cost.
These are relative payment estimates; separate source-normalized norm
decay of the head is not claimed.

## One supply, four charges, one signed rest

`eventually_joint_slabs_spending` pays the original narrow balanced triple
band, the small-prime triple head, the small-prime four-prime head, and
this positive five-prime head from **one** actual four-prime supply.
Their fractions are `1/2, 1/8, 1/8, 1/8`, leaving `1/8`.

The theorem `eventually_core_joint_floor` applies this simultaneously
throughout the existing radial union, on the original dyadic schedule,
with `Q=N^2` for the new head. All selections are proved disjoint and lie
in the original core. For the exact residual complement `W`, paid
populations `X,Z,H,F`, and supply `Y`, it proves

```math
u^{N+1}\left[\operatorname{Re}W
 +\sum_{E\in\{X,Z,H,F\}}\max\left(\operatorname{Re}\sum_{n\in E}f_N(n),0\right)
 +\frac18\operatorname{Re}\sum_{n\in Y}f_N(n)\right]
\le\operatorname{Re}\left(u^{N+1}\operatorname{coreResponse}\right).
```

The stronger `eventually_core_exponential_floor` chooses a common fixed
`delta>0` and replaces all three polynomial heads by
`Q=floor(exp(delta*N))`. This threshold eventually exceeds every fixed
polynomial threshold, by the existing
`ZetaRieszFourPrimeHead.eventually_polynomial_le_exponential`. The common
width is chosen afresh to pay all charges; it is not claimed to equal the
width in the earlier three/four-prime ledger.

The terminal **`eventually_core_full_exponential_floor`** also pays every
eligible label missed by that radial selection. It selects the original
balanced triple band and every squarefree core label with a prime below
`Q` that has count three, count four, or count five with positive Riesz
coefficient. `exists_exponential_head_missed_bound` proves the missed
labels lie in the already controlled radial or dominant-prime sectors,
after zero residual atoms are removed. Its source-normalized cost is

```math
\varepsilon_N=r^N C+
2\,\operatorname{zetaMoebiusLogMajorantMass}(1+1/262144)
e^{-N/1000000},\qquad 0\le r<1,\quad C\ge0.
```

The full inequality has the same favorable real parts and one-eighth
supply, subtracts this error, and takes the exact complement of the
**entire** selected head. The existing
`tendsto_exponential_head_allowance` proves the displayed error tends to
zero on the original dyadic schedule. Thus radial endpoints and the
dominant-prime boundary are paid, not left as extra hypotheses.
`remaining_full_positive_head_prime_log_gt` identifies the surviving
positive five-prime sector: **every prime now has `log p>delta*N`**.
Negative five-prime coefficients are not removed by this theorem.

The actual supply has positive real sum. The old one-quarter leftover is
**replaced** by this one-eighth leftover; the two ledgers cannot be added.
The broader angular/certificate payments also require their own disjoint
accounting before combination.

Other triple shapes with all primes above the common threshold,
unselected five-prime signs and sizes, higher prime counts, and all other
unselected terms stay in `W`. No sign bound for that complete rest follows
here. The independent whole-joint-sum floor
`-79/1000-o(1)` and the multiple-zero ceiling `3/2+o(1)` both remain open.

## Diagnostic for choosing the next signed estimate

The optional [`probe_riesz_signed_counts.py`](../scripts/probe_riesz_signed_counts.py)
evaluates all subset signs of the continuous Riesz coefficient before
splitting its final sign. The stored
[probe output](riesz-signed-count-probe.json) uses `lambda=.693`, minimum
share `.001`, largest share at most `.601`, and four scrambled Sobol
replicates with `2^16` samples each. It includes the exact `1/k!` symmetry
factor and the uniform simplex density `(k-1)!`.

| Count | Positive coefficient mass | Negative coefficient mass |
| ---: | ---: | ---: |
| 3 | 0.3542 | 0 |
| 4 | 0.1047 | 0.0146 |
| 5 | 0.0043 | 0.2150 |
| 6 | 0.0817 | 0.0777 |
| 7 | 0.0860 | 0.0499 |
| 8 | 0.0582 | 0.0617 |

These are **uncertified continuum diagnostics**, not prime-sum bounds or
source-scale credits. The original allocation, complex phase and radial
kernel are not transported, deleted shares and higher counts are unpaid,
and replicate variation is not a rigorous error interval. In particular,
the table proves no no-go theorem and supplies no additional credit.
It does show why extending the narrow triple band should not be treated
as a plan to pay the entire remaining carrier from the currently checked
five-prime credit: the wider signed populations are substantial. Future
payments need the same exact disjoint accounting and full phase retained.
