# Quarter-gap skew reserve: the old allocation removes its source-scale mass

This test starts from `7a659cba53dbbf5f9d19b2d18b3790dfcabaa805` and uses
the requested radius ceiling $U=10001/20000$. **The literal unassigned
$N/4$ skew box tends to zero at source scale. It cannot supply a fixed
positive reserve.** This is an independent arithmetic estimate, without
an exposed-zero hypothesis, prime completion, or a replacement of the
composite cofactor by a prime series.

This conclusion concerns the concrete narrow box. It does not rule out
the wider $N/5$ variant, estimate the full ownership correction, or prove
a restricted zero exclusion. The original `LocalizedTypeIIBound` and the
public RH frontier are unchanged.

## Exact incidence and factorial identity

Use the existing dyadic schedule $N=N_t$, count threshold $K=K_t$,
length $L=L_N$, intermediate prime set $A_N$, and original allocation
$\theta_N(n)=\operatorname{boundedShare}(A_N,N,n)$. The integer support is
the actual `tripleBand`, including the nondominant and count masks and
$1.95N<\log n\le2.05N$.

Write $n=pqr$ with $p>q>r$ prime and squarefree, and mark $q$. The
`secondIncidences` set retains $q\in A_N$ and exactly two reflected-large
primes $p,q$, using $\log p,\log q\ge\log n-L$, with the remaining prime
strictly below that threshold. All coprimality follows from the actual
squarefree label; the second incidence is unique. No averaging over the
three possible pair incidences takes place.

`second_neg_riesz` proves $-\mathcal R_L(n)=\log r$. For
$K_a(s,m)=(\log m)^a m^{-s}/a!$, `log_kernel_convolution` proves

$$
\log r\,K_k(s,pr)
 =\sum_{j=0}^k(k-j+1)K_j(s,p)K_{k-j+1}(s,r).
$$

The exact order selection is

$$
\ell=N+1-j-h,\quad j+h\in I_N,\quad
25(h+1)\le N,\quad j-\ell\ge N/4,
\qquad I_N=\{k:13N<40k\le27N\}.
$$

Thus $j+\ell+h+1=N+2$. `skewAtom_eq_factorials` identifies the literal
selected atom as

$$
(1-\theta_N(n))\frac{N+1}{L}
 \sum_{j,h\ \mathrm{selected}}(h+1)
 K_j(s,p)K_\ell(s,q)K_{h+1}(s,r),\qquad s=3/2+iy.
$$

`second_composite_convolution` identifies these with the original
`compositeAtom` row, and `second_mem_nonowner_row` places the incidence in
the exact nonowner partition `correction_eq_nonowner_rows` of
`ownerCompletionCorrection`. The remaining completion/allocation/off-mask
term in that partition is displayed explicitly and is not bounded here.
These identities are bookkeeping infrastructure; the quantitative result
below is the new estimate.

## Why the literal box is small

Put $x=\log(qr)/\log n$ and $c=\log r/\log(qr)$. Let

$$
b_{M,k}(x)=\binom Mk x^k(1-x)^{M-k},\qquad
w_N(x,c)=\sum_{j,h\ \mathrm{selected}}
 b_{N+1,j}(1-x)b_{N+1-j,h}(c).
$$

The narrow box forces $j\ge121N/200$. The old allocation already assigns
the largest-prime incidence for cofactor orders in `unpaidOrders`, whose
upper endpoint is $13N/32$. These are different allocations of the same
literal coefficient, so their overlapping tails must be bounded jointly.
It is not enough to assert a hard prime-log cutoff from the order box.

The proofs retain the complete binomial tails. A common rational tilt
$41/40$ gives the product bound

$$
\bigl(1+x/40\bigr)\bigl(41/40-x/40\bigr)
 \le(81/80)^2,
$$

and Lean proves the exact logarithmic enclosure

$$
2\log(81/80)-\frac{809}{800}\log(41/40)\le-\frac1{8100}.
$$

The other old allocation tail uses the proved surviving bound
$x\ge7/20$. Combining both tails gives, on every nonzero supported atom,

$$
0\le(1-\theta_N(n))w_N(x,c)\le3e^{-N/8100}.
$$

This is `literal_missing_skew_bound`, valid from dyadic index $t\ge32$.
It keeps the original allocation and order correlations together instead
of bounding them by two unrelated worst cases.

## Independent source-scale estimate

Let $S_N(y)$ denote `skewResponse`, the finite sum of the literal atoms
above. Define the existing summable arithmetic majorant mass
$M(\sigma)=\operatorname{zetaMoebiusLogMajorantMass}(\sigma)$ and

$$
\sigma=1+\frac1{262144},\qquad
d=\frac{131071}{262144},\qquad
r_* = \frac{U}{d}e^{-1/8100}<1.
$$

The strict last inequality is proved in `skewRate_bounds`, using rational
inequalities in Lean. `skewResponse_bound` proves, for $t\ge32$, every
real height $y$ and every $0\le u\le U$,

$$
\left\lVert u^{N_t+1}S_{N_t}(y)\right\rVert
 \le 3U\,r_*^{N_t}M(\sigma).
$$

The full complex phase is retained in the object being bounded. The
norm is used only after the allocation/order product has supplied a
saving stronger than the source growth. The estimate is uniform in
height, so `tendsto_skewResponse` allows an arbitrary sequence $y_t$.
`not_eventually_norm_skewResponse_ge` rules out any eventual positive
constant lower bound on its norm, and hence a reserve of either sign.
The prefactor is not numerically evaluated and no effective starting
order for a requested tolerance is claimed.

## Where a weight-one numerical source can remain

Nonowner rows of the original complete correction have weight **one**,
not automatically $1-\theta_N(n)$. For the same finite skew box, define
$S_N^{\rm raw}$ before the allocation split, and $S_N^{\rm alloc}$ with
weight $\theta_N(n)$. Lean proves exactly

$$
S_N^{\rm raw}=S_N^{\rm alloc}+S_N,
\qquad
u^{N_t+1}(S_{N_t}^{\rm raw}-S_{N_t}^{\rm alloc})\longrightarrow0.
$$

These are `rawSkewResponse_eq` and `tendsto_raw_sub_allocated`. They do
not assert decay of either raw or allocated sum separately. If the raw
sum has a nonzero source limit, the allocated sum has the same limit;
it cannot be removed as a source-scale error. Thus a numerical coefficient
around 0.0084 before the allocation split does not certify a new 0.0084
reserve for the actual unassigned carrier. The numerical experiment itself
has not been reproduced or certified by this pass. Nor does this asymptotic
bound disprove those reported finite-order values: its rate is close to
one and its majorant prefactor is unevaluated. The theorem does not identify
which allocation convention was used in that experiment.

**Stop condition:** the concrete quarter-gap box supplies no independent
extra margin after the old allocation is retained. No further completion
of $pr$ or either large-prime leg is attempted. The full correction is
still open. The $N/5$ alternative has a weaker forced largest-prime order
and is not covered by this obstruction; an estimate for that different
box would require its own allocation audit and literal signed bound.

## Checked sources

- [Joint binomial tails and exact geometric rate](../RiemannGaussian/ZetaRieszSkewAllocation.lean)
- [Actual reflected incidence and order masks](../RiemannGaussian/ZetaRieszSkewIncidence.lean)
- [Exact factorial expansion and correction partition](../RiemannGaussian/ZetaRieszSkewFactorial.lean)
- [Uniform literal bound and allocation obstruction](../RiemannGaussian/ZetaRieszSkewCarrier.lean)
