# Through the signed Riesz obstruction: feasibility and literature audit

**Subsequent strict test:** the [quantitative Type-II go/no-go audit](zeta-riesz-typeii-go-no-go.md)
now formalizes the sufficient reduction and records **no-go with the current inputs**.
Its checked narrow-window theorem and full unsaturated correction supersede
the exploratory implementation recommendations below.

Research audit, 21 September 2026. This note is a recommendation, not a new
Lean theorem or a zero exclusion. It distinguishes existing checked results
from mathematical deductions and proposed estimates. The current uncommitted
symmetric-identity work is included in the audit and left intact.

**Recommendation:** attack a one-sided, phase-twisted sieve discrepancy on a
smaller radius interval, retaining the actual Riesz cutoff and all relevant
prime counts. Use the existing truncated Selberg identity and complete
squarefree cofactor estimates. Do not start another unrestricted Euler-series
completion, a positive allowance optimization, or a general-purpose sieve
formalization. The literature identifies the missing bilinear input; it does
not supply that input for this carrier.

## 1. What the repo actually gives us

Write `N=N_j`, `L=L_N`, `t=log n`, `s0=3/2+iy`, and let `S_N` be the actual
`nondominantBand` with the original count schedule. The target is

\[
R_j=\frac{u^{N+1}}{N!}\sum_{n\in S_N}
 (1-\theta_N(n))c_L(n)n^{-3/2-iy}t^N,
\qquad
c_L(n)=-\frac{t}{L}\mathcal R_L(n),
\quad
\mathcal R_L(n)=\sum_{d\mid n}\mu(d)(L-\log d)_+.
\]

The exact source and the strict eventual inequality `Re R_j < -3/40`
are in
[ZetaRieszNondominantCarrier](../RiemannGaussian/ZetaRieszNondominantCarrier.lean).
They require the stated **simple exposed zero** and
`1/2<u<exp(-11/16)`. An independent cofinal floor at `-3/40` suffices.
Neither simplicity nor exposure may be silently removed.

The support restrictions and the following bounds are already useful:

| Checked ingredient | What it buys | What it does not buy |
| --- | --- | --- |
| [Joint cofactor cancellation](../RiemannGaussian/ZetaRieszJointCofactor.lean) | The unpaid wing plus its complete composite companion is bounded by `C_y(N+1)^2 exp(-N/64)` | Separate smallness of either summand |
| [Allocation and mask transfer](zeta-riesz-joint-allocation.md) | Exact multiplier `1-theta`, all old off-mask corrections paid | Small unassigned mass on balanced triples |
| [Dominant-prime deletion](zeta-riesz-dominant-sector.md) | Every surviving nonzero label has `log p < (13/20) log n` | Cancellation between surviving labels |
| [Allowance obstruction](../RiemannGaussian/ZetaRieszAllowanceGrowth.lean) | `B-(3/4)B4` tends to infinity, with a balanced-triple lower bound of order `(2u)^N/(N+1)^4` | A contradiction for the signed sum |
| [Symmetric completion audit](zeta-riesz-symmetric-completion-audit.md) | Newton, Euler and differentiated identities; the allocation-removal error on the actual balanced triple band is geometric | Transfer of its other masks to a complete series |
| [Truncated Selberg identity](../RiemannGaussian/ZetaRieszTruncatedSymmetry.lean) | Exact signed overlap with all divisor incidences | An independent inequality for that overlap |

The obstruction boxes have coefficient `t(t-L)/L`, not the reflected-linear
three-prime coefficient `t(2L-t)/L`. Their pair-cutoff correction is on the
surviving support. In addition, the signed full generating function at `z=1`
is `1/zeta(s)`, whereas the analytic unsigned squarefree completion is
`zeta(s)/zeta(2s)`. Confusing these would remove the hypothetical pole by
assumption.

## 2. The most useful structural diagnosis

On squarefree composites the existing reflection identity gives

\[
\mathcal R_L(n)=\mu(n)\mathcal R_{t-L}(n).
\]

For `D>=0`, the finite hinge also has the exact integral form

\[
\mathcal R_D(n)=\int_1^{e^D}
 \left(\sum_{d\mid n,\ d\le v}\mu(d)\right)\frac{dv}{v}.
\]

Thus the reflected coefficient couples `mu(n)` to an integral of precisely
the kind of truncated Möbius divisor sum appearing in the asymptotic sieve.

At the central scale `t ~ 2N`, put `lambda=-log u`. Then

\[
e^L=n^{\lambda+o(1)},\qquad
e^{t-L}=n^{1-\lambda+o(1)},\qquad
\frac{11}{16}\le\lambda<\log2.
\]

Thus the reflected sieve cutoff is approximately `n^0.307` to `n^0.3125`.
If every prime factor exceeds that cutoff, the reflected divisor sum is
just `t-L`. Since four such factors cannot fit into `n` at this scale,
the surviving rough labels have exactly three primes after the earlier
lower-count deletions. Any fourth or later prime-count class must have a
prime below the reflected cutoff. Cancellation with those classes therefore
crosses a specific small-prime boundary. It is not merely cancellation
between two lists having opposite parity.

These scale deductions concern the central range, not every point of the
current wider window. Section 4 gives a restricted interval on which a
narrower window is feasible.

The exact existing overlap is

\[
-t\mathcal R_L(n)=
\sum_{abv=n}\mu(a)\Lambda(b)
 T_L(\log a,\log b),
\]

where squarefreeness makes the factors pairwise coprime and `b` a prime
whenever its summand is nonzero. Here

\[
T_L(x,y)=L_+-(L-x)_+-(L-y)_++(L-x-y)_+.
\]

It vanishes for `ab<=exp L`. Consequently its residual cofactor satisfies
`v<n/exp L`. This simultaneously retains the Möbius sign, a small cofactor,
the prime factor, the physical boundary and the product phase. It is the
closest existing interface to a signed asymptotic-sieve estimate. Taking
`abs(mu(a))` or bounding the prime-count classes separately destroys the
information needed here.

### Why selecting two primes is a useful test, but not an automatic solution

The old allocation captures a single prime carrying roughly two thirds of
the logarithm. Balanced triples have no such prime, but a pair carries that
fraction. This suggests marking two primes and completing the cofactor.

There is a precise diagnostic. Let `p,q` be distinct primes, coprime to a
squarefree `a>1`. Suppose

\[
\log a\le L-\max(\log p,\log q),\qquad
T=L-\log(pq)\ge0.
\]

Twice applying the repository's prime-insertion identity, and using the
saturated divisor identity `R_H(a)=Lambda(a)` for `H>=log a`, gives

\[
\mathcal R_L(pqa)=\mathcal R_T(a)-\Lambda(a),\qquad
c_L(pqa)=\frac{\log(pqa)}{L}
 [\Lambda(a)-\mathcal R_T(a)].
\]

This is a pencil-and-paper deduction from the existing insertion and
saturation identities, **not a new compiled lemma in this audit**. The
`a=1` endpoint requires its own correction and is excluded above.
The hypotheses hold with a margin in the balanced obstruction boxes.

It pinpoints the task: bound the **prime-versus-truncated-divisor discrepancy
jointly**, with the outer pair and its phase. Bounding the completed
`R_T` response alone leaves the prime response `Lambda(a)`. That is exactly
where the hypothetical-zero signal can reappear. Also, all three pair
choices qualify in a balanced triple: the old proof that at most one prime
owns a majority allocation does not extend to pairs. A unique-counting or
exact incidence correction is mandatory and can itself affect completion.

I therefore would not launch a two-prime completion package merely because
its cofactor sizes look favorable. Its acceptance test must include this
prime discrepancy and the incidence correction.

## 3. What numerical strength is actually necessary?

For calibration, define the **actual**, masked complex coefficients

\[
a_N(n)=\mathbf1_{S_N}(n)(1-\theta_N(n))c_L(n)n^{-iy},
\qquad A_N(x)=\sum_{n\le x}a_N(n).
\]

A sufficient, stronger-than-necessary arithmetic target is

\[
\operatorname{Re}A_N(x)\ge -C_{u,y}N^A x^{1-\delta}
\tag{*}
\]

for a cofinal set of the actual orders, all relevant endpoints, and a fixed
`0<delta<1`. This is **one-sided**; no bound for `abs(A_N)` is required.
The constant may depend on the fixed height and radius, but not on order.

Indeed `x^(-3/2)(log x)^N` is decreasing throughout the retained window:
its derivative has sign `N-(3/2)log x`, which is negative there. Abel
summation, including the endpoints, turns (*) into a lower bound with cost

\[
C_{u,y}N^A u\left(1+\frac{3/2}{1/2+\delta}\right)
\left(\frac{u}{1/2+\delta}\right)^N.
\]

For this calculation extend the finite-support cumulative sum constantly
beyond its final endpoint; the same lower bound continues to hold there.
The displayed cost is a convenient upper estimate for the resulting
positive derivative-kernel integral. This deduction is not formalized here.

Thus **any fixed positive power saving** would close some nonempty radius
interval adjacent to `1/2`; it need not cover the whole current range.
For the whole range it suffices that

\[
\delta>e^{-11/16}-1/2\approx0.002831578.
\]

For example `delta=1/1000` and `u<=5001/10000` give the exact geometric
ratio `1667/1670<1`. This is a target specification, not an available bound.
A direct cofinal floor for the smoothed sum could be easier than (*), and
should take priority if available. There is no reason to insist on an
absolute norm, all orders, uniformity in unbounded height, or a full power
saving if the needed signed floor can be proved more directly.

By contrast, fixed fractional savings, powers of `1/log x`, and generic
PNT errors `exp(-o(log x))` cannot overcome the known exponential positive
allowance for fixed `u>1/2`. This rate mismatch persists however small that
fixed excess is.

## 4. A concrete restricted test using existing machinery

Use initially

\[
\frac12<u\le\frac{5001}{10000},\qquad
\frac{39}{20}N<\log n\le\frac{41}{20}N.
\]

The general theorem
[`exists_uniform_deviation_bound`](../RiemannGaussian/ZetaArithmeticDeviationBounds.lean)
already handles arbitrary finite selections and coefficients dominated by
the original arithmetic majorant. This includes the unassigned multiplier,
once its existing bounds are inserted. It requires just

\[
\log(2U)<I(a),\quad\log(2U)<I(b),\qquad
I(x)=x/2-1-\log(x/2).
\]

For `U=5001/10000`, `a=39/20`, `b=41/20`, these strict scalar tests reduce
to `Ua<exp(-1/40)` and `Ub<exp(1/40)`. They have elementary rational
certificates:

\[
Ua<(159/160)^4<e^{-1/40},\qquad
Ub<1+1/40+(1/40)^2/2<e^{1/40}.
\]

The two rational gaps are respectively `125829/3276800000` and
`43/400000`; they were checked with exact rational arithmetic during this
audit. The exponential inequalities follow from the elementary exponential
bounds. The specialization to the actual carrier remains to be written and
compiled; it is not a new claimed bounding milestone.

Throughout this narrower window, the asymptotic physical-cutoff exponent
`L/log n` lies strictly between `2/3` and `3/4`. The complementary exponent
lies between `1/4` and `1/3`. Floors and the `log N` correction in `L` must
still be transported with their eventual margins. This puts the entire
test window, rather than just its saddle, into the geometry described in
section 2.

This also matches a notable threshold in Friedlander–Iwaniec: their
asymptotic-sieve distribution level is beyond `x^(2/3)`, with truncated
Möbius coefficients reaching `x/D`. The resemblance is a **scale match**,
not a proof that our cutoffs provide their distribution or bilinear
hypotheses. The match is worth exploiting in a targeted estimate; it does
not justify importing their conclusion.

## 5. Literature: tools, exact gaps, and priority

The earlier [prime-tail literature audit](prime-tail-literature-audit-2026-09-11.md)
already examined general Type II, pretentious, Fourier, spectral and sieve
routes. This pass focuses on the now-explicit Riesz hinge and also checks
recent short-interval work.

**Friedlander–Iwaniec, _Asymptotic sieve for primes_, Theorem 1 and
hypotheses (B), (B1)–(B3).** Their bilinear input retains `mu(mn)` coupled to
a short Möbius divisor sum, and their proof explains why that input breaks
the parity limitation of divisor-distribution estimates alone. This is the
closest structural match to the reflected carrier. Their theorem assumes
the crucial estimate; it does not prove it for our phase, masks and moving
cutoff. Its published logarithmic error scale also cannot be substituted
for the power-scale calibration above.
[Primary paper](https://arxiv.org/pdf/math/9811186).

**Ramaré, _On Bombieri's asymptotic sieve_, Section 2 and Theorems 1–3.**
The Diamond–Steinig generalization of Selberg symmetry provides quantitative
prime/semiprime combinations with explicit dependence on the derivative
order. That dependence matters for our growing factorial moments. Use its
coupled identities and error accounting as a guide to the
`Lambda(a)-R_T(a)` estimate. Its distribution assumptions, positivity
requirements and parameter inequalities still need matching; fixed-order
asymptotics cannot simply be used with order proportional to `N`.
[Author's paper](https://ramare-olivier.github.io/Maths/V12BombieriSieve.pdf).

**Granville–Koukoulopoulos–Maynard, _Sieve weights and their smoothings_,
equations (1.5)–(1.9), Theorems 1.3 and 1.6.** Our normalized hinge is
exactly their weight with `f(t)=(1-t)_+`. Their finite differences retain
inserted prime logarithms, and their moment results diagnose contributions
from different factorization patterns. They are useful for boundary and
incidence costs, not an off-the-shelf signed floor. The basic averaging
error costs a power of the divisor cutoff; in the reflected central range
the square fits below the integer scale, but the fourth power does not.
Moreover their sixth-moment main-term coefficient for the hinge has larger
logarithmic growth in their asymptotic regime. Blindly raising the moment
order is therefore a poor default.
[Published paper](https://smf.emath.fr/system/files/filepdf/ens_ann-sc_54_1089-1177.pdf).

**Ford–Maynard, _On the theory of prime-producing sieves_, equations
(I), (II) and the optimality results.** This is a useful sufficiency test:
it uses all available Type I and Type II ranges together. But its Type II
hypothesis quantifies over arbitrary divisor-bounded coefficients, while
our completed unsigned squarefree response is much more specific. Prove
only the input needed for the literal signed carrier before investing in
the general framework. A claimed application must identify both sequences,
all coefficient quantifiers, endpoint uniformity and its final error rate.
[Primary paper](https://arxiv.org/html/2407.14368v1).

**Menon, _Improved bounds for multiplicative functions in almost all short
intervals_ (July 2026 preprint), Theorems 1.2–1.3.** The smooth-number case
is especially relevant to our dominant-prime deletion, and its modified
Ramaré decomposition retains a useful factorization structure. Nevertheless
the conclusion is averaged over intervals, with logarithmic error terms,
for bounded multiplicative functions. Our masked hinge is not such a
function. This paper supplies neither the necessary pointwise transfer nor
the required order-scale saving.
[Primary preprint](https://arxiv.org/html/2607.15574v1).

**Bellotti, _Explicit bounds for the Riemann zeta function and a new zero
free region_, Theorem 1.1 and Section 8.** This remains the more established
route if the deliverable becomes an enlarged zero-free region. The repo has
already proved fixed-degree Dirichlet-block savings; the outstanding work
includes uniform degree-dependent moment costs and all-scale analytic
transport. Those are quantitative implementation problems with a published
model. They do not directly bound our fixed-height cofinal Riesz tail.
[Primary paper, pinned version](https://arxiv.org/html/2306.10680v1).

A search also returned Ramaré's May 2026 _The weighted large sieve through
Parseval_. It was withdrawn in June for a miscalculation; it is excluded
from the proposed inputs.
[Withdrawal record](https://arxiv.org/abs/2605.29470).

## 6. The next task and its stopping rules

1. Specialize the already generic tail estimate to the restricted window
   above, with the **actual** residual coefficients. Record this as
   localization, not a signed-cancellation breakthrough.
2. Attack one coupled signed overlap estimate, starting with balanced outer
   prime factors and retaining every squarefree cofactor count. The target
   must include `Lambda-R_T`, product phase, cutoff, allocation and unique
   integer counting. Use the Selberg/asymptotic-sieve identities to seek a
   one-sided gain for this literal weight, not estimates for arbitrary
   independent bilinear coefficients.
3. Before expanding a Lean package, calculate the resulting order exponent
   and all completion costs. A useful result either bounds an actual
   component with its coupled partners and a paid complement, or directly
   supplies the cofinal `-3/40` floor. A bound only for the completed
   truncated-divisor piece fails this test.
4. Keep the remaining support in the same ledger. Paying the balanced
   triple obstruction together with some higher-count terms is genuine
   component progress; it is not a floor for the whole remaining carrier.

Do not continue the experiment if its only saving is logarithmic, if the
prime term is merely renamed, or if a completion/ownership boundary is
left at source scale. The product phase `(ab)^(-iy)=a^(-iy)b^(-iy)` is
separable; generic bilinear cancellation does not follow from oscillation
alone. Likewise, the repo's Vinogradov block bounds require the height to
grow with block scale, whereas this contradiction fixes `y` and sends
`N` to infinity. Their hypotheses must not be extrapolated across that
change of limits.

**Assessment:** this is the best-matched direct research target, not a
known route guaranteed to close. I found no published estimate that
discharges its independent signed inequality. If the targeted estimate
does not acquire a sufficient rate, finishing the uniform
Vinogradov–Korobov transport is the more predictable route to additional
proved zero-free coverage. It is a separate advance; it will not by itself
establish the current cofinal floor or RH.
