# What integers occur in the retained signed sum?

This is a structural and numerical audit, not a signed-sum estimate. The
literal lower-threshold packet minus short overflow and its complementary
carrier remain unbounded. No Lean theorem or public frontier changes here.

## The order index is not a summed integer

The stress tests use moment orders `N=2^16,2^17,2^18,2^19`. Their factorization
is a choice of experimental scale, not a restriction that carrier labels are
powers of two. The labels satisfy `1.95N<log n<=2.03N`. At `N=262144` this
allows integers with 222004--231111 decimal digits; at `N=524288` the range
is 444007--462222 digits.

Integer rounding of the factorial endpoints depends on `N mod 40` and
`N mod 100`. A dyadic-only probe can therefore contain lattice effects as
well as continuous oscillations. No experiment here proves that such effects
explain the previous residuals.

## Arithmetic shape of the surviving interior

The label is a squarefree composite with 3--55 distinct prime factors.
Every prime is strictly above `N^2` and below the original physical cutoff.
The independently localized interior also has

\[
n^{1/2}<P^+(n)<n^{3/5},\qquad
n^{1/200}<P^-(n)<n^{3/50}.
\]

Thus there is exactly one prime larger than `sqrt(n)`. The complementary
factor is a squarefree composite below `sqrt(n)`. These are rough integers
(no small prime divisors), with one large prime, rather than smooth numbers
or prime powers. For `k=omega(n)`, the divisor count is exactly `2^k` and
`mu(n)=(-1)^k`; this does **not** determine the Riesz coefficient's sign.

There is also a central divisor gap. Writing `n=P*a` with `P>sqrt(n)`,
every divisor either divides `a` or equals `P` times a divisor of `a`.
Consequently no divisor lies strictly between `a=n/P` and `P`. The two
divisor blocks remain internally structured; the small-subproduct cutoff
inside the cofactor is what the Riesz response still has to resolve.

The original finite factorial selection favors owner share about
`0.525..0.575` and least share about `0.01..0.04`. Those are concentration
ranges, not extra exact log-share masks. The complete lower-threshold-minus-
short-overflow ledger retains its broader support and all its finite tails.

The integer count thresholds 14 and 56 arise from constraints such as
`x_owner+(k-1)x_min<=1` and the quantitative factorial tails. They are not
special residue classes or claims about divisibility by 14 or 56.

## Actual prime products with a common large and small factor

[`probe_riesz_label_anatomy.py`](../scripts/probe_riesz_label_anatomy.py)
constructs five examples at `N=512`, with `u=10001/20000`. All have 445
decimal digits, the same 245-digit largest prime, and least prime
`784629761`. Every prime has an exact modular certificate recorded in
[`riesz-label-anatomy-probe.json`](riesz-label-anatomy-probe.json), together
with the complete decimal factorizations. These are certificates checked
by integer arithmetic, not new Lean primality theorems.

Let `c_L(n)=-log(n)*R_L(n)/L` be the repository's squarefree composite
coefficient. Approximate normalized prime logs and numerical coefficients
are:

| Prime count | Prime-log shares | `c_L(n)/log(n)` |
| --- | --- | ---: |
| 3 | .55, .43, .02 | +.02937569 |
| 4 | .55, .26, .17, .02 | +.02937569 |
| 5 | .55, .20, .12, .11, .02 | -.01594918 |
| 6 | .55, .17, .12, .08, .06, .02 | -.04532487 |
| 7 | .55, .13, .105, .08, .065, .05, .02 | -.06483422 |

Their total logarithms differ by less than `7e-10`. At the illustrative
height `y=60`, all phases are approximately `-.996459-.084076i`, with
phase differences below `4e-8`. Their canonical largest/least factorial
rectangle weights are all approximately `.73061219`. The positive common
radial kernel consequently does not explain the sign change: the middle
factorization changes the Riesz hinge response. The three- and four-prime
examples have negative real coefficient-times-phase; the other three have
positive real coefficient-times-phase.

All reported transcendental values use 600-digit arithmetic; the factorial
probabilities use floating point. These are deliberately chosen products of
Proth-form primes, not a representative distribution. Only the listed
squarefree, count, core, physical, owner/least and nondominant tests are
evaluated in the script; it is not an exhaustive evaluation of a Lean
Finset or of the entire retained carrier. In particular it gives no relative
density of the favorable and unfavorable classes and no joint floor.

For a certificate `p=k*2^m+1`, `k` odd and `k<2^m`, the script verifies
`a^((p-1)/2)=-1 (mod p)`. For every prime divisor `q` of `p`, `a^k` then
has exact order `2^m` modulo `q`, so `q>=2^m+1>sqrt(p)`. This excludes
composite `p`. The report records `k,m,a` for every factor.

## Why the middle factors matter

The coefficient retains all divisor subsets:

\[
R_L(n)=\sum_{d\mid n}\mu(d)(L-\log d)_+.
\]

For a new prime `p` coprime to `a`, the two divisor classes give exactly
`R_L(pa)=R_L(a)-R_(L-log p)(a)`. In the current large-prime geometry this
also reduces to `R_L(n)=-R_(L-log P)(n/P)`, where `P=P^+(n)`. The numerical
audit verifies this latter identity at high precision for every example.
The actual cutoff response therefore depends on which *subproducts* of the
remaining primes lie below `exp(L-log P)`. Prime count alone loses that
information.

The examples illustrate a useful grouping to investigate: keep the large
and small factors fixed, and compare middle cofactors of almost the same
size across prime counts. That keeps the phase and principal factorial
weight aligned while permitting opposite divisor responses. An estimate
for the weighted populations in those groups is still required.

## Shared signed subset geometry

Write `n=P*r*b`, with largest prime `P`, least prime `r`, and middle
cofactor `b`. Put `T=log n`, `D=L-log P` and `h=log r`. In the saturated
large-prime geometry just used, least-prime deletion gives the exact identity

\[
c_L(n)=\frac{T}{L}\int_{D-h}^{D} M_b(t)\,dt,
\qquad M_b(t)=\sum_{\substack{d\mid b\\\log d\le t}}\mu(d).
\]

Indeed, `R_D(rb)=R_D(b)-R_(D-h)(b)`; the derivative of each hinge away
from its breakpoint is its cutoff indicator. Equivalently the integral is
`sum_(d|b) mu(d)*min(h,max(D-log d,0))`. Values of the indicator at the
finitely many breakpoints do not affect the integral. The new numerical
profile in the optional script checks this finite identity directly, with
the unit divisor retained. It is not an additional Lean theorem.

For the five constructed examples, this normalized window is approximately
`0.11085836 < t/T < 0.13085905`. The signed count there is particularly
simple:

| Total prime count | Even-minus-odd middle-subset count in the window |
| --- | --- |
| 3 | `1` throughout |
| 4 | `1` throughout |
| 5 | `0`, then `-1` after the middle prime of share about `.12` enters |
| 6 | `-1`, then `-2` after the same share enters |
| 7 | Starts at `-3`; the `.065+.05` pair raises it to `-2` |

The last example also has nearly coincident `.13` singleton and `.08+.05`
pair thresholds, with opposite signs. Their normalized clipped contributions
are approximately `-.00085914619331` and `+.00085914619269`. All divisor
terms of one label share **exactly** the same outer complex phase. However,
these near coincidences were built into the chosen log-share targets; their
frequency in the actual weighted prime population has not been established.
Distinct prime subproducts cannot coincide exactly, by unique factorization.

There is a classical topological description of this arithmetic structure.
The prime subsets of `b` with total logarithm at most `t` form a threshold
(quota) simplicial complex. Its alternating face count, including the empty
face, is precisely `M_b(t)`; equivalently this is minus its reduced Euler
characteristic, with the usual augmented empty-complex convention. Thus the
Riesz coefficient is an integrated signed Euler characteristic over a moving
window. This is an interpretation of the exact formula, not a novelty claim.

Pakianathan and Winfree's [threshold-complex theorem](https://arxiv.org/html/1104.4324)
describes a least-weight-vertex matching that leaves faces in a narrow quota
shell (Theorem 2.3). Their log-prime construction and
[Björner's number-theoretic complexes](https://arxiv.org/abs/1101.5704)
also relate Euler characteristics to Möbius sums. The elementary pairing
underneath this description is already present in our least-prime recurrence;
giving it a topological name supplies no arithmetic saving by itself.

A concrete loss of information is visible in
`ZetaRieszSperner.abs_signedDivisorWindow_le`: it replaces the signed sum by
the sum of absolute values and then bounds the number of window subsets by
Sperner's theorem. A potentially useful new estimate would instead control
the **weighted even-minus-odd imbalance** of the remaining shell subsets,
jointly across the actual prime-count classes and with the literal phase and
allocation masks. The profiles above suggest what to measure, but neither a
topological restatement nor the selected near-cancelling examples proves that
estimate. The signed lower-threshold-minus-short-overflow target remains open.

The follow-up [weighted profile investigation](zeta-riesz-signed-cutoff-profile.md)
adds a checked four-prime coefficient sign and probes the difference between
within-label and cross-count cancellation. Its arithmetic floor remains open.

## Bias in the older sparse actual-prime regression

The five labels in `riesz-least-order-boundary-probe.json` use Mersenne
primes `2^e-1` from exponents `17,19,31,61,89,107,127,521`. Every surviving
label shares the five factors with exponents `521,127,107,89,61`; only the
small remainder changes. Only prime counts six and seven occur.

Their logarithms satisfy

\[
\log n=\Bigl(\sum e\Bigr)\log2+
\sum\log(1-2^{-e}).
\]

At `y=60`, the phase-angle difference from the corresponding power of two
is below `.000573` radians in every example. The regression is therefore
highly structured and nearly lies on one logarithmic lattice. It remains
valid as an identity check, but cannot support a general phase-distribution
or cancellation claim. The new Proth examples are also selected, and are
not a replacement for an unbiased density study.

Run the optional audit with

```sh
.lake/plot-venv/bin/python scripts/probe_riesz_label_anatomy.py \
  --output /tmp/riesz-label-anatomy.json
```

Keep it outside ordinary CI. No exhaustive numerical certification workflow
is needed to reproduce this investigation.
