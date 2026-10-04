# Exact algebra before the signed-pair detector

The new [Lean module](../RiemannGaussian/ZetaRieszPairPrefixConvolution.lean)
proves a complete **finite** convolution identity for the current symmetric
factorial-prefix coefficient. Both prime phases, every factorial index and
the single whole repeated-prime diagonal are retained. The independent
cofinal upper bound `Re prefixPairDefect <=399/5000+o(1)` is still open.

The literature search found the classical prime-zeta product identities in
[Mathar, *Series of Reciprocal Powers of k-almost Primes*](https://arxiv.org/abs/0803.0900).
They give complete prime-product algebra, not the required signed bound for
our factorial prefix and moving literal masks. The identity below is derived
from finite factorial convolution and exact binomial prefixes; no new sieve
or phase estimate is assumed.

## Checked complete finite identity

Let `A` be any finite set of genuine primes, `M=N+1`, `K=floor(13N/32)`,
`L!=0`, and

$$
P_k=\sum_{p\in A}\frac{(\log p)^k}{k!}p^{-s},\qquad
F(x)=\sum_{k=0}^{K}\binom{M}{k}x^k(1-x)^{M-k}.
$$

The exact current coefficient is

$$
Q_N(x,z)=(x+z)\left(1-\frac{x+z}{L}\right)
-\frac{x+z}{L}\left[(L-x)F\left(\frac z{x+z}\right)
+(L-z)F\left(\frac x{x+z}\right)\right].
$$

Define the central convolution and whole square diagonal by

$$
C_t=\sum_{k=K+1}^{t-K-1}P_kP_{t-k},\qquad
D_N=\sum_{p\in A}Q_N(\log p,\log p)
\frac{(\log(p^2))^N}{N!}(p^2)^{-s}.
$$

Then `unordered_prefix_eq_central_sub_diagonal` proves exactly

$$
\boxed{
\sum_{\substack{n=pq\\p,q\in A,\ p<q}}
Q_N(\log p,\log q)\frac{(\log n)^N}{N!}n^{-s}
=\frac M2C_M-\frac{M(M+1)}{2L}C_{M+1}
-\frac M L\sum_{k=1}^{K}kP_kP_{M+1-k}-\frac12D_N.
}
$$

The order-zero terms cancel exactly between the full convolution and the
two prefixes. This holds for every phase; it is not a statistical feature
of selected primes. The remaining lower-order factor `k*P_k` is the logged
prime moment of order `k-1`. Keep it joined with the central sums: no
independent one-sided bound for this combination is proved here.

`prefix_mass_kernel` and `logged_prefix_kernel` prove the exact binomial
prefix/product-kernel bridge. `canonical_prefix_pair` verifies the owner
coordinates, including squares. `joined_convolution_cancel_endpoints` works
for any complex moment array with `2K<M`. No concentration approximation,
share indicator or low-order deletion enters any identity.

`mixed_convolution_cancel_endpoints` polarizes the identity without moving
factorial orders between primes. `prefix_atom_eq_central_logged` then proves
the same cancellation on each individual literal pair, including both
swapped factorial incidences. Any common radial, period or physical mask
can multiply this equality before summation. **Endpoint cancellation on
the current masked sum needs no prime completion.** The surviving kernels
still carry those correlated masks; they cannot be replaced by products of
separate complete prime moments without an additional boundary theorem.

The first quantitative application is now
[`ZetaRieszPairLowOrderPayment`](zeta-riesz-pair-low-order-payment.md): on
the literal pairs with largest-prime log at most the moving length, logged
orders through `floor(17N/64)+1` have an independent source-scaled cost
`8e^2(N+1)e^(-N/1250)`. Higher orders and all pairs above that cutoff remain
signed and unpaid; the `399/5000` target is unchanged.

This is **not** an identification of the complete convolution with the
literal `prefixPairDefect`. That target retains its original period support,
moving length, radial flag correction and Selberg subtraction. Completing
those populations still needs a proved boundary payment. The existing
global owner-mask payment is preserved, not spent again.

## Detector preflight

Run the optional [algebraic preflight](../scripts/probe_riesz_pair_algebra.py)
before statistical discovery:

```bash
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python scripts/probe_riesz_pair_algebra.py --scan-survivors
../.venv/bin/python scripts/check_riesz_pair_algebra.py
```

It records four unjoined components: the full order-`M` convolution, the full
order-`M+1` convolution, the unlogged prefix and the shifted logged prefix.
Every term retains incidence orientation, assigned factorial indices, total
order, phase identity and support signature. Coefficients are exact rational
pairs `constant + inverseL/L`. Whole legs may commute; derivative orders may
not move between primes. Different support signatures remain unmatched.

Only after exact collection does it evaluate the three surviving complex
component responses. The literal owner-mask difference, radial flag
correction and Selberg subtraction stay separate. Matched components share
the same physical product phase. No norm or positive allowance enters the
algebraic cancellation.

The original Riesz, allocated-head and unallocated-correction pieces also
remain individually recorded with their distinct mask signatures. They are
not freely identified with the symmetric prefix. The globally paid
owner-mask difference is a separate term. Original owner factorial indices
and full representative prime-leg rows are saved rather than inferred from
an already-joined charge.

With `--scan-survivors`, the surviving expression is handed to the existing
coupled phase detector only after exact collection and literal replay pass.
The cached handoff scans four order/seed groups over 129 dyadic offsets at
height 100, retaining every coupling mode. No reference permutations are
rerun and this regression supplies no new discovery signal. The independent
checker compares the overlapping joined curves with the frozen prior scan,
so algebraic rearrangement cannot silently change the arithmetic target.

The run checks 204 exact cases: `N=0..96` and five larger native orders, with
distinct and repeated primes tested separately. At `N=256`, 212 of the 517
distinct factorial monomials cancel exactly, including all four zero-order
endpoints. This counts terms, **not** source-scale savings. Negative controls
detect missing endpoints, wrong leg/order swaps, differing masks, and missing
or doubled diagonal subtraction.

The replay covers all 50 cached boxes and 48,256 actual sampled pair
incidences at `N=256,640,1536`. Height 100 is solely a regression case already
covered by known zero-free regions. Moving length and literal complete-period
masks remain unchanged; no unsampled population is completed. The largest
floating coefficient replay discrepancy is about `2.14e-11`. These samples
are below the global payment's `N>=65536` threshold. Their common positive
kernel normalization is not the source scale.

The [independent checker](../scripts/check_riesz_pair_algebra.py) imports no
producer code. It verifies a closed rational coefficient table, repeats 50
actual-prime coefficient calculations using 85-digit arithmetic and checks
every order in 200 factorial rows by independent binomial recurrence. The
maximum floating row-mass discrepancy is about `1.18e-15`. A separate 18-case
high-precision complete finite-prime regression retains both phases and the
whole diagonal.

The strict leaf build and namespace lint pass. The optional
[axiom audit](../scripts/CheckRieszPairPrefixConvolution.lean) checks all 49
theorems including generated proof declarations: only `propext`,
`Classical.choice` and `Quot.sound` occur. There are 15 public theorems.
Artifacts stay under `.lake/riesz-pair-algebra/`, outside ordinary CI. No
root registration, broader gates, commit or push is part of this local slice.

The next arithmetic target is the surviving signed central/logged
combination under the literal masks. A separate boundary bridge is required
only if those masked kernels are replaced by complete prime moments.
Exact cancellation improves
bookkeeping; it does not prove the `0.0798` upper bound, a zero exclusion or RH.
