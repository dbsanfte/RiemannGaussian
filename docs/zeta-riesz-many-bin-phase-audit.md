# Many cofactor bins: a test of joint phase cancellation

The independent `-79/1000-o(1)` floor remains **open**. This slice tests
whether the newly remaining many-bin population supplies an automatic
orthogonality or parity gain. It does not pay another population or measure
a percentage of the floor gap.

## What the occupancy hypothesis supplies

The current nonzero remainder has

```
56 <= omega(n) < 5 log(N+1)+2,
card(cofactorBins(N,n/largestPrime(n))) > floor(log(N+1)/16),
every prime log-share < 60069/100000.
```

The count/bin restrictions come from `ZetaRieszCoreOwnerPayment`; the
latest owner-share cut comes from `ZetaRieszSharpOwnerPayment`. Occupancy
counts locations; it does not assert that the *weighted* contribution is
spread evenly over them, or supply independent frequencies.

There is an exact phase correlation. For a cofactor with logarithm `b`,
its owner-prime period has centre `v-b`. Throughout that period,

```
exp(-i*y*((v-b+t)+b)) = exp(-i*y*(v+t)).
```

Thus all counts and occupied patterns may retain the same total-log
phase. `recentered_owner_phase` and `literal_owner_phase` prove this without
changing any arithmetic support. `coherent_energy` retains every cross
term. With `m` identical columns, `unit_columns_energy` gives joint energy
equal to `m` times the diagonal energy, not a square-root saving.

## The actual bin-deletion energy

For every squarefree cofactor `a` and every prime `r|a`, prime deletion gives
the exact four-hinge expansion of the original two hinges:

```
R_x(a)-R_L(a)
 = [R_x(a/r)-R_(x-log r)(a/r)]
   -[R_L(a/r)-R_(L-log r)(a/r)].
```

Retain any common complex original weight `w`, including its allocation,
phase and factorial kernel. Each complete deletion expression is still
`w*(R_x(a)-R_L(a))`. Consequently `bin_deletion_energy_exact` proves

```
(1/card B) * sum_(i in B) (1/card P_i) * sum_(r in P_i)
  norm(w * fourHinges_r)^2
 = norm(w * (R_x(a)-R_L(a)))^2,
```

where `B` and `P_i` are the **actual** occupied bins and their prime
incidences. This is not a continuous prime model. Cauchy--Schwarz applied
to unchanged deletion copies has no automatic bin saving. It does not
exclude cancellation after reindexing across *different original labels*.

## Numerical joint-period regression

The optional `scripts/probe_riesz_many_bin_period.py` retains the full
factorial radial amplitude, both reflected hinges, the complete owner
phase period, moving length with an explicit rounding enclosure, and a
uniform bound on the original allocation. It sums six neighbouring count
classes before computing the Gram energy. The largest tests have counts
`129..134` and `257..262`, rather than fixing the count as `N` grows.

All tests keep more than the paid bin ceiling and owner share in
`[0.54,0.56]`. The joint/diagonal energy ratio approaches **6**, while the
cross-count profile correlations approach **1**. Precision-preserving
defect strings are recorded so rounded floating-point ones are not
mistaken for exact equalities.

The full-period residual also need not vanish. The exact model theorem is

```
integral_(-pi/y)^(pi/y) exp(k*t)*cos(y*t) dt
 = -k*(exp(k*pi/y)-exp(-k*pi/y))/(k^2+y^2) < 0,
```

for `k,y>0`. In the off-saddle probe at total log `1.99N`, the limiting
radial tilt is `k=1/398`; the period residual remains nonzero. At `2N` it
shrinks polynomially. These are **continuous log models**, not certified
prime labels. In particular, the essential cofactor population and `1/a`
mass are not bounded by this experiment, and original spent-set membership
is not certified. The probe neither disproves the floor nor supplies an
arithmetic counterexample to it.

Odd-grid subset models can likewise put all active subset parities in the
same sign. `odd_grid_layer_no_cancellation` proves that algebraic fact;
it is not an identity asserted for the actual prime divisor.

## The rate and the useful remaining mechanism

The available bin count is at most `2 log(N+1)+1`. Even a binary discount
for *every* bin is therefore bounded below by `exp(-1)/(N+1)^2`.
`binary_bin_discount_source_tendsto` proves that this discount, multiplied
by the existing positive source envelope `(2u)^N/(N+1)^5`, still diverges
when `u>1/2`. This is an envelope audit, not a lower bound on the signed
carrier. An exponential in the guaranteed logarithmic bin count is only
a power of `N`.

The remaining promising use of the bins is **cross-label arithmetic
correlation**, retaining the whole signed sum before squaring. The
existing `ZetaRieszCofactorPhaseEnergy` already supplies exactly that
inequality, using the actual weighted sharp Möbius prefixes. Its
`phaseEnergy` is not paid at source scale. No new Gram carrier is needed.
The current `ZetaRieszSignedConvolution.joint_periods_eq_bilinear` also
keeps the count, allocation, owner and radial masks inside the weight on
the original product `p*d*b`; it cannot be replaced by a separable weight
without paying that difference.

Prime-factor averaging is a real literature mechanism. Matomäki and
Radziwiłł use Ramaré's identity to extract bilinear structure and prove a
mean-square estimate after averaging over Mellin frequency. Their survey
separates the small-frequency PNT input from the large-frequency prime
polynomial estimate. This does not directly give the required fixed-height
signed floor for our correlated masks. [Authors' ICM survey, pp. 3–5](https://maksym-radziwill.github.io/icm.pdf).

Their later power-saving statement concerns the size of the exceptional
set in short-interval theorems; it is not, by itself, a pointwise bound for
this carrier. [Matomäki–Radziwiłł, *Multiplicative functions in short intervals II*](https://arxiv.org/abs/2007.04290).

## Actual cross-label test after removing early cutoffs

The unit logarithmic null correction now removes every cutoff with
`log(k+1) <= L` exactly, without changing any squarefree count3+ label or
its signed weight. The new17-proof
[cutoff-period audit](riesz-cutoff-period-floor-audit.json) records a direct
lower inequality on the same funded ledger after complete cutoff periods
are joined. The price of the surviving post-hinge terms is still unpaid.

`ZetaRieszManyBinCorrelationAudit.sharp_prime_mul` proves on actual integers

```
sharp(k,p*a) = sharp(k,a) - sharp(floor(k/p),a).
```

Canonical owner extension preserves `a` and all its occupied bins. Primes
in a common quotient cell consequently have identical prefix columns.
The new energy lower bound retains their full signed original moment
`sum_p w(p*a)`; it does not replace phases or mask/funding coefficients by
one. This can occur at an active post-hinge cutoff, so removing the early
coherent prefix does not justify automatic diagonalization.
The lower bound concerns the same selected fibre energy; it is not a
lower bound after other cofactors have been joined. Their signed cross
terms may still cancel it.

The optional actual-integer regression has negative cross-label energy
in5 of9 small-order cases and positive cross-label energy in4. It also
checks `a=210`, owners907 and911, and cutoff5500: both literal prefixes
equal1 and the height54 phases have the same sign. These are count5/test
length examples, **not** the unpaid count56+ physical/many-bin population.
They neither certify a cofinal saving nor refute the floor. The generic
seven-proof [correlation audit](riesz-many-bin-correlation-audit.json)
applies to any cofactor satisfying its stated ownership/quotient conditions.

The next strict quantitative target is a bound on the *actual weighted
off-diagonal Möbius correlations* in `phaseEnergy`, or a direct signed
aggregate with the funding credits. The occupancy condition cannot simply
be substituted for such a bound. All five final floor estimates remain
open, as do the ceiling and any new zero exclusion.

## Stronger rate test for a proposed many-bin L2 saving

`ZetaRieszManyBinRateAudit` strengthens the fixed-discount audit. For any
fixed constants `A,B` and every fixed `u>1/2`, it proves

```
exp(-A log(N+1)^2 - B log(N+1)) (2u)^N -> +infinity.
```

The same limit holds on the original `dyadicMomentOrder` sequence. Even
an inverse power of `N` **per occupied bin** only produces this
superpolynomial, subexponential discount. The theorem uses the actual
`cofactorBins` definition and its existing physical prime-log bound when
specialized to that grid. It audits the positive envelope, not the value
of any signed population.

The new exact energy identity is

```
E = D + C,
D = sum_k sum_n (w(n)*sharp(k,n))^2/k,
C = sum_k sum_n sum_(m != n) w(n)w(m)sharp(k,n)sharp(k,m)/k.
```

All cutoffs are the same active post-hinge cutoffs, and `w` retains the
whole original phase/allocation/funding coefficients. Lean checks the
equivalence `E <= r D <-> C <= -(1-r)D`. No sign of `C` is assumed.
For an L2 strategy starting from a positive amplitude allowance of size
`poly(N)(2u)^N`, an energy-ratio saving must overcome `exp(2N log(2u))`,
up to polynomial factors. At the outer radius Lean proves

```
1/10001 <= log(2*radiusCeiling) <= 1/10000.
```

This rate requirement is specific to pricing that envelope. It does not
rule out a direct one-sided inequality for the actual signed sum, and it
does not assert that its actual diagonal energy has that growth.

The primary literature has useful complete Möbius-Gram estimates:
Ramaré–Zuniga-Alterman prove explicit constant upper bounds for
`sum_(d,e<=X) mu(d)mu(e)/lcm(d,e)^(1+epsilon)`, including `0.4664` for
`epsilon=0`, `X>=10^33`. Those results keep the signed divisor cross terms,
but their constant bounds are not a fixed power saving for our masked,
fixed-height, funded carrier. The paper is **not** imported as a Lean
arithmetic input. [Primary paper, Theorems 1.1–1.2](https://arxiv.org/pdf/2603.25961).

The optional `scripts/probe_riesz_many_bin_rates.py` checks the small
reference Gram diagonalization with exact rationals through cutoff 64,
then evaluates that complete reference form through 100000. Its last
value is approximately 0.440741. It also evaluates envelope rates: even
the optimistic `N^-1` per-bin discount regrows after roughly 5.78 million
orders in the continuous rate model. This crossover is floating and is
not a certified interval. Neither computation evaluates the literal
unpaid count 56+ population or the funding witness.

The next arithmetic test is consequently a quantitative estimate of the
**whole weighted signed off-diagonal sum**, or of complete adverse cutoff
periods directly. A claim of "orthogonality from many bins" without such
an estimate does not supply a source-scale payment. The floor remains
OPEN. [Nine-proof local audit](riesz-many-bin-rate-audit.json).

## Local validation

`ZetaRieszManyBinPhaseAudit` is imported by the ordinary root. Its 20
public proofs are checked with warnings as errors, namespace lint and
transitive axiom audit. [Proof audit](riesz-many-bin-phase-audit.json)
records the completed local checks and source hashes. The optional probe
is outside ordinary builds and CI. No wider publication checks or new
commit are part of this local iteration.
