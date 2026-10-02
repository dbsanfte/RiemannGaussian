# Running investigation: semiprime factor location

Started: 2026-10-01. Last updated: 2026-10-02.
Scope: side investigation; independent of the active RH proof campaign.
Repository reference when this note was written:
`ec0473dfab685561c2fdca7f08ff449684bcca07`.

## Publication registration (2026-10-02)

The ten `Semiprime*` proof modules are now imported by the ordinary Lean
library and checked by its build, declaration lint and axiom audit. The
numerical factorisation probes and benchmarks remain optional and separate
from the RH campaign. Historical entries below describe their earlier local
validation and import status; this registration supersedes statements that
the published proof modules are outside the umbrella or ordinary CI. It
supplies no new generic factoring exponent or RH estimate.

## Current conclusion

We now have a cheap classical modular encoding of the unknown factor sum:
for `N=p*q`, `S=p+q` and `gcd(a,N)=1`, `a^(N+1)=a^S (mod N)`.
A sparse residue-colour decoder searches this encoding without a zeta
coefficient grid. Adaptive interval growth and prime-power residue masks
give a measured speed advantage over the installed GNU `factor` 8.32 on
fresh balanced semiprimes with the public promise `q/p<=2`.
The saved implementation and complete 108-input replay are linked in the
dated modular-signal entry below. At 79–96 input bits that replay was
approximately 3.4–6.8 times faster than this baseline.

This is a practical result in a specified regime, not a new asymptotic
factoring theorem or a claim to beat the best classical software.
The collision search remains approximately `N^(1/4)` in size, with
additional collision work possible for small multiplicative orders.
Broader factor ratios reversed the earlier prototype's advantage.
Tuned quadratic-sieve and number-field-sieve implementations have not
been benchmarked.

Earlier numerical zeta extraction remains useful evidence about exact
support filters: the local-support/Euler-filter pass reduced medians from
0.125 s to 0.0197 s at 323, and from 1.661 s to 0.0653 s at 2021.
These small-input extractors did not beat conventional factorisation.

The scaling audit below still rules out an anticipated large-input
crossover for the present fixed-cutoff, fixed-local-window parameter
strategy: its grid grows at least linearly in the numerical product
magnitude, hence exponentially in input bit length. Improving the
arithmetic cost per sample or these fixed filters does not remove this
dependence.

The October 2 investigation adds an experimental weighted collision search
at the one-fifth target scale, with exact order certificates and batched
GCD/vector operations. Its saved replay improves our own baseline by about
10% at nominal 64 and 80 bits, but fixed-base low-order failures remain.
It does not prove a new unconditional exponent.

An exact sparse Frobenius identity also exposes `p+q` through a truncated
polynomial or one binomial residue. Cheap extraction remains unresolved.
Independent prime-prefix tables do improve large-batch throughput: a
fresh 1,024-input, 32-bit replay took about 11.0 microseconds per input,
including cache construction, versus 44.1 for our prime-power decoder.
That is a standard shared-precomputation regime, not a single-input
one-sixth factoring result. Source and replay data are saved below.

The latest single-input investigation implements an order-separation pass
with `~O(N^(1/6))` charged work and an explicit coverage condition. It uses
`N-1` to make the hidden local orders coprime before a batched order search.
Adding it before our own weighted prototype gives total-corpus speedups of
about 1.1–1.9 times at nominal 64 bits and 1.8–2.3 times at nominal 80 bits
in two fresh replays. These comparisons are against our Python prototype.
The pass fails explicitly on long remaining periods; it is not a generic
one-sixth algorithm.

Quadratic Jacobi colour supplies another exact order separator using
`N-Jacobi(D,N)`. An exact common phase rotation reduces its geometric
evaluation from three scalar convolutions to two, with approximately 2%
runtime savings in the larger tested inputs. Both ideas have checked Lean
algebraic lemmas and exact finite regressions. Colour solved the five
safe-prime controls that defeated the scalar pass, but adding it to the
hybrid increased total runtime in the fresh 72-input corpus. Three new
controls, including 64- and 80-bit inputs, defeat all 16 tested colours:
all four `p±1,q±1` rough periods are too long. The dated entry below records
the successful extraction, the phase-tilt derivation and this sharper gap.

The subsequent long-period investigation gets past two of those controls
with a degree-six Dickson map, including a remaining period about 95 times
larger than the old linear cover. Exact trace folding, multiplicative
finite differences and monic remainder trees supply public-input recovery
without a quadratic grid. Classical ECM supplies another bounded pass that
solves all three controls on its first public curve. On 48 fresh inputs,
the Dickson pass adds five hits over the same-colour linear pass but costs
more time; one curve succeeds on 44/48. Staged target evaluation improves
the curve pass's total runtime by 1.67–1.93 times over full-cover evaluation.
These are partial algorithms and comparisons within our prototype, not
a generic exponent theorem or a speed claim against tuned ECM software.

The complex-correction follow-up adds two more public-input covers. A phase
rotation before scalar projection recovers two of four saved Dickson
failures; exponentially spaced order aliases recover a third. Their points
are generated by repeated group powering, without writing enormous integer
exponents. The larger four-rough control still defeats all tested phase
and small-base orbit covers. Lean also proves that applying the RH-style
perpendicular null correction to our coherent collision detector erases
the factor-bearing amplitude entirely. This distinguishes useful rotation
from an exact cancellation which destroys the observable.

The user-confirmed terminal target is now a **guaranteed bound on every
run**: factor every semiprime in `~O(N^(1/6))` bit operations, where `N`
is the numerical input, including all input-specific construction. It is
not an expected-time target. This theorem is **not proved**. A bounded-work
attempt, a coverage hypothesis, and a finite successful corpus do not
establish it. The checked Lean files currently certify signal algebra and
finite witnesses, not universal coverage or an implementation cost model.

The latest row audit proves an exact shared-prefix cancellation and a
root-preserving paired product/reciprocal-trace identity. Raw signed row
cancellation can erase an original factor hit; the root-preserving version
retains the coupled weighted centre. Sharing those centres saved about 6.7%
of centre evaluations on the fresh 80-bit cohort, with no exponent change.
The dated row-structure entry records the proofs and complete replay.

The Cartesian follow-up computes the exact root-preserving product of a
4,096-by-4,096 **constant-centre model** from 8,192 residues without visiting
the individual pairs. It is about 10 times faster than explicit pair
multiplication in the tested 79–80-bit inputs. This is a bulk-detector
benchmark, not a factoring speedup: the literal rounded square-root centres
are different. Lean now proves the mixed-curvature formula and a lower
bound on the integer correction width needed to flatten them. The dated
Cartesian entry below records both the working batch kernel and that gap.

The immediate open problem is processing the exact centre-coupled collision
rows implicitly while preserving their factor hits. The next batching
experiment must retain the integer square-root correction and charge all
input-specific construction. A universal theorem will additionally need
separating-hit coverage, proper-factor recovery and a bit-operation bound.
These experiments do not establish independence of prime gaps and factors,
or impossibility of other zeta-based algorithms.

## Mathematical observables and existing Lean work

Throughout the factor-reconstruction identities, let `N = p*q` for distinct
primes `p < q`, and define

$$
\eta=\frac{\log q-\log p}{2},
\qquad p=\sqrt N\,e^{-\eta},
\qquad q=\sqrt N\,e^\eta.
$$

The local scratch file is
`.lake/SemiprimeImbalanceScratch.lean`, in namespace
`RiemannGaussian.SemiprimeImbalanceScratch`. It is outside ordinary builds
and is not a portable, tracked library artifact. Its existing declarations
include:

| Observable or audit | Scratch theorem |
| --- | --- |
| Reconstruction from imbalance | `small_factor_log`, `small_factor_eq` |
| Noisy imbalance gives a factor interval | `factor_interval_of_imbalance_error` |
| Midpoint Riesz response equals `log p` | `riesz_midpoint_eq_small_log` |
| Noisy Riesz measurement gives a factor interval | `factor_interval_of_riesz_error` |
| Total-log phase depends only on the product | `total_phase_product` |
| Factor-sensitive pair spectrum equals `2*cos(2*t*eta)` | `pairSpectrum_semiprime` |
| Nonaliased noisy phase gives a factor interval | `factor_interval_of_phase_measurement` |
| Cosine sensitivity is quadratic near equal factors | `phase_defect_quadratic_bounds` |
| Positive product-Gaussian resolution requirement | `productGaussian_resolution_requirement` |
| Low-sensitivity estimator obstruction at 33 and 35 | `low_sensitivity_two_semiprime_obstruction` |

These declarations were inspected, not recompiled during this side
investigation. Accurate measurement is an explicit premise in the
reconstruction statements; an efficient evaluator is not supplied by them.

Relevant tracked building blocks:

- [ZetaPrimeQuadraticArithmetic.lean](../RiemannGaussian/ZetaPrimeQuadraticArithmetic.lean):
  `zetaPrimePairArithmetic` is the Dirichlet convolution
  `vonMangoldt * vonMangoldt`, and
  `LSeriesHasSum_zetaPrimePairArithmetic` identifies its convergent series.
- [SuzukiLogarithmicConvolution.lean](../RiemannGaussian/SuzukiLogarithmicConvolution.lean):
  `vonMangoldt_logWeight_add_self_convolution` and
  `sum_moebius_log_square_eq_vonMangoldt_log_add_pair` retain the pair
  coefficient in exact arithmetic identities.
- [GaussianMellinVertical.lean](../RiemannGaussian/GaussianMellinVertical.lean):
  `integral_gaussianMellin_vertical` evaluates the full complex Gaussian
  Mellin integral while retaining its phase.

The scratch comments also record earlier finite-spectrum probes:
a precomputed 225-prime universe and all 25,200 distinct prime-pair
products showed improved localization only when the positive product
filter became extremely narrow. That experiment already knew every
prime pair, so it was not a blind factoring algorithm. A separate
4,000-semiprime phase-feature regression gave mean log-factor error
0.12538505 versus 0.12537949 for its prior alone. These are historical
scratch diagnostics, not newly rerun results.

## 2026-10-01: neighboring primes and factor correlation

Write the nearest surrounding primes as

$$
r_-=N-d_-,\qquad r_+=N+d_+,\qquad g=r_+-r_-=d_-+d_+.
$$

Their distances describe the local prime gap around the product. They
do not directly identify a divisor of the product.

Numerical protocol:

- Sample 36,000 distinct-prime semiprimes with both factors greater than
  100: 18,000 from each product band
  `[2^19,2^20)` and `[2^21,2^22)`.
- Seed: `20261001`. Predict `eta`.
- Control for product size using eight logarithmic bins in each band,
  and for residue class using `N mod 210`.
- Assign complete surrounding prime gaps to the same split using a
  deterministic hash of the lower neighboring prime. The split contained
  21,606 training, 7,201 validation and 7,193 test observations.
- Select ridge/shallow boosting models using validation only.
- Test gap sizes/asymmetry, neighboring Legendre symbols, their combinations,
  and features formed by division/multiplication with the neighbors.

The improvement statistic is
`100*(baseline_MSE-feature_MSE)/baseline_MSE`;
negative values mean slightly worse held-out prediction.

| Feature family | Test MSE improvement |
| --- | ---: |
| Neighboring-gap features | -0.0021% |
| Neighboring Legendre-symbol features | -0.0314% |
| Gap and character features together | -0.0361% |
| Direct ratio/operation features | -0.0731% |

A 6,500-input follow-up also searched for primes surrounding
`N*r_-` and `N*r_+`. The combined model improved test MSE by
-0.1728%, with approximate gap-clustered 95% interval
[-0.525%, +0.179%].

Decision: no useful extra predictive signal was established by these
feature families and models. This is a finite statistical result, not a
proof that every correlation is absent.

## 2026-10-01: successive multiplication and division

The cross operations have exact algebraic identities:

$$
Nr_-=(N-g)r_+ + d_+g,
\qquad
Nr_+=(N+g)r_- + d_-g.
$$

Consequently the remainders are respectively
`(d_+*g) mod r_+` and `(d_-*g) mod r_-`.
If these products are smaller than the corresponding moduli, and
`gcd(N,d_-)=gcd(N,d_+)=1`, their gcds with `N` reduce to
`gcd(N,g)`. The apparent factor information is then the prime-gap
width's common factor with `N`.

Example: `N=119=7*17` lies between 113 and 127. Its gap width is 14,
and `119*113 mod 127 = 112`, so `gcd(119,112)=7`.
This illustrates a genuine factor extraction, but the same factor is
already found by `gcd(119,14)`.

Across the 36,000 sampled semiprimes with factors greater than 100,
the cross-operation gcd tests and gap-width gcd tests found no
nontrivial factors.

A separate modular-power test tried each of `d_-` and `d_+` as a
base, with exponents `(N-1)//2` and `N-1`, and tested gcds of
the resulting residues minus one with `N`. On 6,500 inputs:

| Base selection | Inputs with a factor found |
| --- | ---: |
| The input's own neighboring gaps | 5.338% |
| Gap bases from matched size/residue controls | 5.163% |
| Fixed bases 4 and 6 | 5.385% |

Matched controls used eight peer draws per input. No special advantage
for neighboring-prime bases was established. These are finite success
rates under this trial budget, not end-to-end factoring complexity
benchmarks.

## 2026-10-01: blind zeta coefficient extraction

Let

$$
Z(s)=-\frac{\zeta'(s)}{\zeta(s)},\qquad
Z(s)^2=\sum_{n\ge1}M(n)n^{-s},\qquad M=\Lambda*\Lambda.
$$

For a distinct-prime semiprime,

$$
M(N)=2\log p\log q,\qquad
\eta=\sqrt{\frac{(\log N)^2}{4}-\frac{M(N)}2}.
$$

Thus a sufficiently accurate estimate of `M(N)` determines the factor
imbalance, with the smaller factor recovered by `sqrt(N)*exp(-eta)`.
This observable uses the full von Mangoldt series, including prime powers;
the semiprime coefficient itself has exactly the two ordered prime pairs.

The experiment evaluated actual numerical values of zeta and its derivative,
rather than constructing a prime-pair table:

$$
\widehat M_H(N)=
\frac{N^\sigma}{\sqrt{2\pi}H}
\int_{\mathbb R} Z(\sigma+it)^2
e^{it\log N}e^{-t^2/(2H^2)}\,dt.
$$

Its exact smoothed-series interpretation is

$$
\widehat M_H(N)=
\sum_{n\ge1}M(n)(N/n)^\sigma
e^{-H^2\log^2(N/n)/2}.
$$

### Numerical recipe and evidence limits

- `sigma=3`; working coefficient-error allowance `eps=0.0002`.
- Zeta and its derivative evaluated by analytically differentiated
  Euler–Maclaurin summation with 16 Bernoulli correction terms.
- At each 64-point block, the integer-series endpoint was
  `max(32,ceil(max(t)/2))`. No factor labels or primality information
  were used in these integer sums.
- Positive frequencies were computed explicitly and negative frequencies
  supplied by conjugate symmetry.
- One thread: `OPENBLAS_NUM_THREADS=1`, `OMP_NUM_THREADS=1`.
- Environment: the existing `../.venv/bin/python`, NumPy 2.2.6,
  SymPy 1.14.0, mpmath 1.3.0.
- Point evaluations were compared with mpmath at 40 decimal digits at
  `t=0,0.125,10,100,1000,10000`. Observed absolute discrepancies were
  at most approximately `7.2e-14` for zeta and `5.4e-14` for its
  derivative at those points.
- Analytic leakage, quadrature-aliasing, truncation and Euler–Maclaurin
  bounds were used to select parameters. They do not bound all IEEE
  floating-point roundoff, so the resulting factor intervals are
  experimental rather than formally certified.
- Each recovered integer factor was subsequently verified by exact
  divisibility. Independent factorization labels were introduced only
  after zeta extraction and timing.

For reproducing the conservative Gaussian grid, let
`e=eps/8`, `a=3/2`, and use

$$
H=\frac{\sqrt{2\log(4N^3/e)}}{\log(1+1/N)},
$$

$$
h=\frac{2\pi a}{
\log\!\left(1+
\frac{(36N^{3-a}+4N^{3+a})e^{a^2/(2H^2)}}{e}
\right)},
$$

$$
T=h\left\lceil
\frac{H\sqrt{2\log(4N^3/e)}}h
\right\rceil.
$$

Here `h` is frequency-grid spacing and `T` is its upper endpoint.
These are this prototype's conservative parameter choices, not universal
requirements for every coefficient-extraction algorithm.

### Measured extraction results and fresh-factor baselines

| N | Factors recovered | Zeta time | Positive grid nodes | Fresh-factor SymPy time | GNU factor time |
| --- | --- | ---: | ---: | ---: | ---: |
| 35 | 5 × 7 | 0.095302 s | 4,776 | 4.679 µs | 0.980 ms |
| 77 | 7 × 11 | 0.563619 s | 12,972 | 4.819 µs | 0.967 ms |
| 143 | 11 × 13 | 2.252019 s | 28,081 | 5.238 µs | 0.848 ms |
| 323 | 17 × 19 | 13.367284 s | 76,441 | 5.657 µs | 1.231 ms |

SymPy timings are medians of 31 calls with
`sympy.ntheory.factor_.factor_cache.cache_clear()` before each timed call.
Earlier repeated-call timings used a populated factor cache and were
superseded by these measurements. Library imports remain warm.

GNU timings are medians of seven fresh `factor` subprocesses and include
process startup. The installed coreutils version was 8.32.

Zeta timings exclude imports, Bernoulli-coefficient preparation and the
post-hoc independent factorization check. They include extraction and a
six-width diagnostic scan sharing the same zeta evaluations. Fresh
imports of NumPy/SymPy/mpmath took about 0.223 s, and preparation of the
16 Bernoulli coefficients took about 0.0053 s. This is an exploratory
prototype comparison, not an optimized implementation shootout.

| N | Observed absolute coefficient error | Experimental smaller-factor interval |
| --- | ---: | --- |
| 35 | 3.11e-10 | [4.99852, 5.00149] |
| 77 | 6.84e-12 | [6.99845, 7.00155] |
| 143 | 6.92e-11 | [10.99344, 11.00661] |
| 323 | 1.74e-9 | [16.98484, 17.01542] |

Every interval contained exactly one integer, the correct smaller factor.

A width scan used `H/N` equal to
`0.125,0.25,0.5,1,2,4`. Broader, cheaper filters mixed in neighboring
coefficients; several estimates even made the reconstruction's square-root
radicand negative. At `H/N=4`, the estimate for `N=323` gave a smaller
factor near 17.0406, but without the selected conservative error allowance.
The final conservative widths had `H/N` between approximately 6.83 and
7.67.

### Larger conventional baselines and scaling forecast

Deterministic seed `20261001` supplied balanced, non-close prime factors
for four larger input examples. These are a handful of examples, not a
representative distribution benchmark.

| Input N | Bits | SymPy fresh-factor median | Projected zeta grid nodes |
| --- | ---: | ---: | ---: |
| 16,363,499 | 24 | 0.206 ms | 1.86e10 |
| 5,141,575,211 | 33 | 0.769 ms | 9.71e12 |
| 789,103,629,247 | 40 | 0.792 ms | 2.13e15 |
| 208,812,600,117,463 | 48 | 0.794 ms | 7.88e17 |

The node counts are forecasts from the same parameter rule, not measured
zeta runs or lower bounds on all possible zeta methods.

SymPy's self-initializing quadratic sieve, using `prime_bound=1000` and
`M=5000`, factored the 40-bit example in 0.0919 s and the 48-bit example
in 0.0785 s. The returned factors were verified. GNFS and ECM were not
benchmarked here.

Decision: the tested zeta extractor has no speed advantage, even over
basic conventional methods on tiny inputs. For a positive Gaussian
isolating individual integers, the log separation near `N` is about
`1/N`; this implementation therefore uses frequency width on the scale
of `N`, with logarithmic accuracy costs. Its straightforward
Euler–Maclaurin evaluation adds substantial further work. The scratch
Gaussian theorem audits this filter class, not all signed or arithmetic
factor-localization methods.

## 2026-10-01: first extractor optimization

This version preserves the same coefficient observable and the working
error allowance `eps=0.0002`. It changes parameter selection and the
numerical evaluator; it supplies no new Lean theorem.

### Sharper leakage estimate

For `n>=1`, the elementary divisor identity gives

$$
0\le M(n)=\sum_{d\mid n}\Lambda(d)\Lambda(n/d)
\le \log n\sum_{d\mid n}\Lambda(d)=(\log n)^2.
$$

Let `B(sigma)=1+1/(sigma-1)^2`. Bounding the unimodal function
`log(x)*x^(-sigma)` by its integral plus its maximum gives
`|Z(sigma+it)|<=B(sigma)` for `sigma>1`.
For the 24 nearest integer offsets on each side of `N`, bound each
coefficient individually. Only the more distant tail receives the
whole-series bound. The resulting leakage bound is

$$
E_D(N,H)\le
\sum_{\substack{0<|d|\le D\\N+d\ge2}}
(\log(N+d))^2\left(\frac{N}{N+d}\right)^\sigma
e^{-H^2\log^2((N+d)/N)/2}
+N^\sigma B(\sigma)^2
e^{-H^2\log^2(1+(D+1)/N)/2}.
$$

Here `D=24`; no neighboring coefficient is factored or supplied as an
oracle. Choose `H` by solving for the bound to equal `eps/8`. At
`N=323,sigma=3`, this reduces `H/N` from approximately 7.669 to 5.440.
Selecting the analytic quadrature strip from four candidate widths also
reduces the frequency count from 76,441 to 45,022.

### Faster finite zeta evaluation

Use 20 Euler–Maclaurin corrections and select the integer-series endpoint
for each block by its explicit analytic remainder bound, rather than
setting it to half the frequency. At the largest frequency for `N=323`,
the new endpoint is 3,010 instead of roughly 9,484 in the first prototype.

For consecutive frequencies, reuse the exact identity

$$
e^{-i(t+h)\log n}=e^{-it\log n}e^{-ih\log n}.
$$

Evaluate blocks of 128 samples by multiplicative phase recurrence,
reinitializing the phase at each block. This replaces most complex
exponential evaluations by complex multiplications. An identical-grid
ablation at `N=323` took 2.539 s with direct exponentials and 0.731 s
with recurrence. These are individual measured runs, not universal
speed ratios.

### First optimized run

| N | Original zeta time | Optimized zeta time | Approximate improvement |
| --- | ---: | ---: | ---: |
| 35 | 0.095302 s | 0.016275 s | 5.9× |
| 77 | 0.563619 s | 0.052467 s | 10.7× |
| 143 | 2.252019 s | 0.157133 s | 14.3× |
| 323 | 13.367284 s | 1.126942 s | 11.9× |

All four factors were recovered from single-integer experimental
intervals and checked by exact division. Observed coefficient errors
were between about `5.9e-7` and `4.7e-6`, below the working allowance.
The narrower filter intentionally uses more of the error allowance than
the original over-precise run.

The same method recovered `899=29*31` in 7.881 s. A later run took
6.676 s; runtime depends on system load. It also recovered independent
test inputs `221=13*17`, `437=19*23`, `667=23*29` and `1147=31*37`
using `sigma=2`. Lowering `sigma` reduces numerical amplification but
requires more quadrature nodes, so it did not improve runtime on these
small inputs. The `sigma=2` run recovered `2021=43*47` in 48.531 s.
A first `sigma=3` run on that input stopped at a 30-second execution
cap before completing its grid; that is an execution limit, not a
failed factor estimate.

Independent 40-digit checks of the optimized evaluator covered
`sigma=2,3`, four frequencies near each of `0,10,100,1000,10000`.
Maximum observed discrepancies were approximately `3.4e-13` for zeta
and `3.7e-13` for its derivative. Analytic approximation bounds still
do not certify floating-point roundoff.

Decision: meaningful implementation improvement, but the repeated
finite-series evaluations still scale poorly. The next test is to
evaluate the entire equally spaced frequency grid together, using
FFT gridding plus a controlled Taylor correction for the nonuniform
frequencies `h*log(n)`. No prime-pair table is needed for this test.

## 2026-10-01: FFT evaluation of the whole frequency grid

The next version replaces repeated finite zeta sums by a batched
nonuniform Fourier evaluation. It keeps the sharper leakage estimate,
the coefficient error allowance `eps=0.0002`, and analytically
differentiated Euler–Maclaurin corrections. Its test contour is
`sigma=2`, which limits numerical amplification by `N^sigma`.

### Exact expansion behind the acceleration

For a fixed finite integer endpoint `m`, both the finite zeta sum and
its derivative have the form

$$
S_j=\sum_{1\le n<m}a_n e^{-ijh\log n},\qquad 0\le j<K.
$$

Use `a_n=n^(-sigma)` for zeta and `a_n=-log(n)*n^(-sigma)` for its
derivative. The coefficients are real. No prime-factor table occurs.

Choose an FFT length `L>=2K`, round `h*log(n)` to the nearest grid angle,
and set

$$
b_n=\operatorname{round}\!\left(\frac{Lh\log n}{2\pi}\right),
\qquad
\delta_n=h\log n-\frac{2\pi b_n}{L}.
$$

For each Taylor order, bin the real coefficients as

$$
C_r[b]=\sum_{b_n\equiv b\pmod L}
a_n\frac{(K\delta_n)^r}{r!}.
$$

The exponential expansion then gives

$$
S_j=\sum_{r=0}^{P}
\left(-i\frac jK\right)^r\operatorname{FFT}_L(C_r)[j]+E_j.
$$

Since `|delta_n|<=pi/L` and `j<K`, every Taylor argument has magnitude
at most `pi/2`. In exact arithmetic,

$$
|E_j|\le
e^{\pi/2}\frac{(\pi/2)^{P+1}}{(P+1)!}\sum_{n<m}|a_n|.
$$

At `P=24`, the scalar tail factor is approximately `2.481e-20`.
This bounds Taylor truncation only; frequency rounding and FFT
floating-point errors are separate. No formal certification of those
errors is claimed.

The implementation uses `scipy.fft.next_fast_len(2*K, real=True)` and
single-worker `scipy.fft.rfft`. Because every `C_r` is real and
`j<K<=L/2`, the real FFT contains all required output frequencies.
The finite-series endpoint is chosen once for the largest frequency,
and the ordinary Euler–Maclaurin tail and derivative are then added
at every sample.

The batched finite-sum work is roughly `O(P*(m+K*log K))`, instead
of `O(m*K)` individual finite-series work. Euler–Maclaurin corrections
add linear work in the sample count for fixed correction order.
This is an improvement in evaluation cost; the coefficient isolation
still requires a large frequency grid.

### Results

| N | Recovered factors | FFT extractor time | Observed coefficient error magnitude |
| --- | --- | ---: | ---: |
| 35 | 5 × 7 | 0.02251 s | 4.58e-6 |
| 77 | 7 × 11 | 0.01466 s | 2.28e-6 |
| 143 | 11 × 13 | 0.03167 s | 3.58e-6 |
| 221 | 13 × 17 | 0.06293 s | 2.53e-10 |
| 323 | 17 × 19 | 0.12689 s | 5.93e-7 |
| 437 | 19 × 23 | 0.22613 s | 2.13e-6 |
| 667 | 23 × 29 | 0.41275 s | 2.14e-6 |
| 899 | 29 × 31 | 0.65844 s | 2.25e-6 |
| 1147 | 31 × 37 | 0.88028 s | 2.45e-10 |
| 2021 | 43 × 47 | 1.69671 s | 3.92e-10 |

All ten experimental intervals contained exactly one integer, and
exact division verified the factor. Factorization labels were introduced
only after extraction and timing. The first FFT run at `N=35` includes
first-call FFT overhead; the results show that FFT is not always the
fastest evaluator on the smallest grids.

Three-repeat timings for the larger examples were:

| N | FFT times, seconds | Median | Fresh-factor SymPy median |
| --- | --- | ---: | ---: |
| 323 | 0.10455, 0.10315, 0.10223 | 0.10315 s | 5.727 µs |
| 899 | 0.52977, 0.53107, 0.53549 | 0.53107 s | 6.635 µs |
| 2021 | 1.70454, 1.70931, 1.71134 | 1.70931 s | 7.682 µs |

The `N=323` median is about 130× faster than the original 13.367 s
prototype. The `N=2021` median is about 28× faster than the previous
48.531 s recurrence run on the same `sigma=2` quadrature grid. Library
imports, Bernoulli-coefficient preparation and independent reference
factorization are excluded from the extractor times. The SymPy timing
used 31 calls with its factor cache cleared before each timed call.

Independent 40-digit comparisons at nine points each on the `N=323`
and `N=2021` grids observed discrepancies of at most approximately
`1.8e-12` for zeta and `2.7e-12` for its derivative. The larger grid
extends to frequency approximately 82,598. These sampled checks and
the small observed coefficient errors are numerical evidence, not
interval-arithmetic or Lean certification.

### Interpretation and remaining obstruction

The improvement is real, but conventional factoring still wins by
roughly four to five orders of magnitude on these tiny inputs. The
FFT accelerates access to the same observable; it does not remove
the product-resolution problem. In particular, `N=2021` still uses
484,433 frequency samples despite having only 11 input bits.

The next mathematical improvement would need to reduce coefficient
isolation cost or extract factor-sensitive information without isolating
the coefficient. Possible computational follow-ups are a cheaper signed
filter, adaptive measurement precision with a bounded candidate budget,
and reuse of a common spectral grid across many inputs. These are
untested options, not achieved speedups. Any batch comparison must
include preprocessing and compare against batch arithmetic/sieving
methods, rather than only isolated calls to a factorization library.

## 2026-10-01: scaling audit

Question: could the zeta extractor lose on small semiprimes but eventually
win on huge ones? That is a valid criterion for a new algorithm, but the
current extractor has unfavorable asymptotic scaling.

Let `b=ceil(log2(N))`. Resolving nearby product coefficients requires
separating logarithms whose spacing is about `1/N`. The current positive
Gaussian therefore uses `H` proportional to `N`, with accuracy factors.
Its truncation endpoint is `T=H*sqrt(2*log(N^sigma*B(sigma)^2/e))`, and
the analyticity-based grid spacing decreases on a `1/log(N)` scale.
The grid count `K=ceil(T/h)+1` thus grows at least on the scale of `N`,
with additional logarithmic factors.

In particular, even an idealized evaluator costing roughly one operation
per sample would require exponentially many operations in `b`, since
`N` is approximately `2^b`. FFT batching improves the finite-sum evaluation
to `O(P*(m+K*log K))`; it does not reduce `K`.

This is an audit of this implementation and its parameter strategy,
not a lower bound on every possible zeta-based factoring method.

### Comparison with established methods

For generic balanced semiprimes, suppressing polynomial costs of
big-integer arithmetic, the usual scaling comparison is:

| Method | Growth with input bit length b |
| --- | --- |
| Current zeta extractor's sample processing | At least on the `2^b` scale, with additional costs |
| Trial division | Approximately `2^(b/2)` candidate divisions |
| Pollard rho | Heuristic expected `2^(b/4)` modular-operation scale |
| Quadratic sieve | Heuristic `exp(O(sqrt(b*log b)))` |
| General number field sieve | Heuristic `exp(O(b^(1/3)*(log b)^(2/3)))` |

Pollard rho's `O(sqrt(p))` scale comes from its collision model; for a
balanced semiprime the smaller prime is on the `sqrt(N)` scale.
See [Pollard's original paper](https://pages.cs.wisc.edu/~cs812-1/pollardrho.pdf).
The sieve estimates are heuristic subexponential bounds, not certified
runtime limits for every input; see
[Pomerance, A Tale of Two Sieves](https://math.dartmouth.edu/~carlp/PDF/paper109.pdf).
These comparisons do not use quantum algorithms.

Adding ten input bits multiplies the current grid's leading `N`
dependence by approximately 1,024, before logarithmic costs. The
corresponding leading factor for Pollard rho is approximately 5.66.
The sieve algorithms have slower asymptotic growth still.

### Parameter-only projections

Evaluate the improved leakage/grid formulas at magnitude `N` near
`2^b`, `sigma=2`, `D=24`, and the original fixed `eps=0.0002`.
The evaluation uses logarithmic arithmetic and mpmath to avoid overflow
and the loss of `N+1` in floating-point calculations. No large zeta
grid is allocated and no large semiprime is factored in this forecast.

| Product magnitude | Projected frequency samples |
| --- | ---: |
| Near 16 bits | 2.35e7 |
| Near 24 bits | 9.74e9 |
| Near 32 bits | 3.60e12 |
| Near 64 bits | 3.97e22 |
| Near 128 bits | 2.00e42 |

These are predictions for the chosen parameter rule, not measured
runtime or universal requirements for coefficient extraction.

### Accuracy adds further costs

Holding the coefficient tolerance fixed does not maintain a fixed-width
factor interval as `N` grows. For the continuous reconstruction formula,

$$
M=2\log p\log(N/p),\qquad
\frac{dM}{dp}=\frac{4\eta}{p}.
$$

Consequently the local factor sensitivity is `dp/dM=p/(4*eta)`.
When the imbalance `eta` stays a fixed positive constant and `p` is on
the `sqrt(N)` scale, a constant-width factor interval needs coefficient
error on the `N^(-1/2)` scale. Very close factors can require finer
accuracy. This is a sensitivity calculation, not a replacement for the
scratch theorem's explicit interval/error hypotheses.

As an illustrative calibration, setting `eps=1/(4*sqrt(N))` instead
predicts approximately `4.34e12` grid samples near 32 bits and
`6.33e22` near 64 bits. That calibration is not a universal certificate
for every possible factor imbalance.

The current double-precision implementation and fixed Taylor degree
24 cannot simply be used at those large sizes. The analytic Taylor
error is amplified by `N^sigma`; the degree and arithmetic precision
must grow to keep the extraction allowance. A fixed 20-term
Euler–Maclaurin choice also gives extra growth in the integer-series
endpoint. Therefore the grid forecasts already omit further costs
needed for a reliable large-input implementation.

Decision: the 130× small-input improvement is useful computationally,
but it does not create an eventual advantage over conventional
factorization. The next competitive mechanism needs to change the
dependence on product magnitude, through a different observable,
a substantially different isolation strategy, or an arithmetic
localization identity. Further FFT tuning alone leaves the dominant
scaling obstruction intact.

## 2026-10-01: repository audit for a different scaling mechanism

This audit inspected local Lean source; it did not recompile the declarations
or alter the main RH campaign. The specializations and numerical mask test
below are side-investigation deductions, not newly checked Lean theorems.
The search covered the finite divisibility/Fourier, prime-count, coprime
Euler, factorial-filter, prime-colour, semiprime Riesz and convolution files.

### Factor-sensitive identities worth retaining

1. **Exact semiprime cutoff profile.**
   `riesz_semiprime_eq_tent` in
   [ZetaRieszSemiprimePrefixDecay.lean](../RiemannGaussian/ZetaRieszSemiprimePrefixDecay.lean)
   keeps the complete two-prime tent. For distinct `p<q`, its specialization is

   $$
   \mathcal R_L(pq)=L_+-(L-\log p)_+-(L-\log q)_+
     +(L-\log N)_+.
   $$

   In particular, at `L=log(N)/2` the response is exactly `log(p)`, as
   already stated in the scratch theorem. Its breakpoints also identify
   both factors. The missing algorithm is an evaluator from `N,L` that
   avoids enumerating unknown divisors; the tent identity itself does not
   supply one.

2. **Finite coprime Euler factor contains the factor sum.**
   `CoprimeEulerPhase.coprimeEuler_eq_product` in
   [ZetaCoprimeEulerPhase.lean](../RiemannGaussian/ZetaCoprimeEulerPhase.lean)
   gives, for this squarefree semiprime,

   $$
   E_N(s)=\sum_{d\mid N}\mu(d)d^{-s}
     =(1-p^{-s})(1-q^{-s}).
   $$

   Specializing the finite expression at `s=-1` gives
   `E_N(-1)=N+1-(p+q)=(p-1)(q-1)`. Knowing this integer would determine
   `p+q`, hence the roots of `X^2-(p+q)X+N`. This is an exact alternative
   to measuring a log-product coefficient, but `zetaCoprimeEulerFactor`
   is defined through `N.divisors`. Evaluating that definition is not a
   blind fast algorithm. Its convergent infinite-series representation
   is only established for `Re(s)>1`; it must not be evaluated at `-1`
   by an unsupported series continuation.

3. **Opposite phases retain the split; ordinary multiplicative phase does not.**
   The scratch `pairSpectrum_semiprime` is `2*cos(2*t*eta)`.
   `total_phase_product` instead gives only `exp(i*t*log(N))`.
   The latter is already known from the input. The exact pair moment and
   Suzuki convolution identities preserve genuinely factor-sensitive
   coefficients, but the existing coefficient-isolation cost remains.

4. **Newton identities remove repeated-prime contamination.**
   `PrimeNewtonThree.newton_two` in
   [PrimeNewtonThree.lean](../RiemannGaussian/PrimeNewtonThree.lean) proves
   `2*pairPrefix = (sum f)^2 - sum(f^2)` for a finite prime universe.
   This is a precise signed diagonal deletion. It can clean a prime-pair
   observable without approximating the diagonal, but it does not select
   the unknown product's coefficient or bound its evaluation cost.

### Masks with an evaluator from the input alone

`sum_divisors_moebius_dvd_eq_coprime` in
[EtaMoebiusCoprimeProduct.lean](../RiemannGaussian/EtaMoebiusCoprimeProduct.lean)
identifies the whole signed common-divisor sum with `1[gcd(N,a)=1]`.
The right side is directly computable without factoring `N`. This is
an important computational distinction from a generic divisor sum.

The finite union and prime-pattern identities in
[FiniteDivisibilitySieve.lean](../RiemannGaussian/FiniteDivisibilitySieve.lean)
and [FinitePrimePatternSieve.lean](../RiemannGaussian/FinitePrimePatternSieve.lean)
retain signed overlaps exactly. They motivate testing a block of candidate
integers using `gcd(N, product(block) mod N)`, followed by subdividing a
successful block. This is a batched arithmetic search, not a new zeta
oracle. Product construction, collisions where both factors are present,
and the full candidate-range cost must all be counted. No new asymptotic
factoring bound follows from these source identities.

For example, before reaching the smaller factor, every positive candidate
`a<p` has `gcd(N,a)=1`. An unweighted initial coprimality scan therefore
has no early factor signal. Batching can change evaluation cost, not this
exact arithmetic fact.

### Exact Fourier residue masks: numerical cost audit

`sum_range_finiteCircleWave` and
`sum_range_finiteCircleWave_mul_conj` in
[FiniteCircleFourier.lean](../RiemannGaussian/FiniteCircleFourier.lean)
provide the orthogonality needed for an exact product-index mask:

$$
\frac1Q\sum_{a=0}^{Q-1}
   e^{2\pi i a(n-N)/Q}=\mathbf 1_{n\equiv N\pmod Q}.
$$

Applying this to the Gaussian extractor leaves aliases at `N+d*Q`,
rather than every neighboring integer. We tested the resulting *analytic
leakage envelope*, without factoring or building a prime-pair table:
`N=2021`, `sigma=2`, `D=24`, leakage budget `0.0002/8`.
For each modulus, solve `E_Q(H)=budget`, where

$$
\begin{aligned}
E_Q(H)={}&\sum_{0<|d|\le D,\,N+dQ\ge2}
  \log^2(N+dQ)\left(\frac N{N+dQ}\right)^\sigma
  e^{-H^2\log^2((N+dQ)/N)/2}\\
&+N^\sigma B(\sigma)^2
  e^{-H^2\log^2(1+(D+1)Q/N)/2}.
\end{aligned}
$$

The far term deliberately bounds the remaining mass by the same
unmasked absolute-series bound used earlier. This is a floating parameter
calculation, not an interval-certified implementation of masked L-series.

| Modulus `Q` | Required `H` | Bandwidth reduction | `Q*H` / unmasked `H` |
| ---: | ---: | ---: | ---: |
| 1 | 11197.537166 | 1.000000 | 1.000000 |
| 7 | 1599.696790 | 6.999787 | 1.000030 |
| 31 | 361.429361 | 30.981260 | 1.000605 |
| 127 | 88.998094 | 125.817719 | 1.009397 |
| 509 | 23.778766 | 470.904894 | 1.080898 |

The numerical finite-circle selector agreed with its exact integer mask
to residuals below `4.5e-14` for `Q=7,31,127`.

Decision: congruence filtering genuinely improves isolation, but a direct
`Q`-channel evaluation gives essentially the same channel-times-bandwidth
cost. `Q*H` is a diagnostic work proxy, not measured runtime or a lower
bound for all implementations. A useful speedup would require a shared
evaluation of the masked series that saves the channel cost as well.
The additive twist acts on the product index `n`; it is not obtained just
by changing the vertical ordinate in an ordinary zeta evaluation.

### Relevant exclusions and next computational target

- The prime-count Euler series has coefficient `mu(N)*z^omega(N)=z^2`
  for a distinct-prime semiprime. Count information alone is already known.
- `zetaPrimeDivisorCoefficient_eq` and `squarefree_log_eq_prime_sum`
  reduce the complete sum of distinct-prime logarithms to `log(N)`.
  That common colour weight does not distinguish the split.
- Independent fourth-root colour averaging in
  [Zeta23FourthMomentPhaseColour.lean](../RiemannGaussian/External/Zeta23FourthMomentPhaseColour.lean)
  removes unbalanced labelled monomials, but requires the labelled finite
  family and does not supply the missing factors or a cheap product mask.
- The exposed-zero prime filters require a specified hypothetical zero
  and exposure hypotheses. They are spectral tools for the RH campaign,
  not unconditional factor-location estimators for an input semiprime.
- `eventually_zetaFactorialLocalAmplitude_near_one` in
  [ZetaFactorialFilterLocalization.lean](../RiemannGaussian/ZetaFactorialFilterLocalization.lean)
  shows that a fixed normalized filter remains near one on its affine
  logarithmic window. It is not a universal obstruction to all moving
  filters, but rules out attributing sharp localization to that fixed
  normalization alone.
- `sum_pairedEtaInverseOuterDivisible_mul_eq` exactly isolates `f(q)`
  from a finite inverse hyperbola when `q` is supplied. It does not find
  an unknown factor; evaluating its signed hyperbolic sum still has a cost.

The most immediately executable avenue is input-only batched divisibility
and interval localization. For a specifically zeta-based improvement,
the focused open task is shared evaluation of a signed residue-masked,
opposite-phase pair observable. It must demonstrate an end-to-end saving
in channel count and coefficient isolation, not just a narrower kernel.
None of the inspected theorems yet supplies that algorithm.

## 2026-10-01: prime anchors and a cheap rough-prime Euler filter

The user correctly emphasized that the available preprocessing includes
the nearest surrounding primes. These supply a logarithmic bracket and
exact arithmetic calibration values, even though they are computable
from the input rather than independent external data.

For `N=2021`, the nearest primes are `r_-=2017` and `r_+=2027`, at
distances 4 and 6. In the Dirichlet-series coordinate this gives

$$
\log(2017)<\log(2021)<\log(2027).
$$

For the full von Mangoldt coefficient the endpoint values are
`Lambda(r_±)=log(r_±)`. For our pair coefficient `M=Lambda*Lambda`,
both endpoint values are exactly zero. An interior composite can still
have nonzero `M`; a prime gap is not a gap in the pair spectrum.

### Exact filtering with known small primes

Choose a *known* small-prime set `S_B={ell prime: ell<=B}` and put
`P_B=product(S_B)`. First compute `gcd(N,P_B)`. A nontrivial gcd already
finds a divisor; if it equals 1, the target pair coefficient is preserved.
Use the single modified zeta response

$$
Z_B(s)=Z(s)-\sum_{\ell\in S_B}\frac{\log\ell}{\ell^s-1}
      =-\frac{d}{ds}\log\left(\zeta(s)
                 \prod_{\ell\in S_B}(1-\ell^{-s})\right).
$$

On `Re(s)>1`, its coefficients are exactly the von Mangoldt coefficients
with the selected prime powers removed. Squaring gives

$$
Z_B(s)^2=\sum_{n\ge1}M_B(n)n^{-s},\qquad
M_B(n)=M(n)\mathbf 1_{\gcd(n,P_B)=1}.
$$

This follows because a nonzero von Mangoldt leg is a prime power, and
coprimality of a product with `P_B` is equivalent to coprimality of both
legs. It is an exact derived identity; it has not been added as a new
Lean theorem in this side investigation. The finite coprime Euler and
convolution files supply the underlying identities.

This differs computationally from a direct `Q`-channel residue selector:
there is one zeta/derivative evaluation per frequency, with a finite
explicit correction for the selected primes. No unknown divisor of `N`
enters that correction.

For `B=7`, exclude the known primes `2,3,5,7`. Only 2021 survives these
coprimality tests among the composite integers strictly between 2017 and
2027. The nearest other integers that *could* have nonzero filtered pair
coefficient are 1991 and 2033. A survivor is not asserted to have nonzero
pair coefficient; using its `log^2(n)` bound is conservative.

### Parameter and extractor tests

Use `sigma=2`, `eps=0.0002`, and scan offsets `|d|<=128` around the
target. Delete an alias from the near leakage bound if it has a selected
small prime factor (by gcd) or is itself prime. Keep the same unfiltered
absolute-series bound for the entire far tail. The algorithm counts the
small-prime generation, neighboring-prime search, local gcd/primality
checks, parameter selection and extraction in its timing. Imports and
the already-prepared Bernoulli coefficients are excluded consistently
with the earlier FFT comparison.

For 2021, the bandwidth calculations gave:

| Known small-prime cutoff | Number of selected primes | Required `H` | Reduction from unmasked `H` |
| ---: | ---: | ---: | ---: |
| None | 0 | 11197.537166 | 1.000000 |
| 2 | 1 | 5598.779222 | 1.999996 |
| 7 | 4 | 914.197989 | 12.248482 |
| 19 | 8 | 423.217719 | 26.458101 |

With no Euler deletion, removing the known prime aliases alone did not
change the bandwidth materially in this example: the adjacent composite
aliases still controlled the bound. The strong gain is from the known
small-prime filter and local support checks together; it must not be
attributed to the two prime endpoints alone.

We then ran the actual zeta/derivative FFT extractor, replacing `Z^2`
by `Z_B^2`. This was not a prime-pair coefficient-table evaluation.
The following are three-run medians in the same comparison process,
using `B=7` for all three inputs:

| N | Surrounding primes | Unfiltered FFT | Filtered FFT | Speedup | Exact division result |
| ---: | --- | ---: | ---: | ---: | --- |
| 323 | 317, 331 | 0.124627 s | 0.019693 s | 6.33× | 17 × 19 |
| 899 | 887, 907 | 0.641987 s | 0.231736 s | 2.77× | 29 × 31 |
| 2021 | 2017, 2027 | 1.661500 s | 0.065348 s | 25.43× | 43 × 47 |

All runs produced a single-integer smaller-factor interval and verified
it by exact division. Observed coefficient errors were approximately
`1.19e-5` to `1.22e-5`, within the working `0.0002` allowance. Independent
factorization labels were not used in the filter, parameter selection,
zeta evaluation or candidate recovery.

A single additional `B=19` run at 2021 took `0.026232 s`, used 18,311
frequency nodes and an Euler–Maclaurin integer endpoint of 870, and
recovered 43 and 47. Four independent 40-digit mpmath checks of the
filtered logarithmic derivative had discrepancies at most `8.8e-14`.
This last timing is a single run, not a median.

These are floating numerical experiments with exact final divisibility
verification. There is still no interval bound for all accumulated
floating-point error and no new Lean-certified numerical extractor.
The test scripts ran in memory, as in the earlier experiments.

Decision: preprocessing supplies useful exact coefficient zeros and a
substantial practical improvement on these small inputs. The earlier
negative gap-feature regression did not test this filtering mechanism.
There is still no demonstrated asymptotic factoring advantage: with a
fixed small-prime cutoff and a fixed 128-offset support scan, the far-tail
parameter retains bandwidth proportional to the product magnitude up
to logarithmic factors. Scaling the cutoff or scan must account for the
cost of finding and applying every additional zero.

## 2026-10-01: modular factor-sum signal and stronger residue colours

### Exact signal, decoder and scaling

For distinct primes `N=p*q`, write `S=p+q`. Euler's theorem and
`phi(N)=N+1-S` give

$$
\boxed{a^{N+1}\equiv a^S\pmod N,\qquad \gcd(a,N)=1.}
$$

This is a modular encoding, not an ordinary complex phase readable by an
argument operation. Acquisition needs one modular exponentiation; repeated
squaring costs `O(b*M(b))` bit operations for `b=bit_length(N)`.
It requires no zeta coefficient extraction, factor-pair table, neighbouring
factorisation or Fourier grid.

Under the public promise `p<=q<=R*p`,

$$
2\sqrt N\le S\le(R+1)\sqrt{N/R}.
$$

For `R=2`, the exact integer endpoints are `L=ceil(sqrt(4N))` and
`U=floor(sqrt(9N/2))`. Compute `h=2^(N+1-L) mod N` and decode
`h=2^(S-L) mod N` inside this interval. Known small prime divisors and
perfect squares are checked first.

Every collision candidate must have square discriminant `S^2-4N`, correct
parity, and a proper divisor verified by exact division. Duplicate modular
values retain ALL associated exponents. The saved regression exercises
`N=2047`, where base 2 has order 11, and rejects a false collision before
recovering `23*89`.

Since the interval width is approximately `(3/sqrt(2)-2)*sqrt(N)`, the
usual baby-step/giant-step search-size heuristic is `O(N^(1/4))`, or
`O(2^(b/4))`. It is not an unconditional runtime theorem for this
implementation: small multiplicative order can create extra candidates.
No input-bit-length `O(b log b)` factorisation has been obtained.

### Cheap colour and prime-power correlations

For a known small modulus `m` coprime to `N`, every valid factor sum lies in

$$
A_m(N)=\{t+Nt^{-1}\bmod m:\ t\in(\mathbb Z/m\mathbb Z)^\times\}.
$$

At odd prime moduli this is equivalent to requiring the discriminant to
be a quadratic residue. The decoder joins permitted residues by CRT
directly; it does not scan the full product wheel. Each giant stride is
a multiple of that wheel. Precomputed modular jumps visit only permitted
baby exponents.

With permitted density `rho` and stride `m`, approximate work is
`rho*m+(U-L)/m`, minimized near `m=sqrt((U-L)/rho)`. This improves
constants and memory, not the `N^(1/4)` exponent. Adaptive decoding first
searches a smaller interval and reuses the baby table as the stride grows.
The actual factor sum and factor ratio never enter the policy.

Prime-power lifts preserve additional exact correlations:

- If `N=1 mod 3`, both factors have the same residue modulo 3. Hence
  `p-q` is divisible by 3 and the discriminant vanishes modulo 9.
  At `N=3337` the modulo-3 mask admits six lifts modulo 9, while the
  exact mask admits only `{1,8}`.
- If `N=1 mod 4`, moving from modulus 8 to 16 halves the unit
  factor-sum mask's density. At `N=2021`, the four lifts admitted by
  the modulo-8 mask reduce to `{6,10}` modulo 16.
- Stationary-residue lifts modulo 25 are used when `N` is a quadratic
  residue modulo 5.

The frozen input-only policy uses 8 or 16, 3 or 9, 5 or 25, and selected
primes 7, 11, 13 and 17. Larger wheels are used only at larger bit lengths.
Every input's wheel construction is included in its timing.

### Benchmark progression

The initial decoder recovered all 210 generated semiprimes through
63–64 input bits. A sparse CRT decoder recovered all 120 subsequent
fresh cases; at 63–64 bits its median was 1.10 ms versus 5.63 ms without
colours. Comparing to a stronger native baseline then erased the apparent
large advantage over Python Pollard–Brent: GNU `factor` was approximately
level with the fixed-wheel decoder at 64–80 nominal bits and faster at 88.

Adaptive interval growth and prime-power masks produced the following
in-memory result on a fresh corpus, with seed `2026100900+nominalBits`.
Settings were frozen before the sample. Times are median three-run
batch-average milliseconds per input, with method order shuffled
deterministically:

| Actual input bits | Inputs | Prime-power prototype | GNU `factor` 8.32 |
| ---: | ---: | ---: | ---: |
| 63–64 | 48 | 0.50196 ms | 0.97367 ms |
| 79–80 | 32 | 5.35771 ms | 21.11880 ms |
| 87–88 | 20 | 12.08723 ms | 99.13121 ms |
| 95–96 | 8 | 54.58630 ms | 442.08379 ms |

All 108 factors passed exact checks. Imports, prime generation and
reference labels were outside the timing regions. Decoders received only
`N`, the public `q/p<=2` promise and public settings. Native timing includes
one process startup and captured output per batch. GNU performs general
factorisation; this decoder uses the balance promise.

The saved implementation has structured counters and an explicit resource
cap. Its fresh replay of the same seeded corpus is recorded in
[semiprime-modular-signal-audit.json](semiprime-modular-signal-audit.json),
including every input/reference pair, decoder statistics, all timing
repetitions, environment/baseline versions and the source SHA-256:

| Actual input bits | Inputs | Saved decoder | GNU `factor` 8.32 | Speedup |
| ---: | ---: | ---: | ---: | ---: |
| 63–64 | 48 | 0.58213 ms | 0.98113 ms | 1.69× |
| 79–80 | 32 | 6.24033 ms | 21.17065 ms | 3.39× |
| 87–88 | 20 | 14.59621 ms | 99.10359 ms | 6.79× |
| 95–96 | 8 | 66.01737 ms | 441.49579 ms | 6.69× |

Every replay input factored exactly. The source also passes 601 small
semiprime/perfect-square checks, 16 independently enumerated CRT masks,
a low-order alias regression and an explicit table-cap regression.
A pure-Python fallback recovered
`24514908557095695328929618289 = 151488737100313 * 161826608540953`.

The balance restriction matters. An earlier adaptive-prototype audit used
12 inputs per population, seed `2026100780`, and a public ratio ceiling
large enough for each population:

| Nominal bits | Factor bit lengths | Ratio ceiling | Adaptive prototype | GNU `factor` |
| ---: | --- | ---: | ---: | ---: |
| 80 | 40,40 | 2 | 9.30631 ms | 29.66532 ms |
| 80 | 39,41 | 8 | 52.44166 ms | 21.24412 ms |
| 80 | 38,42 | 32 | 94.14567 ms | 10.41097 ms |

Thus this is a measured win in a specified regime and baseline version.
There is no claim of a record, superiority over current GNU versions,
tuned quadratic sieve or NFS, or improved asymptotic complexity.
Published deterministic `N^(1/5)` methods already improve the exponent
through shared weighted-factor-sum collisions and lattice constructions.
Those methods are the relevant scaling comparison.

### Other colour and signal gates

These exploratory probes ran in memory. Their aggregate results are
preserved without claiming complete executable reproduction:

- Quartic colour can distinguish factor splits with the same product
  colour. Independent fourth-root averaging kills the pair amplitude
  while preserving balanced pair energy. It does not cheaply select the
  unknown semiprime coefficient; phase-colour identities are not themselves
  factorisation oracles.
- The unit-restricted Gauss sum
  `U_N=sum_(x mod N, gcd(x,N)=1) exp(2*pi*i*x^2/N)` is factor-sensitive.
  Put `F=epsilon_N*sqrt(N)+1-U_N`, where `epsilon_N=1` for `N=1 mod 4`
  and `i` for `N=3 mod 4`. The derived reconstruction is `S=abs(F)^2`
  in the second case and `S=abs(F^2-2*sqrt(N))` in the first.
  Ten small-semiprime checks agreed within `5.14e-12`. No cheap evaluator
  of the unit restriction was found: the discarded nonunits carry the
  factor-sensitive correction, and sampling a nonunit already finds a factor.
- A Lucas parameter with `Jacobi(P^2-4,N)=-1` guarantees opposite
  local quadratic colours. A 1,800-input audit compared this variant with
  fixed Lucas and ordinary `p-1` at smoothness bounds 32, 128 and 512,
  seed `2026100521`. Returned-factor checks passed, but no consistent
  advantage over fixed Lucas was found. This is classical Williams
  `p+1` machinery, not a near-linear algorithm.

### Saved source and replay commands

The optional decoder is
[probe_semiprime_modular_signal.py](../scripts/probe_semiprime_modular_signal.py).
It is not integrated into ordinary builds or CI. From `formal/`, using
the existing research virtual environment:

~~~bash
PYTHONDONTWRITEBYTECODE=1 ../.venv/bin/python -B scripts/probe_semiprime_modular_signal.py validate
PYTHONDONTWRITEBYTECODE=1 ../.venv/bin/python -B scripts/probe_semiprime_modular_signal.py factor 24514908557095695328929618289
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python -B scripts/probe_semiprime_modular_signal.py benchmark --output docs/semiprime-modular-signal-audit.json
~~~

The benchmark is explicit and optional. Its defaults are
`--bits 64 80 88 96 --counts 48 32 20 8 --seed-base 2026100900 --repeats 3`.
GMP is optional for individual decoding (`factor --no-gmp`); generated
experiments require SymPy and a GNU-compatible `factor` executable.
The two-million-entry table cap reports resource exhaustion rather than
treating an unfinished search as evidence.

The older source
[probe_semiprime_partial_information.py](../scripts/probe_semiprime_partial_information.py)
is preserved too. Its Euler–Maclaurin correction had an extra integer-
endpoint factor previously removed only in memory. The saved source now
contains that correction. Nine independent 45-digit mpmath checks of its
small zeta grid had maximum zeta/derivative discrepancies below `5e-16`.
This is a numerical regression, not a floating-error certificate.

## 2026-10-02: weighted batching, sparse signals and independent tables

This entry preserves the later in-memory investigation as executable source
and a fresh replay in
[semiprime-sparse-batch-audit.json](semiprime-sparse-batch-audit.json).
The artifact separates historical measurements from saved-source results
and records source hashes, seeds, dependency versions and corpus information.
The algebra below has exact Python regression checks; it has not been
formalised in Lean in this slice.

### Cheaper shared collision work

[probe_semiprime_weighted_batch.py](../scripts/probe_semiprime_weighted_batch.py)
preserves the weighted factor-sum prototype. It joins primitive balanced
rows `a*b<=r`, with `r` proportional to `N^(1/5)`, using centres
`ceil(2*sqrt(a*b*N))` and anchors `2^(a*N+b-centre) mod N`.
The implementation combines an exact Kronecker product tree, geometric
evaluation by a Bluestein convolution, blocked GCD extraction, and a
NumPy Montgomery accelerator for sufficiently many anchors. Small batches
retain the simpler GMP exponentiation path.

The new order gate tests geometric products in approximately square-root
many evaluations. A proper GCD returns a factor; unit products certify
that neither prime sees order at most the requested cutoff. A global
low-order collision is reported as a failure rather than silently treated
as a certificate. A general large-order base finder is still missing.
The public promise is an odd balanced semiprime with `p<q<=2p`.

The saved replay checks 220 order-certificate outcomes and 108 factoring
runs on six inputs in each nominal size, seed `2026100447`. Method order
is shuffled, each input is repeated twice, and times include the full
factor call. The table is the median across input mean times:

| Nominal bits | Baseline, ms | Batched GCD, ms | Joint batching, ms |
| --- | ---: | ---: | ---: |
| 48 | 1.6705 | 1.8048 | 2.0287 |
| 64 | 19.9638 | 18.0510 | 17.8604 |
| 80 | 206.5784 | 196.3529 | 186.8431 |

These are modest practical savings against our own prototype. Smaller
inputs favour the baseline. The number of materialised rows remains at
the one-fifth target scale, so batching alone supplies no exponent change.
The factor calls receive only `N`; generated factors are used for the
final exact assertions. Fixed base 2 is not an unconditional algorithm.

### An exact sparse polynomial signal

For distinct odd primes `p<q<2p`, put `N=p*q` and `m=floor(sqrt(2N))`.
Then `q<=m<2p`, and coefficientwise reduction gives

$$
(1+X)^N\equiv 1+qX^p+pX^q
\pmod{N,\ X^{m+1}}.
$$

Modulo `p`, Frobenius gives `(1+X)^N=(1+X^p)^q`; below degree `2p`,
only `1+qX^p` survives. Modulo `q`, the corresponding truncation is
`1+pX^q`. The displayed identity follows by CRT. Thus the unknown prime
locations really are encoded sparsely. The alternating binomial prefix
then yields a single scalar observable:

$$
p+q\equiv 1-(-1)^m\binom{N-1}{m}\pmod N.
$$

Since `0<p+q<N`, its least nonnegative residue is the exact factor sum.
For `N=323`, `m=25` and the binomial residue is `35`, giving sum `36`
and factors `17,19`. The source
[probe_semiprime_sparse_signal.py](../scripts/probe_semiprime_sparse_signal.py)
checks the polynomial coefficients, scalar identity and formal derivative
on all 423 eligible odd-prime pairs below 200.

This has two exact extraction obstructions. First, the nonconstant
formal derivative is zero modulo `N`, because its coefficients are
`p*q=N`. Differentiation erases the sparse factor signal. Second,
ordinary scalar modular exponentiation includes the high-degree tail;
it does not evaluate the truncated polynomial. At `N=323`, evaluating
the truncation at `X=2` gives `73`, whereas `3^323 mod 323` is `146`.
The quotient's nilpotent variable cannot be evaluated at an ordinary
unit by a ring homomorphism. The saved naive convolution probe also
finds fully dense intermediate polynomials. Final sparsity does not
itself provide cheap construction.

### Factorial value/derivative extraction

A second exact access route keeps a product and its derivative together.
Let `F_m(X)=prod_(i=1..m)(X+i)`, `B=m!`, and `D=F'_m(0)`.
On the same balanced support, `B` contains each prime exactly once, so
`b=B/N` is a unit modulo `N`. All derivative summands except the two
prime locations vanish modulo `N`, giving

$$
D\equiv b(p+q)\pmod N.
$$

Recover `b mod N` from `B mod N^2` by exact division by `N`, then
recover the factor sum from `D*b^(-1) mod N`. A product tree of dual
numbers `(B,D)`, with multiplication `(a,b)(c,d)=(ac,ad+bc)`, evaluates
these two quantities jointly. It never divides by `B mod N`, which
is exactly the nonunit where the factor information lives.

The source
[probe_semiprime_factorial_jet.py](../scripts/probe_semiprime_factorial_jet.py)
checks 1,035 odd semiprimes with primes below 200, including squares and
unbalanced pairs: 612 use a proper factorial GCD and 423 use the trace
identity. The factor recovery does not receive the reference factors.
The batched derivative cache works, but is slower than the prime-prefix
cache below; it is an identity/extraction audit rather than the preferred
routine. This mirrors the repository's useful practice of retaining
joined product/derivative information before division, for example in
[ZetaRieszOrderedWard.lean](../RiemannGaussian/ZetaRieszOrderedWard.lean).
It does not establish that the RH identities supply a factoring oracle.

### Independent prime tables and accumulating remainders

[probe_semiprime_prime_prefix_batch.py](../scripts/probe_semiprime_prime_prefix_batch.py)
builds an independent Eratosthenes list and exact prime-product tree
through `floor(sqrt(X))`, where `X` is the public input bound.
For a query `N=p*q`, the primorial prefix through `floor(sqrt(N))`
contains the smaller prime and excludes the larger one; its GCD with
`N` gives the factor. A square also gives its prime factor.
A sparse accumulating remainder tree shares the large integer reductions
across many distinct queries. These are standard remainder-tree ideas;
see [Harvey's notes, sections 7.1 and 7.4](https://swc-math.github.io/aws/2026/2026HarveyNotes.pdf).

The saved replay checks 1,081 small semiprimes, including even inputs,
squares and unbalanced pairs, plus duplicate queries, an empty batch
and rejection of queries outside the cache bound. The timing corpus
contains 1,024 distinct 32-bit semiprimes with disjoint factors. It uses
seed `6897333`, a common public bound, shuffled method order and the
median of three repetitions. The cache is target-independent.

| Batch size | Cached query, microseconds/input | Cache plus query, microseconds/input | Existing prime-power decoder, microseconds/input |
| --- | ---: | ---: | ---: |
| 1 | 27.6570 | 5580.9550 | 48.5390 |
| 64 | 9.6074 | 96.3777 | 44.9445 |
| 256 | 7.6999 | 29.3925 | 43.8225 |
| 1024 | 5.6134 | 11.0365 | 44.1333 |

Construction took `5.5533 ms`. Stored product integers total `165,723`
bytes; that excludes Python object overhead and the sieve. The largest
batch is about four times faster than our decoder with precomputation
charged. This is not a benchmark against the fastest native factoring
software, and the small prototypes do not establish large-input scaling.

With logarithmic factors suppressed, the natural total batch cost is
`~O(sqrt(X)+B)` for `B` queries, and the amortized cost is
`~O(sqrt(X)/B+1)` per input. Reaching `X^(1/6)` this way requires roughly
`B>=X^(1/3)` inputs sharing the public bound. A single input still pays
the square-root construction/reduction cost. Storage and preparation
remain exponential in input bit length and are infeasible for RSA-size
universal tables. No generic single-input `N^(1/6)` improvement was found.

### What sparse centres and colour tables did not yet provide

[probe_semiprime_centre_compression.py](../scripts/probe_semiprime_centre_compression.py)
preserves the numerical Taylor-block experiment for
`ceil(2*sqrt(N*k))`, `r<=k<2r`, with `r=floor(N^(1/3))`, seed `600193`.
Cubic blocks of length about `2*r^(2/5)` and quartic blocks of length
about `2*sqrt(r)` need few correction descriptors in the tested inputs.
At 47 bits the quartic pass used 110 blocks and 15 exceptions instead
of 47,947 literal centres.

Those exceptions were discovered by scanning every centre. Rounding
also destroys the polynomial's exact higher-difference cancellation:
about 87% of next-order differences were nonzero in the largest quartic
probe. Neither cheap exception generation nor an implicit modular
collision-product evaluator has been proved. A heuristic one-sixth
descriptor count therefore remains a representation observation.

The same source audits precomputed unit-residue factor-sum masks.
For the tested `W=2^t`, `t=4,6,...,16`, the residue class `N=-1 mod W`
still permits exactly `W/8` sum residues. Larger tables do not remove
that density on this class. This is a result about unit residues, not
an impossibility theorem about prime pairs in a bounded input range.
Mixed wheels can improve individual classes at a larger table cost.
No cheap zeta/eta table has supplied an additional independent factor
signal; the repository's eta here is Dirichlet eta, not Dedekind eta.

### Replaying the preserved source

These five scripts are optional, guarded on import, and are not wired
into ordinary builds or CI. From `formal/`, run any of:

~~~bash
PYTHONDONTWRITEBYTECODE=1 ../.venv/bin/python -B scripts/probe_semiprime_sparse_signal.py
PYTHONDONTWRITEBYTECODE=1 ../.venv/bin/python -B scripts/probe_semiprime_centre_compression.py
PYTHONDONTWRITEBYTECODE=1 ../.venv/bin/python -B scripts/probe_semiprime_factorial_jet.py
PYTHONDONTWRITEBYTECODE=1 ../.venv/bin/python -B scripts/probe_semiprime_prime_prefix_batch.py
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python -B scripts/probe_semiprime_weighted_batch.py
~~~

The replay environment uses Python 3.10.12, gmpy2 2.3.1, NumPy 2.2.6,
SymPy 1.14.0 and mpmath 1.3.0. Timings are indicative: no CPU affinity
was imposed, and the initial independent replay jobs overlapped.
Use sequential repeats for a controlled timing comparison. All checks
reported above passed; no source edit or staging in this side project
changes the active RH work.

## 2026-10-02: cheap individual extraction and exact phase tilt

This pass charges the construction and evaluation costs to each input.
No square-root-sized universal table, known factor, totient, private local
order or separate Legendre sign is an input to the extraction functions.
Write `N=p*q` with distinct odd primes. The exponent in `N^(1/6)` refers
to numerical `N`: for a `b`-bit input it is about `2^(b/6)`, not polynomial
time in `b`. The one-fifth comparison is to the deterministic exponent
framework, rather than a claim to beat heuristic NFS or tuned native code.

### A public exponent separates the hidden local periods

For an ordinary modular unit, let

\[
g=\gcd(p-1,q-1).
\]

The identities

\[
\gcd(p-1,N-1)=\gcd(q-1,N-1)=g
\]

imply that raising the unit to `N-1` makes its two local orders divide
`(p-1)/g` and `(q-1)/g`. Those quotients are coprime. Subsequent common
prime-power projections preserve that coprimality. Neither `g` nor either
local order needs to be known to execute the projection.

This pays a concrete weakness of the previous low-order search: distinct
nontrivial local periods cannot coincide after separation. If one local
period closes before the other, the GCD is a proper factor. If both close
within the same geometric block, the product-tree descent recovers a
separating leaf. The implementation inspects the first nonunit block,
rather than accepting a shared collapse as a factor. A bounded search over
32 bases can still return `kernel-unresolved`; it does not assume a small
nontrivial witness always exists.

[SemiprimeOrderSeparation.lean](../RiemannGaussian/SemiprimeOrderSeparation.lean)
now proves the cardinality/GCD identities, coprime projected orders, their
preservation under further powers, a bounded separating witness, its GCD
consequence and the exact geometric-cover indexing. This optional module
is outside the RH umbrella. It does not formally verify the whole Python
program or its bit complexity.

The public budget is

\[
B=\lceil N^{1/6}\rceil,\qquad
D=\max(1,\lfloor B^2/c\rfloor).
\]

The pass builds its own primes through `B`. For each prime `ell<=B`, it
projects by the largest power of `ell` at most `floor(sqrt(N))`, not just
the largest power below `B`. Thus it removes all small-prime powers from
the smaller factor's remaining order. Checking the GCD after every power
preserves a factor found during the projection.

The final polynomial has about `sqrt(D)` roots and is evaluated at about
`sqrt(D)` geometric points. Their differences cover every positive period
through `D` (with a slightly larger exact block endpoint). With fast integer
and polynomial arithmetic, construction, projection, evaluation and GCD
descent have soft `O(B)` bit work, with logarithmic factors in `N` suppressed.
This operation analysis is separate from the Lean structural proof.
Success is guaranteed for a nontrivial separated witness when at least one
remaining private period lies in that cover. Otherwise the pass reports
`certified-large-order`: both private periods exceed the covered endpoint.
It does not hide failure inside an unproved coverage hypothesis.

[probe_semiprime_single_extraction.py](../scripts/probe_semiprime_single_extraction.py)
implements the partial pass and a hybrid using our earlier weighted search
as fallback. The fallback keeps its balanced-input and fixed-base
limitations; this is not an unconditional factoring library.

### Fresh single-input timing, with failure and fallback charged

[semiprime-single-extraction-audit.json](semiprime-single-extraction-audit.json)
contains 32 fresh balanced inputs at each nominal size, seed `2026100331`.
The fixed divisor `c=16` was chosen after a separate small exploratory
budget scan with seed `2026100251`. Complete method calls, including each
input's sieve, are timed in shuffled order for three repetitions. There
is no cross-input cache. Known factors construct and verify the corpus;
they are not passed to recovery. Every returned factor was verified.

| Nominal bits | Partial pass successes | Weighted total, ms | Hybrid total, ms | Total speedup |
| --- | ---: | ---: | ---: | ---: |
| 48 | 13/32 | 60.3940 | 54.7768 | 1.103x |
| 64 | 19/32 | 732.3646 | 390.6287 | 1.875x |
| 80 | 20/32 | 8145.0112 | 3600.2575 | 2.262x |

At 48 bits the hybrid median was worse, `2.0994` versus `1.8120` ms, even
though its total was slightly better. Median improvements at the larger
sizes are strongly affected by the partial pass solving over half the
inputs, so the total-corpus comparison is the clearer aggregate measure.

A second fresh corpus, seed `2026100461`, contains 24 inputs per size.
Its scalar-hybrid total speedups were `1.032x`, `1.107x`, `1.781x` at
48, 64, 80 bits respectively. Hit rates and benefits vary materially by
corpus. Neither replay establishes a limiting success probability or a
generic exponent improvement. These are API timings against our own
Python weighted prototype, not the best classical factoring software;
startup is excluded, and no CPU affinity was imposed.

### Quadratic colour: use the public product of the private signs

In the quadratic algebra `(Z/NZ)[sqrt(D)]`, use a norm-one unit. Its local
orders divide

\[
A=p-\epsilon_p,\qquad B_q=q-\epsilon_q,
\qquad \epsilon_p=\left(\frac Dp\right),\quad
\epsilon_q=\left(\frac Dq\right).
\]

Only their product is needed by the separator:

\[
\sigma=\operatorname{Jacobi}(D,N)=\epsilon_p\epsilon_q,
\qquad E=N-\sigma.
\]

For all four sign patterns, exactly

\[
\gcd(A,E)=\gcd(B_q,E)=\gcd(A,B_q).
\]

Raising the norm-one unit to `E` therefore makes its private local orders
coprime too. `colour_gcd_separator` and
`coloured_projected_orders_coprime` formalize the signed cardinality
arithmetic and the group conclusion, assuming the local order divisibility.
The identification of those cardinalities with the quadratic Legendre
cases uses the standard finite-field fact; it is checked in the exact
reference probes, not separately formalized here.

The norm-one starting element is the input-specific Cayley quotient

\[
\frac{a+\sqrt D}{a-\sqrt D}
=\frac{a^2+D}{a^2-D}+\frac{2a}{a^2-D}\sqrt D.
\]

A nonunit denominator supplies a GCD factor. The code checks parameter
values `1..32` and reports failure if they all lie in the separator kernel.
Its default colour scan selects `Jacobi=-1` and therefore `E=N+1`; an
explicit public discriminant also tests the `Jacobi=+1`, `E=N-1` case.
Equal mixed-sign cardinalities force twin factors; their product plus one
is a square, which the public preliminary square test pays exactly.

[probe_semiprime_quadratic_extraction.py](../scripts/probe_semiprime_quadratic_extraction.py)
implements both split and nonsplit quadratic arithmetic with exact modular
products and a geometric order cover. `quadratic_norm_one_collision`
proves that the norm detects equality between norm-one elements over either
local quadratic algebra, including the split case. This restriction matters:
zero norm does not mean zero for arbitrary elements of a split algebra.

Five safe-prime controls, from `59*83` through a nominal 80-bit input,
all fail the scalar full-budget pass but are factored by colour at the
same `c=1` budget. This is additional coverage, not a universal guarantee.
On the fresh 72-input timing corpus the cheaper colour pass (`c=256`)
added only one hybrid success per size, and increased total hybrid runtime.
It remains optional rather than becoming a recommended default.

### Exact phase tilt removes a convolution channel

The new RH theorem in
[ZetaRieszComplexProjection.lean](../RiemannGaussian/ZetaRieszComplexProjection.lean)
motivated a specific extraction question: can a common known phase be
removed before projecting the entire collision product? The factoring
analogue is algebraic; a real one-sided inequality from the RH theorem
cannot itself be used as a modular divisibility detector.

Let `beta` be the projected norm-one element, `alpha=beta^2`, and choose
an even baby width `b`. With

\[
P(X)=\prod_{i=0}^{b-1}(X-\alpha^i),
\]

the whole geometric evaluation has the exact known phase

\[
P(\alpha^{bj})
=\beta^{b^2j+b(b-1)/2}\,c_j,
\qquad \overline{c_j}=c_j.
\]

Indeed each difference factors as

\[
\beta^{2e}-\beta^{2i}
=\beta^{e+i}
  (\beta^{e-i}-\beta^{i-e}).
\]

The parenthesized factor is anti-selfadjoint; an even product is
selfadjoint. This preserves every collision and its cross terms. The
Lean lemmas `squared_collision_phase`,
`inverse_difference_anti_selfadjoint`,
`even_collision_product_selfadjoint`, `product_collision_phase`,
`quadratic_selfadjoint_im_zero` and `quadratic_phase_recover` check the
algebra underlying the projection.

The Bluestein convolution also has a known phase. We compute only its
real coordinate, using two scalar convolutions instead of three, and
recover the real scalar by dividing out that phase coordinate. All
divisions are charged using one input-specific batch inversion. A nonunit
coordinate gives a proper GCD factor; an exceptional zero coordinate has
an exact full-coordinate fallback. Thus the optimization does not silently
project away a factor or use a floating-point phase.

This is a useful implementation connection to the repo's phase-preservation
principle. Reciprocal symmetry and two-convolution `p+1` evaluation already
appear in [Montgomery–Kruppa's primary stage-two presentation](https://antsmath.org/ANTSVIII/files/kruppa.pdf).
We are not claiming a first-ever phase-based factoring algorithm.

[semiprime-quadratic-extraction-audit.json](semiprime-quadratic-extraction-audit.json)
records the comparison on the same fresh 72-input corpus:

| Nominal bits | Quadratic total, ms | Tilted quadratic total, ms | Runtime reduction |
| --- | ---: | ---: | ---: |
| 48 | 34.5341 | 34.5653 | -0.091% |
| 64 | 264.5777 | 260.0765 | 1.701% |
| 80 | 1592.7923 | 1557.4320 | 2.220% |

These small differences need larger controlled repeats before a robust
runtime claim. The exact convolution-count reduction is stronger evidence
than a small timing difference. The total complexity remains soft `N^(1/6)`
for the partial pass; this does not change the coverage exponent.

### Exact controls identify the remaining information gap

[probe_semiprime_order_controls.py](../scripts/probe_semiprime_order_controls.py)
and [semiprime-order-separation-audit.json](semiprime-order-separation-audit.json)
preserve the regressions, larger controls, dependency hashes and focused
Lean compilation. The scalar checks include 3,828 local-order comparisons,
1,035 semiprime projection cases, 220 geometric-cover tests, and 567 exact
folded-Frobenius identities. Quadratic checks include naive-convolution and
Horner comparisons, 108 exact real-tilt regressions, and 990 distinct odd
semiprime cases for both the original and tilted/same-colour variants.

Two more cheap signal candidates failed their intended extraction test:

- For `0<k<min(p,q)`, every `binomial(N,k)` is zero modulo `N`.
  `low_choose_dvd_semiprime` proves this exactly. A shorter nilpotent
  binomial prefix therefore has no factor-sensitive nonconstant residue.
- The reciprocal folded-Frobenius scalar can be evaluated in `O(log N)`
  modular operations and satisfies its exact Laurent identity. The tested
  fixed values `t=2..14` factored none of the 96 fresh inputs. This is a
  finite negative probe, not an impossibility theorem for all Frobenius
  tests or all parameters.

The more decisive coverage counterexample is

\[
N=6827\cdot7187=49065649,\quad B=20,\quad D=400.
\]

Its four cardinalities are

\[
p-1=2\cdot3413,\quad p+1=12\cdot569,\qquad
q-1=2\cdot3593,\quad q+1=12\cdot599.
\]

All four displayed rough factors are prime and exceed `400`. The scalar
pass and all 16 explicit colours return `certified-large-order` at the
full `c=1` budget. Reference exponentiation verifies the exact private
orders after projection. `four_rough_period_control` checks the prime,
factorization and budget arithmetic in Lean. Its statement is deliberately
a finite structural control, not a lower bound for arbitrary algorithms.

The same pattern survives on larger independently generated controls,
seed `2026100541`:

| Input | Public `B` | Covered `D=B²` | Colour outcomes |
| --- | ---: | ---: | --- |
| `2346272483 * 3649327547` | 1431 | 2047761 | All 16 private-order covers fail |
| `661911275027 * 720957498683` | 8840 | 78145600 | All 16 private-order covers fail |

Here both primes are of the form `12r-1` with `r` and `6r-1` prime.
Consequently changing colour merely selects between two long private
prime periods on each leg; it does not create a short period. Generating
these controls uses known reference factors, but recovery receives only
their product. No claim about infinitely many such prime patterns is made.

The next scaling improvement must extract something from long rough
periods, or provide a new cheaply constructed cover of them. Improving the
phase projection alone cannot turn this bounded cover into a generic
one-sixth algorithm. If a remaining order has two rough factors, the
ordinary GCD equality detector only sees closure of their product, not
closure of one private order factor; those factors also need a new signal
or a cheap joined evaluation. This is the sharply defined open target.

The literature's [conditional one-sixth framework](https://arxiv.org/html/2511.10851v1)
requires efficiently prefactored structured difference covers. Our colour
signal and phase projection do not establish that hypothesis.
[The arithmetic-progression obstruction](https://arxiv.org/html/2608.06681)
rules out a particular one-dimensional proposal, not every higher-rank
cover. There is no justified generic one-sixth result here yet.

### Optional replay commands

From `formal/`, the focused validation and exact controls are:

~~~bash
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python -B scripts/probe_semiprime_order_controls.py --check-lean
PYTHONDONTWRITEBYTECODE=1 ../.venv/bin/python -B scripts/probe_semiprime_single_extraction.py hybrid 4897
PYTHONDONTWRITEBYTECODE=1 ../.venv/bin/python -B scripts/probe_semiprime_quadratic_extraction.py factor 4897 --order-divisor 1 --tilt
~~~

The saved timing replays are reproducible with:

~~~bash
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python -B scripts/probe_semiprime_single_extraction.py benchmark --bits 48 64 80 --cases 32 --repeats 3 --seed 2026100331 --order-divisor 16
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python -B scripts/probe_semiprime_quadratic_extraction.py benchmark --bits 48 64 80 --cases 24 --repeats 3 --seed 2026100461
~~~

All new scripts are guarded and optional, with no CI or RH-build integration.
Only the side-project sources, note and audits are staged for preservation.

## 2026-10-02: extracting from long periods without a quadratic grid

Artifacts:

- [Public-input extractor and fast multipoint implementation](../scripts/probe_semiprime_long_period.py).
- [Reference-only signal probes and focused proof replay](../scripts/probe_semiprime_long_period_signals.py).
- [Control recovery audit](semiprime-long-period-audit.json),
  [fresh timing corpus](semiprime-long-period-benchmark.json), and
  [signal/validation audit](semiprime-long-period-signals.json).
- [Checked Lean algebra/witness lemmas](../RiemannGaussian/SemiprimeLongPeriodExtraction.lean),
  outside the RH umbrella.

### A signal beyond the linear order cover

Take the same public quadratic colour `D=-1`, Jacobi separator and smooth
projection used by the earlier pass. Write the resulting norm-one element
as `alpha`, and set `B=ceil(N^(1/6))`. The new pass compares the scalar
traces of

$$
\alpha^{D_6(i,1)},\quad 0\le i<B,
\qquad
\alpha^{D_6(Bj,1)},\quad 1\le j\le B,
$$

where `D_6(x,1)=x^6-6x^4+9x^2-2`. Equal traces detect equal **or inverse**
norm-one elements. This remains valid on both split and nonsplit local
quadratic algebras; no hidden Legendre symbol enters recovery.

The exact identity, now checked in Lean, is

$$
D_6(x,1)-D_6(y,1)
=(x-y)(x+y)(x^2-xy+y^2-3)(x^2+xy+y^2-3).
$$

On the 64-bit control the public algorithm finds `j=477`, `i=1427`,
`B=1431`. Its recovered factor is `2346272483`. **After recovery**, the
reference check identifies the local order as `195522707`, while the old
cover reaches only `2047761`. Put `x=477*1431`, `y=1427`. Then

$$
x^2-xy+y^2-3=2378\cdot195522707,
\qquad x+y<195522707.
$$

The quadratic factor supplies a multiple of the private period; neither
linear gap does. The algorithm never receives that period. Its actual
trace residues give the directly verified certificate

$$
\gcd(6820094445240089472-237621801882584593,\,
8562316804979989201)=2346272483.
$$

This is extraction before enumerating the long period, not an order oracle.
The earlier smallest rough control is also recovered. The 80-bit control
still defeats this particular degree-six map.

### Paying for the nonlinear points

For a fixed-degree integer polynomial `f`, generate `alpha^f(i)` using its
finite-difference table. The update

$$
\alpha^{v_i}\alpha^{v_{i+1}-v_i}=\alpha^{v_{i+1}}
$$

uses only a fixed number of group multiplications per new point. All initial
differences and their powers are computed for the input. Negative exponents
use norm-one conjugation. The implementation reduces each quadratic point
to one scalar trace **before** constructing the collision polynomial.

Geometric chirp evaluation no longer applies to these points. The new
monic product/remainder tree evaluates them using exact GMP polynomial
products and Newton reciprocal iteration. A monic reversed polynomial has
constant coefficient one, so this needs no division by an unknown nonunit
in `Z/NZ`. The algorithm materializes `O(B)` points, not `B^2` comparisons;
the polynomial work is softly linear in `B`. Its logged convolution and
coefficient counts include the full query-specific construction.

These techniques have classical precedents: the
[Brent–Kruppa–Zimmermann account](https://maths-people.anu.edu.au/~brent/pd/rpb264.pdf)
describes fast polynomial continuation, power/Dickson maps and ECM. The
contribution here is their concrete integration with our local-order
separator, scalar trace folding and audited controls. We do not claim to
have invented Dickson continuation or ECM.

### Cheaply replacing a resistant group

`curve_extract` constructs a public Suyama Montgomery curve, starting at
`sigma=6`, and projects away primes through `B`. It compares x-coordinates
of `[i]Q` and `[Bj]Q`: equality means `[Bj-i]Q` or `[Bj+i]Q` is zero locally.
The same monic multipoint evaluator batches the test. Coordinate inversions
are batched, with nonunit GCDs checked first. Curve construction, projection,
coordinates, products and factor descent are charged to the input.

This changes the local group; it does **not** decode the original long
`p±1` periods. On all three controls the first public curve succeeds:

| Input | Old linear cover | Dickson-six result | Curve factor | Verified local annihilator |
| --- | ---: | --- | ---: | ---: |
| `6827*7187` | 400 | factor 6827 | 6827 | 191 |
| `2346272483*3649327547` | 2047761 | factor 2346272483 | 3649327547 | 1357673 |
| `661911275027*720957498683` | 78145600 | no collision | 661911275027 | 20873 |

The last column is verified only after GCD recovery, not supplied to the
search. No curve-order oracle, factor-indexed table, or list of all primes
through `B^2` is used.

The target batches grow as `1,2,4,8,...`, reusing the baby product. This
allows an early hit while retaining only logarithmically many degree-`B`
reductions in the worst case. Fixed-size repeated batches would silently
restore quadratic cost and are deliberately avoided. The 80-bit control
needs only three target coordinates in two batches; its exploratory time
drops from about 0.97 s for the full target cover to 0.24 s. That single
timing motivated, but does not replace, the fresh corpus below.

### Fresh corpus and negative probes

Seed `2026100663`; 16 fresh balanced inputs per nominal size; three
repetitions in randomized method order. Each timing includes the complete
input-specific call. Imports, sample generation, reference verification
outside the call, and JSON are excluded. Every returned factor is checked
by exact divisibility. The one-curve test uses the same public `sigma=6`
on every input. There are no retained cross-input prime or curve tables.

| Nominal bits | Same-colour linear hits | Dickson-six hits | One-curve hits | Linear total ms | Dickson total ms | Staged curve total ms | Full curve total ms |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 48 | 14/16 | 16/16 | 14/16 | 155.5 | 197.8 | 99.4 | 171.6 |
| 64 | 12/16 | 14/16 | 15/16 | 1261.5 | 1793.8 | 896.4 | 1499.5 |
| 80 | 13/16 | 14/16 | 15/16 | 10058.6 | 15870.9 | 7373.4 | 14264.2 |

The nonlinear map adds five hits but is slower in total than the linear
pass. Staging improves the curve totals by `1.727x`, `1.673x`, `1.935x`,
with unchanged hit counts. No tuned native ECM comparison was performed.
Single-input failure is explicit; a fixed curve or fixed map is not
guaranteed to factor every semiprime.

Public exponents `N^d-1` for `1<=d<=64` produce no factors on these controls.
Reference-only alias probes find no power-map hits through tested degree
60 on the two larger controls; the Dickson-six quadratic hit distinguishes
the 64-bit case. Neither power nor tested Dickson maps hit the 80-bit
control. The diagnostic tables contain private periods for explanation;
the separate recovery algorithms never consult them.

There is also an exact inexpensive gap encoding for every unit `a`:

$$
a^{N-1}+a^{-(N-1)}
\equiv a^{q-p}+a^{-(q-p)}\pmod N.
$$

Lean proves the two local exponent identities behind it. The trace is cheap
to obtain, but decoding a generic large gap remains expensive. A short-gap
promise also benefits classical Fermat factoring, so this alone is not a
new generic speedup.

Validation independently compares 175 monic remainders with elementary
division, 625 multipoint values with Horner evaluation, 3335 finite-
difference powers with direct powers, 638 local trace collisions, and 948
Montgomery multiples with an independent affine group law. All pass.
The focused Lean file compiles without warnings or admissions. Its lemmas prove
the algebra and integer witnesses, not the entire Python implementation,
its bit complexity, a hit-rate theorem, or generic one-sixth factoring.

### What is still missing

The quadratic alias is real information that the original linear cover
missed. A universal cheap cover of long periods is still unproved. Fixed
nonlinear maps can fail; increasing their number must be charged. Changing
curves is a useful classical escape, but a bounded curve pass likewise
has no unconditional one-sixth coverage guarantee. The research target
remains a provable improvement in coverage per unit of extraction work,
rather than another cheaply encoded quantity with an expensive decoder.

Optional replay, from `formal/`:

~~~bash
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python -B scripts/probe_semiprime_long_period_signals.py --check-lean
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python -B scripts/probe_semiprime_long_period.py controls
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python -B scripts/probe_semiprime_long_period.py benchmark --bits 48 64 80 --cases 16 --repeats 3 --seed 2026100663
PYTHONDONTWRITEBYTECODE=1 ../.venv/bin/python -B scripts/probe_semiprime_long_period.py factor 8562316804979989201
~~~

## 2026-10-02: complex null corrections and cheap exponential orbits

Artifacts:

- [Public-input phase/orbit extraction](../scripts/probe_semiprime_complex_extraction.py).
- [Exact checks and selected challenge replay](semiprime-complex-extraction-audit.json).
- [33 checked algebra/witness theorems](../RiemannGaussian/SemiprimeLongPeriodExtraction.lean),
  including the new correction and orbit identities, outside the RH build.

### What transfers from the RH null correction

The RH theorem `ZetaRieszComplexNullFloor.increment_coherent_zero` cancels
a flat contribution when its phase is collinear with a common moment.
Its cross-phase algebra transfers to modular quadratic rings. For a known
norm-one phase `phi` and a scalar collision value `v`, write `F=phi*v`.
Then exactly

$$
\phi_{\rm im}F_{\rm re}-\phi_{\rm re}F_{\rm im}=0,
\qquad
\phi_{\rm re}F_{\rm re}+\phi_{\rm im}F_{\rm im}=v
$$

in the Gaussian modular ring. The first identity holds without a norm
assumption; the second uses `norm(phi)=1`. Thus a perpendicular correction
annihilates **every** scalar amplitude, including the amplitude whose GCD
would reveal a factor. `coherent_null_gcd_is_full` proves its GCD is always
the entire modulus. It is not an additional separating signal. No ordered
real inequality from the RH floor is applied to `Z/NZ`.

Rotating **before** projecting changes the collision itself. For norm-one
`kappa,x,y` over either split or nonsplit local quadratic algebras,

$$
\operatorname{Re}(\kappa x)=\operatorname{Re}(\kappa y)
\iff x=y\ \text{or}\ \kappa^2xy=1.
$$

When `kappa=alpha^c`, the second channel is

$$
f(i)+f(Bj)+2c\equiv0\pmod{\operatorname{ord}(\alpha)}.
$$

The equal channel is unchanged. The implementation constructs and tests
the rotated scalar points without knowing either local order. Each added
phase pays for its additional polynomial tree and evaluation; it is not a
free new search dimension. The fixed phases `-13,+15` were calibrated on
a previous control, and the replay identifies that calibration explicitly.

Pure imaginary rotation is less useful here: after removing the 2-part,
the projected local order is odd. Its subgroup cannot contain `-1`.
`imaginary_rotation_odd_order_inverse_impossible` proves that a phase
`i*alpha^c` cannot provide the inverse channel on that subgroup. Imaginary
projection alone consequently loses the existing folded channel rather
than extending it on that odd-order leg.

A second exact limitation concerns choosing an apparently optimal phase.
Both degree-six exponents `e,f` are even, so the public choice
`c=-(e+f)/2` forces `kappa^2*alpha^e*alpha^f=1` globally. The rotated traces
then agree modulo both prime factors, and their GCD is `N`. The new replay
checks this on every challenge. `global_inverse_alignment_gcd_is_full`
proves it over the composite modular ring. A separating phase must expose
a relation on one hidden leg without enforcing the same relation globally.

### Exponentially large exponents with linear point-generation work

Compare traces of `alpha^(a^i)` and `alpha^(b^j)`, with `1<=i,j<=B` and
public distinct integers `a,b>=2`. Each point is generated from the
previous point by the exact recurrence

$$
\bigl(\alpha^{a^i}\bigr)^a=\alpha^{a^{i+1}}.
$$

There is no need to construct the integer `a^i` or to perform a fresh
powering using its exponentially large value. Constant bases need `O(B)`
group multiplications; the public bases `N,N+1` need `O(B log N)`.
One baby product and doubling target batches keep polynomial evaluation
softly linear in `B`. Indices zero are excluded to avoid the vacuous
identity `a^0=b^0=1`. Shared full-modulus collisions are skipped so they
cannot hide a later separating target.

On the 64-bit four-rough control, the public bases `N,N+1` recover factor
`3649327547` with baby index `121`, target index `34`. Only after recovery
can the private-period diagnostic describe this as

$$
N^{121}\equiv(N+1)^{34}\pmod{304110629}.
$$

The actual algorithm computes group points and a GCD; it does not receive
this modulus. This extracts a new collision from a long period at bounded
work. It is not a deterministic cover of every period.

### General structure behind the recoveries

The new `dickson_collision_lift` theorem applies to **every degree**, not
just the degree-six example. For nonzero lifted units `v,w`,

$$
D_d(v+v^{-1},1)=v^d+v^{-d},
$$

and exactly

$$
D_d(v+v^{-1},1)=D_d(w+w^{-1},1)
\iff (v/w)^d=1\ \text{or}\ (vw)^d=1.
$$

Thus the map is a power operation followed by reciprocal identification.
For a **prime** remaining period `r`, a trace lift lies in either the
split torus of size `r-1` or the nonsplit norm-one torus of size `r+1`.
Roots of unity in both tori create the extra fibres, explaining why both
`gcd(d,r-1)` and `gcd(d,r+1)` enter. Classical
[Dickson value-set work](https://doi.org/10.1016/0022-314X(88)90006-6)
studies this structure; the contribution here is a checked connection to
our actual collision extraction. The hidden period `r` is not supplied
to the algorithm.

The finite-field probe enumerates 143 complete small prime fields and
checks 74,924 lift identities. For primes `r=5 (mod 6)`, degree-six
Dickson folding has about twice the full-field collision probability of
the ordinary sixth-power map. For `r=1 (mod 6)`, it has about two-thirds.
The successful 64-bit control has period `195522707=5 (mod 6)`, where the
nonsplit torus supplies a channel the power map misses. These are exact
full-field counts, not a coverage theorem for the short structured grids.
The actual same-sign witness has quadratic characters `-1,-1` for its
two trace lifts, recorded separately in the reference-only audit.

There is an important scaling limit. `dickson6_fiber_card_le` proves that
each degree-six output has at most six preimages over any field.
`dickson_nested_fold` proves that nesting degrees `a,b` is just degree
`a*b`. Nesting does not supply independent free layers. In the current
finite-difference point generator, degree `d` takes `d` group updates per
point. Any proposal for a growing fold must reduce this charged cost or
exploit additional arithmetic structure, rather than infer a new exponent
from one unusually long-period hit.

There is also a universal restriction on the remaining order geometry.
For the smaller factor `p<=q` and `B=ceil(N^(1/6))`,

$$
p+1\le B^3+1.
$$

After removing every prime through `B`, the remaining local order has
**at most two prime factors, counted with multiplicity**: three factors
greater than `B` would have product at least `(B+1)^3>B^3+1`.
`smaller_factor_group_budget` and `rough_order_prime_count_le_two`
formalize these arithmetic bounds. They assume the stated roughness of
the residual order; they do not make the hidden order readable.

Consequently the unresolved smaller-prime orders have only two shapes:

1. One prime `r>B^2`.
2. Two rough primes `r1,r2>B`, including a repeated prime, whose product
   exceeds `B^2`. Each individual factor is below `B^2`, as proved by
   `two_rough_factors_lt_square`.

This is a concrete commonality to exploit. In the second case, finding
closure of one order factor is insufficient: the current GCD needs the
whole local element to close. A new partial-order extraction identity
would have to bridge that difference at charged one-sixth cost.

The reference-only audit of the smaller `p-1,p+1` cardinality envelopes
in the saved 48-input corpus finds 41 single-long-prime envelopes, 10
two-rough-factor envelopes, 41 inside the old cover and 4 completely
cleared. There are no rough-square envelopes in that corpus. Actual
element orders can be proper divisors of these envelopes. Recovery does
not consult the reference factorizations.

### Selected challenges and their cost

The four challenges below are the Dickson failures already present in the
saved 48-input corpus. This is a selected regression, not a fresh unbiased
benchmark. Recovery receives only `N` and fixed public parameters.

| Input `N` | Phases `0,-13,+15` | Orbits `2,3` | Orbits `N,N+1` |
| --- | --- | --- | --- |
| `6015700395832288409` | no hit | no hit | factor `2278586117` |
| `10457652412285181353` | factor `2755464161` at `c=15` | factor `2755464161` | no hit |
| `681744979629536288452009` | no hit | no hit | not tested |
| `387911014119558410533909` | factor `588556368311` at `c=-13` | no hit | not tested |

The new scalar trace tests verify their equal/inverse channels after
factor recovery. Exact single-call observations were about 320 ms for
the adjacent-base recovery in the first row, 87 ms for the small-base
orbit recovery in the second, and 1.71 s for the phase recovery in the
fourth. They include setup, projection, points and polynomial work. These
are not timing guarantees or comparisons with tuned classical software.

The 80-bit four-rough control still defeats all three phases and both
small-base orbit pairs `2,3` and `2,5`. Reference-only probes also found
no inverse-channel hit among 63 predetermined phase exponents, and no
small/adjacent-base orbit hit on either of its two nonsplit rough periods.
Neither reference test is used by recovery. We do not infer an infinite
family or a lower bound for arbitrary factoring algorithms.

Independent exhaustive local checks cover 33,256 rotated trace identities,
including split quadratic algebras. A shared-target regression confirms
the full-modulus collision is skipped before a later GCD of 5 is recovered
modulo 35. Together with the long-period validations, these check the
implemented algebra. The 33 Lean theorems compile without admissions;
they do not yet verify the full Python execution or bit-operation cost.

### The guaranteed one-sixth proof obligation

For every pair of primes, including equal primes, the desired algorithm
must return `1<d<N`, `d|N`, and have charged bit-operation cost at most

$$
C N^{1/6}(\log N)^e
$$

for fixed constants `C,e`, apart from finitely many small inputs. There
must be no assumption about short orders, prime smoothness, a lucky
curve, or a factor-sensitive lookup table. A randomized formulation with
this guarantee on **every run** must cover every allowed random choice;
an expected success probability is insufficient.

The present covers have bounded work but explicit budget exhaustion.
Further numerical successes would not discharge the universal coverage
quantifier. The next theorem must control all possible remaining local
orders with a cheaply constructible cover and guarantee a separating
collision, then tie the cost bound to the actual execution. Enlarging the
phase/map budget is valid only when that enlarged cost is charged.

The literature offers relevant infrastructure, but not a supplied proof
of this target. [Harvey–Hittmeir (2026)](https://arxiv.org/abs/2601.11131)
deterministically produce an element of order greater than `D`, or a
factor, in roughly `sqrt(D)` work without the older lower restriction on
`D`. At `D=N^(1/3)`, that is compatible with a one-sixth budget. It removes
base construction as an asymptotic bottleneck; it does not decode a long
local order. This subroutine is not implemented here yet.

[Umans–Wang](https://arxiv.org/abs/2511.10851) give a conditional
one-sixth route using a structured, efficiently prefactored divisor cover.
The missing cover cannot be inserted as an assumption and called our
desired universal theorem. Our exponential orbits illustrate cheap access
to large exponents, but their observed misses leave the covering theorem
open. Their success cases alone do not establish the conjectured structure.

Optional replay, from `formal/`:

~~~bash
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python -B scripts/probe_semiprime_complex_extraction.py probe
PYTHONDONTWRITEBYTECODE=1 ../.venv/bin/python -B scripts/probe_semiprime_complex_extraction.py factor 10457652412285181353 --algorithm orbit --bases 2 3
/home/dbsanfte/.elan/bin/lake env lean RiemannGaussian/SemiprimeLongPeriodExtraction.lean
~~~

## October 2, 2026: partial rough-order projection and indexed Lucas maps

This pass tests the two remaining extraction targets: one long prime
period, and a period with two rough factors. The implementation is
[probe_semiprime_rough_projection.py](../scripts/probe_semiprime_rough_projection.py),
the complete replay is
[semiprime-rough-projection-audit.json](semiprime-rough-projection-audit.json),
and the class-specific proofs are in
[SemiprimeRoughProjection.lean](../RiemannGaussian/SemiprimeRoughProjection.lean).
Recovery receives only `N` and fixed public parameters. Private factors
and periods occur only in reference diagnostics or explicitly structured
corpus generation.

### Closing one component, without waiting for the product

Write `B=ceil(N^(1/6))`. Form the public exponent

$$
M_2=\prod_{i=1}^B(i^2+1)|i^2-2||i^2-3||i^2-5|.
$$

For a prepared local element whose order divides `r*t`, the exact
group identity is

$$
r\mid M_2\quad\Longrightarrow\quad
\operatorname{ord}(a^{M_2})\mid t.
$$

Thus removing one component can bring the remaining order into the
linear collision cover even when the original order was outside it.
This includes repeated factors `r=t`; the method does not need the
period to be squarefree. The Lean class theorem retains the explicit
small-root condition `r | i^2+1`, `1<=i<=B`, coprimality of the prepared
local orders, and a nontrivial surviving other leg. It does not assume
that every rough prime has such a root.

There are `4B` positive leaves, and Lean proves

$$
M_2\le(B^2+5)^{4B}.
$$

Its complete exponent therefore has `O(B log B)` bits. The implementation
builds a balanced integer product and charges its construction and the
entire modular exponentiation. In split colour `D=1`, an exact character
identity permits native scalar modular powering; both coordinate
recovery and the required inverses are explicit in the proof. If both
local legs close, a balanced prefix descent attempts to separate them;
a shared closing leaf is reported rather than called a factor.

Two additional saved recoveries illustrate actual partial extraction:

| Input `N` | Recovered factor | Initial local order | Order after projection |
| --- | --- | --- | --- |
| `6327961582282610561` | `2228299919` | `3413*25111` | `3413` |
| `513699397734689750848799` | `552807545971` | `18869*976571` | `976571` |

The first uses `924^2-2`, which contains `25111`; the second uses
`5647^2+1`, which contains `18869`. These private order explanations are
computed after recovery. On the structured repeated-order control
`N=232567537276409921`, the local order `8101^2` reduces to `8101` because
`90^2+1=8101`. The original linear attempt misses it.

A cubic continuation uses the fixed leaves `|i^3-2|`, `|i^3-3|`,
`|i^3-5|`, and `i^3+2`. Lean proves closure on the explicit cubic-root
class. It neither asserts a root for arbitrary primes nor conceals a
larger grid. A fresh additional recovery is
`N=9609119139727769923`: the linear, quadratic, and default Lucas attempts
miss, but the cubic projector factors out `2523901547`. The reference
local order is `11093*113761`; `1345^3-5` removes `11093`, leaving `113761`
inside the linear cover. The other local order remains the prime
`475906001`.

### Cheap growing indices and coherent-root extraction

For a fixed seed `s`, let `e_i=D_i(s,1)` be the Dickson/Lucas sequence.
Instead of materializing its exponentially large integer values, generate
the group sequence by

$$
g_0=a^2,\qquad g_1=a^s,\qquad
g_{i+2}=g_{i+1}^{s}g_i^{-1}.
$$

Lean proves `g_i=a^(e_i)`. With fixed seeds, generating each next point
requires a bounded number of group operations. This supplies cheap
access to large exponents, but not universal collision coverage. The
default pair is `5,7`; the identity `D_i(7,1)=D_(2i)(3,1)` also demonstrates
why some apparent aliases are globally coherent and yield no factor.

The saved nominal 64-bit control
`N=8562316804979989201` is recovered using this recurrence. Its recovered
factor `3649327547` has actual projected prime period `1824663773`, about
891 times the old `B^2` cover. This is an individual long-prime recovery,
not a general 891-fold speedup.

Two exact extraction improvements preserve information lost by scalar
trace folding. If a shared trace combines equality on one local leg
with inversion on the other, imaginary differences or sums can still
yield a proper GCD. Globally identical scalar roots are deduplicated;
at most four distinct norm-one representatives share a trace for an odd
squarefree semiprime. When a target equals one global root, evaluate

$$
F'(t)=\prod_{r\ne t}(t-r)
$$

to remove that coherent factor while retaining additional local
collisions. Lean proves the polynomial identity over a commutative ring,
without a field assumption. This avoids repeatedly scanning an entire
list of coherent roots.

### Replay and limitations

The final replay uses fresh seed `2026100273`, with eight balanced inputs
of each exact size 48, 64 and 80 bits. Map constants and default Lucas
seeds were fixed before generating that corpus. The combined stopping
policy was assembled after the individual-method replay, so its result
is not an independently held-out portfolio evaluation. Each actual
combined run charges all attempted preparation and extraction work,
stopping at the first proper factor.

| Population | Cases | Linear | Quadratic projection | Lucas `5,7` | Actual combined |
| --- | --- | --- | --- | --- | --- |
| Structured declared classes | 9 | 0 | 6 | 1 | 9 |
| Saved two-rough cardinality envelopes | 10 | 7 | 9 | 6 | 9 |
| Saved four-rough controls | 3 | 0 | 0 | 1 | 1 |
| Fresh balanced inputs | 24 | 18 | 20 | 13 | 23 |

The combined order is linear, quadratic, Lucas, cubic. Standalone cubic
attempts recover all three constructed cubic controls. Other combined
recoveries may stop before cubic; standalone cubic hit rates are not
inferred for those rows. The remaining fresh miss is
`N=9710106156230271983`, whose two actual projected periods are the primes
`442912871` and `913470307`. The saved two-factor population also retains
one miss, `N=380307690410407004392769`, with actual local orders
`95971*1012513` and `65229376777`.

Timings are single full calls with warm imports in a shared environment,
including setup, projection, points and polynomial work. Across the 24
fresh inputs, the combined calls total about 8.82 seconds, compared with
7.86 seconds for linear alone: the added recoveries do not establish an
overall runtime improvement. There is no tuned classical comparison.
The JSON preserves corpus, outcomes, counters, timing protocol and
source hashes.

### Why the nominal 80-bit control defeats these maps

The deliberately four-rough control is

$$
N=477209897193541203289441
 =661911275027\cdot720957498683.
$$

Its factors each have 40 bits; the product has 79 bits despite the
historical nominal 80-bit label. Both factors are safe primes, both are
`11 mod 24`, and their ratio is about `1.0892`. All four natural group
cardinalities have a tiny smooth part followed by just one large prime:

| Cardinality | Exact factorization | Prime residual / `B^2` |
| --- | --- | --- |
| `p-1` | `2*330955637513` | about 4235 |
| `p+1` | `12*55159272919` | about 706 |
| `q-1` | `2*360478749341` | about 4613 |
| `q+1` | `12*60079791557` | about 769 |

Here `B=8840` and `B^2=78145600`. All four residuals are prime. The
cross-cardinality GCDs are only `2,2,2,12`; preprocessing removes the
small shared structure and leaves distinct long prime periods. The
saved 16-colour diagnostic therefore has no short-period choice.
For the current split-colour base, the actual projected orders are
`330955637513` and `360478749341`.

This is a proved obstruction to quadratic partial extraction on these
orders: every leaf is positive and at most `B^2+5`, so its product is
coprime to each long prime period. The Lean theorem
`long_prime_order_survives_quadratic_projection` says the order remains
unchanged. The fixed cubic and Lucas attempts also miss this control.
A reference-only enlargement to 528 seed pairs on each of the four
private periods finds no noncoherent equal/inverse alias at this width;
globally coherent aliases are excluded. That finite experiment is not
a lower bound for other maps or all factoring algorithms.

The existing
[long-period audit](semiprime-long-period-audit.json) records a useful
contrast: the first Suyama elliptic curve, `sigma=6`, factors out
`661911275027`, with projected local point annihilator `20873`, well
inside `B^2`. The four-rough property constrains the current multiplicative
and norm-one groups; it does not constrain every elliptic-curve order.
This control is therefore diagnostic of our chosen group families, not
evidence of intrinsic factoring hardness. The private factorizations in
this diagnosis are not cheaply available input to recovery.

Power/Dickson continuation and fast product/remainder factoring are
classical; see
[Brent–Kruppa–Zimmermann](https://maths-people.anu.edu.au/~brent/pd/rpb264.pdf).
The present contribution is the explicit partial-order classes, exact
orientation/coherent-root handling, implementation and replay. Universal
coverage is still missing. A bound on attempted work with budget
exhaustion does not prove factoring every semiprime in one-sixth time.

Scoped validation passes: 528 recurrence identities, shared-prefix
descent, imaginary orientation, a repeated-coherent-root cost regression,
and two derivative-stripping controls. The 23 new Lean theorems build
with warnings as errors, and the scoped 14-linter pass reports no errors.
The checked critical declarations use only standard Lean axioms; there
are no admissions or computation axioms. This does not yet verify the
whole Python program or its bit-operation complexity. The optional
module is not imported by the RH umbrella and the probe is not run in
ordinary CI.

Optional replay, from `formal/`:

~~~bash
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python -B scripts/probe_semiprime_rough_projection.py validate
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python -B scripts/probe_semiprime_rough_projection.py factor 477209897193541203289441
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python -B scripts/probe_semiprime_rough_projection.py probe --output docs/semiprime-rough-projection-audit.json
/home/dbsanfte/.elan/bin/lake build RiemannGaussian.SemiprimeRoughProjection --wfail
~~~

## October 2, 2026: public-input group selection with a dyadic tournament

The new optional
[group-selection implementation](../scripts/probe_semiprime_group_selection.py)
chooses a useful elliptic-curve probe from the input `N`, without consulting
the reference factors or hidden group orders. The reproducible
[53-input audit](semiprime-group-selection-audit.json) includes the source
hashes, every attempted curve/width, operation counters, factor certificates,
timing samples and independent single-curve reference replays.

Here “best group” has a precise, limited meaning: the first certified factor
at the smallest successful probe width in the fixed menu
`sigma=(6,11,7,8)`. It does not mean the elliptic curve with the smallest
group cardinality, the cheapest runtime, or the optimum among all curves.
The selector discovers a useful group during recovery; it does not obtain
the hidden order as free preprocessing.

### Public algorithm and the formal guarantee

At each width `W=16,32,64,...`, followed by the exact one-sixth-budget cap
if necessary, try every menu curve before increasing the width. Construct
the Suyama point and Montgomery parameter from the public sigma. Setup
denominators and the discriminant are GCD-tested, so an early failure may
itself expose a factor. Incrementally project by prime powers for newly
admitted primes `ell<=W`, taking each power up to the public bound
`N+2*isqrt(N)+3`. Baby/giant cover collisions are then batched with the
existing polynomial product/remainder machinery. Full-GCD coherent roots
are handled using the earlier derivative-stripping recovery. Setup,
projection, failed curves, repeated covers and recovery are all charged.

[SemiprimeGroupSelection.lean](../RiemannGaussian/SemiprimeGroupSelection.lean)
proves the reusable finite-menu policy:

- `tournament_sound`: every returned checked GCD is a proper divisor.
- `search_minimum_scale`: an ordered search chooses a width no larger
  than any successful candidate's width in the tested menu.
- `dyadic_tournament_guarantee`: if a menu candidate has a successful
  checked residue at `W=b*2^k`, the tournament returns a proper divisor at
  width at most `W`, and its sum of visited cover widths is at most
  `2*m*W`, where `m` is the menu size.
- `capped_coverWidth_bound`: appending a final truncated cap costs at
  most `3*m*cap` in the same cover-width measure.

The successful-probe premise is explicit. These are guaranteed policy and
certificate statements, not an assertion that every semiprime has a useful
curve in the menu. Cover width is a work proxy, not the complete program's
bit-operation count. The module also proves that the projective collision
signal and polynomial Montgomery addition/doubling formulas commute with
ring homomorphisms, and checks the hard control's concrete GCD certificate.
It does not yet verify the full Python implementation or the elliptic-curve
group-law interpretation of every recurrence.

### Same-menu benchmark and held-out results

The exploratory sample has eight balanced semiprimes at each of 48, 64 and
80 exact input bits, seed `2026100281`. The separate held-out sample uses
the same sizes with seed `2026100287`. The curve menu and initial width
were fixed before exploratory generation. A capped-pilot variant was
selected on exploration and frozen before generating the held-out sample:
try the menu through width 128, give sigma 6 an extra width-256 probe, then
fall back to the old staged sigma-6 pass.

The stronger comparison is against the previous staged ECM on precisely
the same four curves, sequentially. Its isolated function namespace makes
one recorded substitution, `sigma=curve_index+6` to
`sigma=curve_index+curve_start`, leaving the old arithmetic, projection
bound, staged target batches and recovery unchanged. This baseline was
added after the initial analysis; the recovery menu and pilot parameters
were not retuned. It is distinct from the new implementation's full-cover
fixed-menu control, which is also saved in the audit.

Each table time is the sum of per-input median full-call timings from
three calls, rotating method order with imports warmed. All algorithm
setup and failed probes are included. Reference generation, validation
replays and JSON writing are excluded. A budget-exhausted run contributes
to the total work but is not reported as a successful factor time.

| Sample | Method | Factors recovered | Sum of medians |
| --- | --- | --- | --- |
| Exploratory, 24 | Old staged sigma 6 | 21/24 | 4493.31 ms |
| Exploratory, 24 | Old staged same menu | 24/24 | 4601.24 ms |
| Exploratory, 24 | Adaptive tournament | 24/24 | 6060.06 ms |
| Exploratory, 24 | Capped pilot + sigma-6 fallback | 23/24 | 5043.18 ms |
| Held-out, 24 | Old staged sigma 6 | 23/24 | 3234.06 ms |
| Held-out, 24 | Old staged same menu | 24/24 | 5051.39 ms |
| Held-out, 24 | Adaptive tournament | 24/24 | 1727.31 ms |
| Held-out, 24 | Capped pilot + sigma-6 fallback | 24/24 | 1982.79 ms |

The tournament is about **2.92 times faster on the held-out same-menu
comparison**, with equal coverage. It is about **31.7% slower on
exploration**, again with equal coverage. On the 23 held-out inputs that
old sigma 6 already factors, the aggregate comparison is almost equal:
1668.72 ms for that baseline versus 1660.05 ms for the tournament. Much of
the held-out benefit is avoiding an expensive failed group before finding
a useful one. This is evidence for useful online group selection, not a
universal speedup or a new factoring exponent. The capped pilot does not
uniformly remove the tournament overhead, and can miss a curve found by
the full tournament.

The five saved regressions give a more concrete picture:

| Input `N` | Old staged same menu | Tournament | Chosen sigma / width |
| --- | --- | --- | --- |
| `49065649` | 0.57 ms | 0.65 ms | 6 / 16 |
| `8562316804979989201` | 129.48 ms | 95.66 ms | 11 / 256 |
| `477209897193541203289441` | 247.72 ms | 87.28 ms | 6 / 256 |
| `9710106156230271983` | 69.57 ms | 10.22 ms | 11 / 32 |
| `380307690410407004392769` | 6.72 ms | 42.84 ms | 6 / 128 |

The four-rough control is about **2.84 times faster** than the old same-menu
pass. The earlier rough-projection miss `9710106156230271983` is about
**6.81 times faster**. The last row is a substantial slowdown and must be
kept when assessing whether the selector is reliably useful.

On the four-rough control, independent public-input single-curve replays
give first successful widths 256, 512, 8192 and 4096 for sigmas 6, 11, 7
and 8 respectively. The selector visits cover widths totaling 1216,
below the formal bound `2*4*256=2048`. The successful x-coordinate alias
has baby multiplier 137 and giant multiplier `81*256`. On the public
projected point, the difference multiplier 20599 yields GCD 1, while
the sum multiplier 20873 yields factor `661911275027`. The saved signal
`474427418761119040057631` has that exact GCD with `N`; Lean checks this
certificate. A first successful width is an observed cover scale with
changing smooth projection, not a claim about the exact group order.

### What cheap colour does and does not reveal

A supplementary in-memory probe on the same control holds `A24` fixed
and tries affine x-coordinates 2, 3, 5, 7 and 11. For the corresponding
curve/twist choice, compute the public unit
`B_x=x*(x^2+(4*A24-2)*x+1)` and its Jacobi sign modulo `N`. The signs are
`+1,-1,+1,+1,-1`; first successful widths are respectively
`256,4096,256,256,256`. Thus x=3 and x=11 have the same cheap Jacobi colour
but very different useful scales in this example. This exploratory
diagnostic is not a formal impossibility theorem. It says that this colour
alone does not identify the best tested point for this input; the public
collision probes provide substantially more information.

The menu remains grounded in classical ECM. Suyama sigma 11 has useful
torsion statistics for certain prime congruence classes, as studied in
[Barbulescu–Bos–Bouvier–Kleinjung–Montgomery, Finding ECM-Friendly Curves](https://eprint.iacr.org/2012/070.pdf).
That is a curve-selection prior, not a pointwise optimality theorem.
The x-only arithmetic follows the framework described by
[Costello–Smith, Montgomery curves and their arithmetic](https://arxiv.org/abs/1703.01863),
and polynomial continuation is classical; see
[Brent–Kruppa–Zimmermann](https://maths-people.anu.edu.au/~brent/pd/rpb264.pdf).
The present result is an implementation, a controlled comparison and a
formal search-policy guarantee over these group choices.

### Validation and the next mathematical gap

The audit checks 10 curve setups, 230 scalar-ladder recurrences against
the previous implementation, six small proper-factor cases, 1098 width
schedules and two shared-root regressions. All four saved source hashes
match the final files. The new optional Lean module has 23 theorems and
builds with warnings as errors; its scoped 14-linter pass reports no
errors. The audited critical proofs use only standard Lean axioms. The
module is outside the RH umbrella and the numerical replay is not part
of ordinary CI.

Optional commands from `formal/`:

~~~bash
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python -B scripts/probe_semiprime_group_selection.py validate
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python -B scripts/probe_semiprime_group_selection.py factor 477209897193541203289441
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python -B scripts/probe_semiprime_group_selection.py factor 477209897193541203289441 --hybrid
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python -B scripts/probe_semiprime_group_selection.py probe --repeats 3 --output docs/semiprime-group-selection-audit.json
/home/dbsanfte/.elan/bin/lake build RiemannGaussian.SemiprimeGroupSelection --wfail
~~~

The target of guaranteed one-sixth factoring for every semiprime remains
open. The immediate gap is a useful-group existence or prediction theorem:
why should a cheaply searched menu contain a separating probe within the
budget on every input? A minimum-width theorem conditional on such a hit
does not supply it. Also outstanding is complete bit-complexity accounting
for smooth projection, polynomial batches and shared-root recovery.
Further experiments should test input-derived ranking signals against
this same-menu baseline, retain failed and slow inputs, and keep ranking
cost inside the recovery budget. The current small shared-environment
timings are not a comparison with a tuned production GMP-ECM build.

## October 2, 2026: useful-group coverage, exact counterexamples and a guaranteed prefix

The next requirement is coverage on **every run for every semiprime**, with
numeric-input budget `B=ceil(N^(1/6))`. Successful samples alone cannot
provide that guarantee. The new
[coverage module](../RiemannGaussian/SemiprimeGroupCoverage.lean),
[public-input probe](../scripts/probe_semiprime_group_coverage.py) and
[coverage audit](semiprime-group-coverage-audit.json) separate a sufficient
period criterion, exact failures of the current menu, an unconditional
small-factor population and the remaining curve-generation problem.

### Exact menu failures, including a separated control

The four-curve menu `(6,11,7,8)` passes an additional 599 balanced examples
at 24, 32, 40 and 48 bits, generated with seed `2026100293`. That exploratory
scan ran in memory. A targeted known-prime diagnostic then found actual
menu failures; its deterministic generation and public replay are saved.

| Control `N` | Reference primes | Width cap | Original four curves | B-step Fermat | Extended menu |
| --- | --- | --- | --- | --- | --- |
| `62108022589` | `248909`, `249521` | 63 | exhausted | first test recovers `248909` | sigma 13, width 16 |
| `46840800959` | `203653`, `230003` | 61 | exhausted | all 61 tests exhausted | sigma 12, width 16 |

Both controls also exhaust the complete quadratic integer prefix because
their factors are above `B^2`. The first control is near a square, so it is
not a difficult factoring example for Fermat. The second has first Fermat
centre `216428` and factor-pair centre `216828`, 400 increments apart. It
therefore remains outside the **current B-step** near-square window.
These finite examples are failures of the specified budget/menu, not
asymptotic lower bounds for arbitrary factoring methods or larger constants.

On the first control the reference residual point periods are:

| Sigma | Modulo `248909` | Modulo `249521` |
| --- | --- | --- |
| 6 | 5189 | 20719 |
| 11 | 20789 | 20873 |
| 7 | 20773 | 5189 |
| 8 | 20753 | 6949 |

Every period is above `63^2+63=4032`; neither equality nor inverse cover
leaves can reach them. Reference orders are computed only after supplying
the known prime to a separate finite-field diagnostic. They never enter
recovery. For both controls, the audit also computes the actual public
projective leaf products at every original curve/width and checks GCD 1,
with all coordinate denominators units. Thus these are exact replayed
implementation failures rather than noisy estimates of smoothness.

The first reference search checks 1174 distinct primes in
`[3*64^3/4,64^3)`, seed `2026100299`; the second checks 1708, seed
`2026100311`, and additionally requires failure of the public B-step
Fermat test. Both deliberately construct adversarial inputs. Their private
prime inspection is diagnostic work, not an available algorithmic signal.
The extended menu `(6,11,7,8,9,10,12,13)` was chosen after inspecting the
first control. It fixes these two examples but has no universal coverage
theorem. The original selector and its previous benchmark remain unchanged.

### The useful-period criterion is weaker than coprimality

For the two projected local point periods `r_p` and `r_q`, a sufficient
target is

$$
\min(r_p,r_q)\le B^2,
\qquad r_p\ne r_q.
$$

`smaller_period_separates` and `unequal_small_periods_have_cover` prove
that a smaller positive period supplies a separating power; coprimality
of the two periods is unnecessary. Crucially,
`smaller_period_has_two_orientation_cover` retains both x-coordinate
orientations. If the smaller period is below `B`, a baby identity
separates. Otherwise write it as `B*j+i`, with `1<=j<=B`, `0<=i<B`.
The selected group closes in the inverse orientation, while the other
group closes in neither orientation: its possible difference exponent
`B*j-i` is positive and below its period, and the sum exponent is the
smaller period. For `i=0` this is a separating giant identity.

Conversely, `same_period_coherent_aliases` proves that equal periods make
all integer-exponent aliases coherent, including inverse channels. Thus
finding a small period alone is insufficient; the other component must
separate. These are generic group theorems. The full elliptic-curve
group-law interpretation of the Python formulas remains outside this
formal module, as in the earlier selector work.

### A population with unconditional coverage

The new public `prefix` command constructs the degree-B polynomial

$$
P_B(X)=\prod_{i=0}^{B-1}(X-i)
$$

and evaluates it at `B,2B,...,B^2` with the existing product/remainder-tree
code. These B evaluations jointly cover all positive integers through
`B^2`. It constructs neither the length-`B^2` factorial nor a factor table.
This is classical Strassen-style batching, not a new algorithmic exponent.

`descending_block_eq_polynomial`, `prefix_rows_eq_factorial` and
`prefixProduct_eq_factorial` prove the exact joined polynomial identity.
`polynomial_prefix_recovers_under_sixth_budget` proves that for every
semiprime `N=p*q`, `p<=q`, with `B>=4`,

$$
(B-1)^6<N,\qquad p\le B^2
\quad\Longrightarrow\quad
\gcd\!\left(N,\prod_{j=1}^{B}P_B(Bj)\right)=p.
$$

The larger prime is automatically above the covered prefix at this budget,
so the separating condition has no additional arithmetic hypothesis.
`failed_prefix_excludes_small_prime` proves that a coprime complete prefix
rules out every prime factor at most `B^2`. Consequently the group search
only needs to handle the remaining larger-factor population.

Twelve fresh samples, seed `2026100307`, use 12-, 16- and 20-bit smaller
primes with a larger prime chosen above `p^2`. All twelve are recovered by
the public prefix at their computed width, on inputs of 36–61 bits. The
reference factors only verify the mathematical coverage premise afterward.
Polynomial work and setup are included in the recorded time and counters.
The formal proof gives exact coverage and GCD soundness; it does not yet
verify the whole Python implementation or its bit-operation complexity.

### Universal arithmetic order targets exist; cheap realisation is missing

`smaller_factor_le_cubic_width` proves `p<=B^3` from `p<=q` and
`p*q<=B^6`. For the remaining range `B^2<=p<=B^3`, set

$$
D=2^{\lceil\log_2 B\rceil},\qquad
c=\lfloor p/D\rfloor+1,\qquad M=Dc.
$$

`dyadic_hasse_order_target` proves

$$
B\le D<2B,\qquad
0<c\le B^2+1,\qquad
p+1\le M\le p+1+2\lfloor\sqrt p\rfloor.
$$

`semiprime_hasse_order_target` supplies a small-cofactor Hasse candidate
for every smaller factor under the sixth-root budget; small factors can
use trace zero. `projected_candidate_order_bound` proves that an actual
point order dividing `M`, after an exponent containing `D`, fits a padded
width-`B+1` cover. The useful-order target is thus precise rather than an
unspecified smoothness wish.

For the first control, the candidate orders are `248960=64*3890` and
`249536=64*3899`, with traces `-50` and `-14`. Classical finite-field order
realisation is described by Deuring–Waterhouse; see Theorem 6.8 of
[Kowalski, Analytic problems for elliptic curves](https://people.math.ethz.ch/~kowalski/analytic-pbs.pdf)
and [Waterhouse's original classification](https://numdam.org/articles/10.24033/asens.1183/).
That curve-realisation theorem is **not formalised or imported here**.
In particular, the Lean Hasse-target theorem is arithmetic existence, not
a claim to have constructed a useful public curve.

The obstacle is algorithmic access: the expression uses the unknown `p`.
A curve or CRT lift designed with private prime knowledge is circular for
factoring. Prescribed-order construction literature also has a different
input specification; for example
[Bröker–Stevenhagen](https://arxiv.org/abs/0712.2022) constructs a field and
curve from a given prime target order. It does not provide a cheap public
constructor over our unknown factor field.

`fixed_divisor_cubic_gap` makes the scaling issue explicit: a fixed
guaranteed torsion divisor does not by itself bound the residual by `B^2`
when the original order is on the cubic scale. Growing smooth structure,
or a guarantee of hitting it, is required. Also,
`period_preserved_by_coprime_kernel` proves that a group homomorphism with
kernel killed by an exponent coprime to the point period preserves that
period exactly. Isogeny-like changes satisfying this condition cannot
shorten the obstructive rough period. This does not exclude genuine
changes of curve or twist that alter the local order.

### Exact frontier and checks

The remaining universal target is an input-derived public family, of at
most polylogarithmically many affordable candidates, guaranteed to produce
unequal projected local periods with a minimum inside the cover for every
remaining semiprime. The dyadic tournament already controls selection
overhead once such a candidate exists. Its existence and cheap construction
are still open. No universal one-sixth claim follows from these examples,
from expected ECM smoothness, or from the Hasse candidate alone. Compare
the explicit conjectural one-sixth framework of
[Umans–Wang](https://arxiv.org/abs/2511.10851); its structured difference-cover
premise is also a genuine additional requirement.

The new module's focused warning-as-error build, 14 namespace linters and
all-public standard-axiom audit pass. The numerical replay checks both
menu failures, the expanded-menu recovery certificates, every recorded
public projective cover, reference-period reductions and all twelve
guaranteed-prefix cases. The optional code and Lean module remain outside
the RH umbrella and ordinary CI. No source from the RH proof campaign or
the previous group selector is changed.

Optional commands from `formal/`:

~~~bash
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python -B scripts/probe_semiprime_group_coverage.py prefix 46840800959
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python -B scripts/probe_semiprime_group_coverage.py fermat 46840800959
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python -B scripts/probe_semiprime_group_coverage.py curve 46840800959
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python -B scripts/probe_semiprime_group_coverage.py probe --output docs/semiprime-group-coverage-audit.json
/home/dbsanfte/.elan/bin/lake build RiemannGaussian.SemiprimeGroupCoverage --wfail
~~~

## October 2, 2026: public point rotation and a cheap product-colour selector

The new [point-rotation module](../RiemannGaussian/SemiprimePointRotation.lean),
[optional implementation](../scripts/probe_semiprime_point_rotation.py) and
[replay audit](semiprime-point-rotation-audit.json) test a cheaper change of
local group before constructing another Montgomery curve. Curve setup is
shared across starting points. Each point still pays its own smooth
projection and polynomial collision batches. Hidden factors and local
orders never enter recovery.

The target remains a deterministic, every-run guarantee for **every**
semiprime at numeric-input cost `Õ(N^(1/6))`. A bounded search that can
return exhaustion is not that theorem. This scaling would improve the
published deterministic one-fifth benchmark on semiprimes; it would not
asymptotically beat GNFS's standard heuristic subexponential scaling. See
[Harvey–Hittmeir](https://arxiv.org/abs/2105.11105) and
[Bernstein–Lenstra's GNFS analysis](https://www.cs.umd.edu/~gasarch/TOPICS/factoring/1993_Book_TheDevelopmentOfTheNumberField.pdf).

### Point rotation fixes both existing menu failures

The existing Montgomery x-only formulas work with a different starting
point on the corresponding curve/twist without changing `A24`; see
[Costello–Smith](https://arxiv.org/abs/1703.01863). The public point fixes are:

| Input | Sigma | Affine x | Successful width | Factor | Exact GCD signal |
| --- | --- | --- | --- | --- | --- |
| `62108022589` | 11 | 3 | 16 | `248909` | `2497552906` |
| `46840800959` | 6 | 2 | 16 | `203653` | `21203535748` |

`first_control_point_signal` and `separated_control_point_signal` check
these proper-divisor certificates in Lean. The optional implementation
first keeps the original four Suyama points and then tries the three
additional public points `(6,2)`, `(11,2)`, `(11,3)`. Its default policy
exhausts the original menu before using this fallback.

The exact finite-field diagnostics explain why the points matter. On the
first input the sigma-eleven curve has projected cardinality quotients
`199` and `10357` over the two reference primes, while its twists have
quotients `20789` and `20873`. The original Suyama point selects the two
twists. On the second input the sigma-six curve at the smaller prime has
quotient `227`, while its twist has `16993`. An alternative point exposes
the small channel. These cardinalities are computed by finite-field
enumeration with **known reference primes**, solely for diagnosis. The
elliptic group-order interpretation is not yet a Lean-verified certificate.

### Preserve the successful baseline instead of interleaving blindly

The fixed point menu was chosen on those two failures before a fresh
32-input sample, seed `2026100323`, with input sizes 23–48 bits. Every call
uses three repeats; totals below sum per-input median times in this shared
development environment.

| Policy | Fresh successes | Total median time | Additional-point hits |
| --- | --- | --- | --- |
| Original four-point tournament | 32/32 | 104.36 ms | — |
| Original pass, then fixed-point fallback | 32/32 | 104.62 ms | 0 |
| Interleaved seven-point tournament | 32/32 | 123.19 ms | 1 |
| Original pass, then colour-selected fallback | 32/32 | 104.56 ms | 0 |

Interleaving costs about 18% more overall. Its one improvement reduces
the observed width from 64 to 32 on `137894683731943`, but the additional
work on the other inputs outweighs that saving. This is retained as a
negative result. The fallback policies preserve every original operation
counter, selected sigma and successful width whenever the baseline succeeds;
the audit asserts this. Small wall-time differences between those policies
are measurement noise, not a claimed speedup. The colour policy was designed
after the adversarial control below; these 32 already-successful inputs
do not test its rescue rate on unseen menu failures.

### A new exact palette failure

The private-prime diagnostic finds

$$
N=71739148259=252983\cdot283573,
\qquad B=\lceil N^{1/6}\rceil=65.
$$

`point_menu_miss_semiprime_and_budget` checks both primes, the product,
`64^6<N<=65^6`, and that both factors exceed `65^2`. The public replay
exhausts the original four points and all three additional points. All
28 actual projective cover products have GCD one, and every sampled
coordinate denominator is a unit. These products and projected starting
coordinates are saved; they are computational trajectory checks rather
than a formal verification of the entire Python program.

The complete `1..65^2` additive prefix and all 65 bounded Fermat tests
also miss. Fermat starts at 267842, whereas the factor-pair centre is
268278. This is a failure of these specified menus and budgets, not an
asymptotic lower bound. The eight-curve extension recovers `283573` at
sigma 9, width 16.

Generation is reproducible: the first reference search uses seed
`2026100337`, width 64, and finds `252983` after 2772 distinct primes.
The second uses seed `2026100351`, width 72, and finds `283573` after 427.
Reference-only searches are never counted as affordable algorithmic input.

### Product colour supplies a cheap, useful selection bit

For a projective point `(X:Z)` and `A=4*A24-2`, evaluate

$$
Q_A(X,Z)=XZ(X^2+AXZ+Z^2).
$$

`homogeneousColour_eq_scaled_rhs` proves exactly, for nonzero `Z` in a
field,

$$
Q_A(X,Z)=Z^4\big[(X/Z)^3+A(X/Z)^2+X/Z\big].
$$

Thus its quadratic colour agrees with the affine RHS colour without
performing a coordinate inversion. `homogeneousColour_character` checks
the multiplicative-character statement with its square-unit premise.

The public Jacobi colour is the product of the two unavailable local
Legendre colours. `product_colour_flip_exactly_one` proves that reversing
this product flips **exactly one** local sign. This makes a curve/twist
change accessible using only `N`; it does not reveal which prime changed,
nor does it assert a shorter order. An unchanged product colour can also
hide changes to both local signs, so opposite-colour selection is not a
complete substitute for the original point palette.

The optional `--colour-flip` policy first runs the original four-point
pass. After exhaustion it scans at most 32 small x-values per curve,
retaining up to two with product colour opposite to that curve's original
point. Every scan, rejected point, GCD and subsequent projection is charged.
Failure to find a requested colour within the cap stays explicit. This
policy recovers all three recorded controls. On the new palette miss it
selects sigma 7, x=2, width 32, with exact signal `38765850005` and factor
`252983`; `colour_selected_new_control_signal` checks that GCD in Lean.

The colour fallback is additional coverage, not an established performance
advantage. It takes about 45 ms on the new control after paying the failed
original pass; the sigma-nine curve extension recovers the same input
earlier. The policy remains optional and does not change the old selector.

### A uniform limitation on changing points

`projected_prime_dichotomy` and `projected_prime_order_of_ne_one` prove:
if a point order divides `h*ell`, `h` divides the public projection exponent,
and `ell` is prime, then the projected point is either the identity or has
order exactly `ell`. If `ell>B^2+B`,
`projected_prime_no_two_orientation_cover` proves both orientations of every
B-by-B cover leaf miss for every nonidentity projected point. This is
uniform across starting points, rather than a finding about a few examples.

For instance, the two sigma-seven cardinality channels at reference prime
`203653` are `8*25469` and `12*16963`, both with large prime quotients;
`separated_rough_channels` checks those primes and the numerical cover gap.
Changing a point within either projected population cannot produce a
shorter **nonidentity** period. It can still hit the identity and separate
the other component, or switch to a different local group. Neither event
is guaranteed by its public colour alone.

This is the remaining mathematical coverage target: guarantee an
affordable candidate whose actual local periods separate and fit the
cover, or provide a genuinely different structured extraction for the
remaining long-prime population. Colour gives cheap access to one bit of
local group selection. It does not supply the missing every-semiprime
order bound, and these results do not establish universal one-sixth time.

### Validation and optional replay

The twelve public theorems have a focused warning-as-error build, scoped
declaration lint and standard-axiom audit. The optional replay checks
the three control certificates, all 28 new-failure cover products, both
reference generators, all fresh successes and preservation of the original
cost counters. Four recorded source hashes match the final files. Full
Montgomery group-law correctness and whole-program bit-complexity remain
outside these certificates. The module stays outside the RH umbrella and
ordinary CI.

~~~bash
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python -B scripts/probe_semiprime_point_rotation.py factor 62108022589
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python -B scripts/probe_semiprime_point_rotation.py factor 71739148259 --colour-flip
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python -B scripts/probe_semiprime_point_rotation.py probe --repeats 3
/home/dbsanfte/.elan/bin/lake build RiemannGaussian.SemiprimePointRotation --wfail
~~~

## Open questions and next experiment criteria

1. Decode the available modular factor-sum signal with better scaling.
   Explore shared collision work across weighted sums and factor-ratio
   windows, comparing with published deterministic `N^(1/5)` methods.
   The sparse binomial observable now gives an exact target: find a cheap
   evaluator that does not materialise a square-root-length truncation.
   Compact rounded-centre descriptors need both cheap exception generation
   and an exact shared collision-product evaluator before an exponent claim.
   The new order-separation pass supplies actual one-sixth-budget extraction
   on an explicit population; the remaining target is cheap information
   from long rough periods. The new Dickson/quadratic alias reaches two
   four-rough controls; its coverage beyond the linear interval needs a
   quantitative theorem. Compare any expanded map family with the newly
   implemented one-curve pass, charging all finite-difference and polynomial
   work. More colours or a constant-factor phase saving alone do not pay
   the generic gap.
2. Test whether a signed or multiscale filter can cancel unwanted
   coefficients while preserving a measurable factor-imbalance signal.
   Specify its evaluation cost and leakage control before calling it a
   factoring algorithm.
3. If revisiting nearby-prime operations, compare the same trial budget
   against matched gap bases and standard modular-factor methods. Include
   the cost of locating all auxiliary primes.
4. Any promising numerical result needs held-out inputs, no hidden factor
   tables, an explicit factor interval and exact divisibility verification.
   A formal measurement theorem and a cheap measurement algorithm are
   separate requirements.
5. Benchmark any improved method against suitable conventional methods at
   meaningful input sizes. Account for cache state, precomputation,
   precision, failure rate and total runtime.

## October 2, 2026: both hidden colour branches and lazy acquisition

The next investigation tested the selector on inputs deliberately built
from original-point misses, rather than relying only on fresh cases that
the original menu already solves. It found a specific information loss:
unchanged public product colour can hide reversal of **both** private local
curve/twist choices. A useful point can consequently be excluded by an
opposite-colour-only policy.

The new optional
[public implementation](../scripts/probe_semiprime_colour_coverage.py),
[exact replay audit](semiprime-colour-coverage-audit.json) and
[focused Lean module](../RiemannGaussian/SemiprimeColourCoverage.lean)
preserve the earlier prototypes. They supply a colour-diverse fallback
and cheaper acquisition of the same opposite-colour menu. They do not
establish an all-input sixth-root factoring bound.

### A same-colour point recovers the excluded branch

The finite control is

\[
N=494041\cdot494191=244150615831,
\qquad B=\lceil N^{1/6}\rceil=80.
\]

The original four-point menu and its opposite-colour fallback both exhaust
their full budgets. The existing fixed-point fallback succeeds on sigma
eleven at affine `x=3`, width 32, with certificate

\[
\gcd(244150615831,10273242508)=494191.
\]

On this curve, the original point has private RHS colours `(-1,+1)` while
the successful point has `(+1,-1)`. Both public Jacobi products are `-1`.
The opposite-colour selector instead chooses `x=2,4`, both with private
colours `(+1,+1)`. Private Legendre evaluations appear only in the labelled
known-prime explanation; the public algorithms receive only N.

`product_colour_same_both_or_neither` proves the exact sign classification:

\[
\epsilon_p\epsilon_q=\epsilon'_p\epsilon'_q
\Longrightarrow
(\epsilon'_p,\epsilon'_q)=(\epsilon_p,\epsilon_q)
\quad\text{or}\quad
(\epsilon'_p,\epsilon'_q)=(-\epsilon_p,-\epsilon_q).
\]

Together with the earlier `product_colour_flip_exactly_one`, this accounts
for every hidden branch. It does **not** mean that acquiring both public
colours guarantees acquiring both local sides: two points with colours
`(+1,+1)` and `(+1,-1)` already cover both public products while leaving
the first field's side unchanged. Nor does any colour bit determine a
projected period.

`same_colour_control_signal` checks the proper-divisor certificate in Lean;
`same_colour_control_semiprime` checks the primes and budget arithmetic.
This control is near a square: the first Fermat centre is 494116 and
`494116^2-N=75^2`. Thus it also has an exceptionally cheap classical
solution. The control establishes a selector failure and its repair,
not superiority over Fermat or intrinsic factoring difficulty.

### Two public policies, with every attempted point charged

Both new policies run the original four points over the complete dyadic
width schedule first. On failure, they acquire each curve's new menu only
when that curve is reached. A successful early probe therefore avoids
scanning later curves. Immutable curve setup is reused, with a separate
smooth-projection history for every point.

The lazy opposite policy retains the first two opposite-colour affine
points found in `x=2..33`, exactly the previous menu. The optional
`--diverse` policy retains those same two points plus the first same-colour
point, in scan order. It handles the new control without a factor, private
character, or group-order oracle. A same-colour point need not reverse
both local signs, so a fixed scan still has explicit failure cases.

Every setup, rejected candidate, GCD, Jacobi test, projection and polynomial
batch is charged. Each policy still has only a fixed number of curves and
points, with maximum width B. This preserves the earlier partial-pass
operation scale; it does not prove that a successful group exists for every
input. The diverse option is not made the default.

### Adversarial replay and fresh controls

The explicitly private generator first tests known primes against the
four original points at a reference width. Seed `2026100367`, width 80,
finds 11 misses among 8051 distinct primes in `[2^18,2^19)`. Seed
`2026100383`, width 112, finds 16 among 15766 primes in `[2^19,2^20)`.
The implementation records the seeds, random-draw limits, exact survivor
lists and diagnostic exponents, and its regeneration replay passes.

All within-cohort and cross-cohort pairs give `55+120+176=351` distinct
semiprimes, at 36--40 bits. Actual recovery uses each product's own B.
Some cross-cohort products raise B above the first reference width and
are therefore solved by the original menu. This construction deliberately
biases the corpus toward failures; it is not a random-input success-rate
estimate.

| Public policy | Factors recovered | Candidate-colour scans | Jacobi tests | Scalar bits |
| --- | ---: | ---: | ---: | ---: |
| Original four points | 60/351 | 0 | 0 | 1222502 |
| Eager opposite-colour fallback | 350/351 | 4611 | 7238 | 1706985 |
| Lazy opposite-colour fallback | 350/351 | 3078 | 5319 | 1706985 |
| Lazy diverse-colour fallback | 351/351 | 3323 | 6119 | 1848211 |

Lazy acquisition reduces candidate scans by 33.25% and Jacobi tests by
26.51%, with **identical** aggregate group and polynomial-operation
counters to the eager opposite-colour policy on this corpus. It does not
demonstrate a meaningful whole-call runtime gain: on the first 24
adversarial pairs, rotating method order over three repetitions, sums of
per-input median times are 947.887 ms eager, 948.512 ms lazy opposite and
1006.262 ms lazy diverse. The diverse option is about 6.16% slower here
and performs 8.27% more scalar bits over the full corpus. Additional
coverage is not a claimed general speedup. These are comparisons with our
own Python prototypes, not GNFS or the best available classical software.

All 32 fresh controls, seed `2026100413`, remain successful in the original
pass with identical original operation counters under both new policies.
Separate small-input checks cover 465 semiprimes with factors at most 113
under both policies, plus 16 finite scan-cap regressions. Every returned
factor is checked by exact divisibility and, where supplied, its GCD signal.

The four new Lean declarations compile with warnings treated as errors,
pass all 14 scoped declaration linters and use only `propext`,
`Classical.choice` and `Quot.sound`. The sign identities are generic;
the concrete GCD and prime assertions are kernel-checked arithmetic.
This does not certify the whole Python control flow or the elliptic group
law. Source hashes tie the replay to the new implementation, previous
rotation/selection implementations and Lean module. No RH source,
umbrella import, default CI target or repository publication artifact changes.

### The universal group guarantee is still the missing exponent step

The sufficient criterion remains unequal local projected periods with
minimum at most `B^2`. The previous
`projected_prime_no_two_orientation_cover` already proves that a nonidentity
point in a residual prime-order population with `ell>B^2+B` cannot close
either orientation in the cover, regardless of which starting point is
chosen. Colour selection helps only when another local curve/twist side or
an identity projection is useful; it does not shorten a long prime period
inside the same group.

Both a curve and its twist can have almost-prime group orders. This is
also the deliberately constructed regime called twist security in
[Costello--Smith's Montgomery-curve survey](https://eprint.iacr.org/2017/212.pdf).
The survey's curve/twist observation supplies context, not a coverage
theorem for our parameter menu. The more recent
[even-order ECM approach](https://arxiv.org/html/2503.00950) explicitly uses
GRH and a distribution conjecture in its complexity analysis; it does not
give the guaranteed every-run sixth-root estimate requested here.

The new sign theorem repairs information loss in the cheap selector; it
does not reduce the universal coverage gap. The next exponent-changing
result must either construct a small separating period at affordable cost
from N alone, or extract useful information from a long rough period without
enumerating it. Enlarging a fixed point palette and reproducing successful
samples are not substitutes for either theorem.

Focused replay, outside normal builds and CI:

~~~bash
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python -B scripts/probe_semiprime_colour_coverage.py factor 244150615831 --diverse
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python -B scripts/probe_semiprime_colour_coverage.py probe --regenerate-cohorts --repeats 3
lake build RiemannGaussian.SemiprimeColourCoverage --wfail
~~~

## October 2, 2026: cheap high-degree evaluation and its collision partition

This investigation tested an inexpensive way to access large polynomial
degrees directly, rather than constructing another group-point menu.
The optional
[public probe](../scripts/probe_semiprime_fast_dickson.py),
[complete replay](semiprime-fast-dickson-audit.json),
[Lean proofs](../RiemannGaussian/SemiprimeFastDickson.lean) and
[scoped checker](../scripts/CheckSemiprimeFastDickson.lean)
are separate from the existing factoring policies and ordinary CI.

For the direct Dickson map `D_d(x,1)`, the exact binary updates are

\[
D_{2k}(x)=D_k(x)^2-2,
\qquad D_{2k+1}(x)=D_k(x)D_{k+1}(x)-x.
\]

They evaluate a degree with millions or trillions of terms without
expanding its coefficients: each point uses two modular multiplications
per degree bit. The generic Lean theorem `dicksonOfBits_correct` proves
both outputs of the binary circuit over every commutative ring, including
composite residue rings. This is different from the earlier experiment
`alpha^(D_d(i,1))`: here the polynomial is evaluated **directly modulo N**,
with no intermediate group exponent.

### Large degree is not the missing coverage signal

The exact fibre theorem is

\[
D_d(x)=D_d(y)\text{ in }\mathbb F_p
\iff
D_{\gcd(d,p^2-1)}(x)=D_{\gcd(d,p^2-1)}(y)\text{ in }\mathbb F_p.
\]

`dickson_prime_field_collision_gcd` proves it for every prime and all field
elements. The proof lifts a trace to reciprocal roots in an algebraic
closure, proves their exponent divides `p^2-1`, and compares the two exact
power kernels. The GCD is a reference explanation; recovery never reads
the unknown prime or this hidden field exponent. The underlying Dickson
theory is classical; see
[Bluher's primary paper](https://arxiv.org/html/1707.06877), which states the
permutation criterion. This pass does not claim to have invented Dickson
folding.

For **every** ordered odd semiprime `N=p*q`, `p<q`,

\[
\gcd(N,p^2-1)=1.
\]

Consequently degree N permutes the smaller prime field. It cannot create
new smaller-prime collisions, even though its evaluation is inexpensive.
`semiprime_degree_short_grid_no_collision` proves that the concrete
`B`-by-`B` integer grid still misses whenever `B^2<p`. This closes the
degree-N candidate for extracting information beyond that smaller-factor
prefix; it is not a lower bound for other maps or factoring algorithms.

The 5940 composite/prime-ring recurrence checks pass. All 990 ordered
odd-prime pairs below 200 reproduce the smaller-field permutation; 875
also permute the larger field. Every larger-field exception has
`p | q-1` or `p | q+1`. There are 1980 full-field collision-partition
comparisons and 336 additional cover-partition comparisons on the saved
and fresh factoring inputs; all agree with the exact GCD compression.

### A real nearby-degree recovery, but sparse coverage

The fixed public degree menu is `1,6,24,N,N-1,N+1`. Each method receives
only N, evaluates B babies and B giants, and uses the existing monic
product/remainder batch, coherent-root stripping and GCD descent.
Every fold update and batch operation is charged; an unsuccessful batch
returns explicit budget exhaustion rather than an alleged factor.

| Direct fold | Four saved controls | 24 fresh inputs |
| --- | ---: | ---: |
| Degree 1 | 0/4 | 0/24 |
| Degree 6 | 0/4 | 1/24 |
| Degree 24 | 2/4 | 1/24 |
| Degree N | 0/4 | 0/24 |
| Degree N-1 | 1/4 | 1/24 |
| Degree N+1 | 1/4 | 1/24 |

The fresh corpus uses seed `2026100441`, with eight balanced inputs at
each exact size 40, 48 and 64 bits. Degree N+1 gives a distinct fresh
recovery missed by the direct degree-1/6/24 batches:

\[
N=171033372116459=12108181\cdot14125439,
\qquad B=236,
\]

\[
\gcd(N,95291626633620)=12108181.
\]

This uses baby 207 and giant `236*41`, with 472 evaluated points and
45312 fold modular multiplications. `fresh_nearby_degree_signal` checks
the proper-divisor certificate in Lean. The private explanatory GCDs
are 420 in both fields, whereas degree N has GCD one. This demonstrates
cheap individual access to a genuine extra collision, not a guaranteed
degree selector or superiority over the existing elliptic algorithms.

Neither nearby degree recovers the saved nominal 64/80-bit four-rough
controls. Their degree N-1 collision partitions are exactly those of
degree 24; their degree N+1 partitions are exactly those of degree 2.
Thus making the degree enormous buys no extra collision pattern there.
One recovery occurs only on the small saved control, and the other on
the previously documented near-square control that Fermat solves
immediately. Those are not new hard-input milestones.

Single full-call exploratory totals on the fresh corpus are about
0.92 seconds for the direct linear batch, 0.98 for degree 24, and 1.90
for degree N+1. They include setup and polynomial work, with warm imports
in a shared environment. There is no tuned classical benchmark, timing
distribution or claimed practical speedup. The complete output retains
per-input results, proper-GCD witnesses, operation counters, private
diagnostics and source hashes. The Lean circuit and algebraic theorems
do not certify the full Python control flow or its bit complexity.

All 11 public theorems compile with warnings treated as errors. The
scoped declaration check passes all 14 linters, and the transitive-axiom
audit covers all 47 module declarations, including 37 proof declarations
with generated equations: only `propext`, `Classical.choice` and
`Quot.sound` are used. The exact finite recovery certificates and
operation-budget checks pass on all 28 saved/fresh inputs.

The remaining exponent step is precise: cheap evaluation is available,
but an input-dependent degree or other map must guarantee a **separating
collision** from N alone. A large formal degree, a hidden large GCD, or a
few successful examples does not prove such coverage. The requested
every-run, every-semiprime `Õ(N^(1/6))` theorem remains open.

Focused replay, outside normal builds and CI:

~~~bash
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python -B scripts/probe_semiprime_fast_dickson.py factor 171033372116459 --degree N+1
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python -B scripts/probe_semiprime_fast_dickson.py probe
lake build RiemannGaussian.SemiprimeFastDickson --wfail
lake env lean -DwarningAsError=true scripts/CheckSemiprimeFastDickson.lean
~~~

## October 2, 2026: row batching and cancellation transferred from the RH toolbox

The new optional
[Lean module](../RiemannGaussian/SemiprimeRowStructure.lean),
[public-input implementation](../scripts/probe_semiprime_row_structure.py),
[complete replay](semiprime-row-structure-audit.json) and
[scoped checker](../scripts/CheckSemiprimeRowStructure.lean)
test whether common phases and joined cancellation can remove the cost of
constructing the weighted collision rows. The universal, every-run
`Õ(N^(1/6))` factoring guarantee remains **unproved**.

### What is shared exactly

For a unit `g`, weights `a,b`, and the literal centre
`c(a,b)=ceil(2*sqrt(N*a*b))`, write

\[
V_{a,b}=g^{aN+b-c(a,b)}
       =(g^N)^a g^b(g^{-1})^{c(a,b)}.
\]

`rowAnchor_factor` proves the shared-axis identity in any commutative
group. The centre depends only on `a*b`, so the implementation caches it
and its modular power once per distinct product. All caches are rebuilt
from public N inside the timed call; no private factors or lookup table
are supplied to the algorithm. Every literal row is still materialized.

For a rectangular four-corner test, `rowAnchor_cross_ratio` cancels the
large axis powers exactly, leaving

\[
\frac{V_{a,b}V_{a',b'}}{V_{a,b'}V_{a',b}}
  =g^{c_{01}+c_{10}-c_{00}-c_{11}}.
\]

`rowAnchor_cross_eq_iff_order_dvd` identifies exact separability with
divisibility of this centre defect by the local group order. This does
not assume that rounded centres admit an outer-product representation.
The 1402 tested admissible four-corner signals `g^defect-1` were all
units, so none yielded a factor or an exact separable block.
This finite negative audit does not rule out a different low-rank or
structured construction.

### A cheap signed collapse, and its lost hit

The strongest directly transferable RH idea was to keep a common prefix
until the cancellation is exact. Swapped weights have the same centre:

\[
\frac{V_{a,b}}{V_{b,a}}=g^{(a-b)(N-1)}.
\]

`rowAnchor_swap_ratio`, `rowAnchor_swap_difference` and
`rowAnchor_swap_sum` prove the ratio and both ring channels. If the weight
indices lie in a B-by-B grid, all normalized swapped channels depend on
only O(B) differences. The implementation tests them using one setup power
`g^(N-1)`, B repeated multiplications and 2B GCDs. No quadratic row list is
required for **these particular channels**.

However, this is exactly the already-known N-1 projected-period signal.
It removes the centre information that aligns an original row with the
target one. `swap_cancellation_does_not_preserve_hit` checks the literal
counterexample N=77, weights 1 and 2, centre 25: the anchors are 71 and 23.
The first anchor minus one gives factor 7, while both their sum and their
difference are coprime to 77. The B=`ceil(N^(1/6))` signed-collapse probes
also returned no proper factor on any of the 20 saved/fresh inputs.
This disproves replacement of the original hits by those channels, not
the possibility of a different joint cancellation.

### Retaining the boundary preserves roots

The RH masked-convolution principle is more useful here than a signed
norm saving: retain the target-one terms before joining the rows. Put
`Y=V_(b,a)` and `beta=g^((a-b)*(N-1))`. The checked theorem
`rowAnchor_swap_target_product` gives

\[
(V_{a,b}-1)(V_{b,a}-1)
  =Y^2\beta-Y(\beta+1)+1.
\]

The constant and linear boundary terms are indispensable. This is an
exact collision product, but Y still contains the coupled weighted centre.

There is also a root-preserving reciprocal fold. For any units x,y in a
commutative ring, `unit_trace_collision_factorization` proves

\[
(x^2-1)(y^2-1)
 =xy\left[xy+(xy)^{-1}-x/y-y/x\right].
\]

`unit_trace_collision_iff` proves that in each hidden prime field the
bracket vanishes exactly when `x^2=1` or `y^2=1`. It therefore retains all
target-one hits and also the target-minus-one hits. No unknown field
order or division by a nonunit is used. If both prime components hit,
the joined GCD is N and the original factors must be inspected by descent;
this is visible in the N=77 regression, where the other row reveals 11.
Reciprocal Laurent/trace folding is classical, rather than an invented
new factoring mechanism; see
[Montgomery–Kruppa's stage-two construction](https://antsmath.org/ANTSVIII/files/kruppa.pdf).

The new small-ring replay checks all these identities, unit-prefix GCD
invariance and preservation of original hits on 1860 swapped pairs.
That does not give a universal separating-hit coverage theorem or certify
the complexity of the complete Python factoring control flow.

### Which RH results carry over

- `ZetaRieszComplexNullFloor.increment_coherent_zero` motivates cancelling
  a shared prefix exactly. The row-swap lemmas implement that idea, but
  the counterexample shows why the factor target cannot be discarded.
- `ZetaRieszOrderedWard.masked_logarithmic_convolution` retains the signed
  complement of an order mask. Its lesson here is the target boundary
  in the paired product. A literal logarithmic derivative cannot be
  divided by the collision product at a factor hit: it is then a nonunit.
  Product/derivative jets must be retained without that division.
- `ZetaRieszCrossingOrbitCancellation.crossing_literal_sum_eq_zero` uses
  complete divisor orbits and affine saturated hinges. Those hypotheses
  do not hold for `g^(-ceil(2*sqrt(N*a*b)))`; unknown divisors are also not
  a cheaply supplied factoring input.
- `ZetaRieszComplexProjection.native_floor_with_credit` improves a real
  one-sided allowance. A reduced real allowance does not itself establish
  a modular collision or a proper GCD.

Thus exact product identities and retained mask boundaries are useful
transfers. Generic real-valued sign savings are not sufficient coverage
signals for factoring.

### Quantitative anchor replay

Seed `2026100463` generates four fresh balanced products at each exact
size 40, 48, 64 and 80 bits, plus four previously saved controls.
Reference prime labels come from `gmpy2.next_prime` and are used only for
generation and post-GCD validation. Every method receives only public N.
The four anchor implementations agree on all 675408 compared residues.
Each input/method is timed three times in shuffled order, after imports
are warm. Timings include geometry, centre and axis powers, and output
construction; they do **not** measure a full factorisation.

| Input bits | Native powers, ms | Shared axes, ms | Shared product centres, ms | Existing vector kernel, ms | Fewer centre evaluations |
| --- | ---: | ---: | ---: | ---: | ---: |
| 40 | 0.052 | 0.068 | 0.078 | 1.088 | 0.0% |
| 48 | 0.152 | 0.184 | 0.199 | 1.219 | 0.8% |
| 64 | 1.556 | 1.823 | 1.919 | 3.254 | 3.5% |
| 80 | 29.307 | 26.040 | 26.062 | 25.098 | 6.7% |

These are medians of per-input medians in a shared environment, not a
claimed tuned classical benchmark. At 80 bits product sharing is about
11% faster than the native per-row powers but about 4% slower than our
existing vector kernel; at smaller sizes its setup costs dominate.

All 12 public theorems compile with warnings treated as errors. The
focused check passes 14 linters and audits all 21 module declarations,
including 20 proof declarations with generated helpers: only `propext`,
`Classical.choice` and `Quot.sound` are used. No side-project module is
added to the RH umbrella or ordinary CI.

The remaining quantitative target is to process a **root-preserving**
joined product of many centre-coupled rows implicitly. Cancelling their
centres without retaining the target boundary changes the observable;
retaining them currently leaves an explicit row cost. This is precisely
where a new batching theorem, rather than another cheap scalar group
test, would have to improve the exponent. Harvey already identifies a
full square-root speedup over the Lehman `N^(1/3)` range as a possible
route to `N^(1/6)` in
[his one-fifth paper, Remark 3.4](https://arxiv.org/html/2010.05450).
No universal such batching theorem has been obtained in this pass.

Focused replay, outside normal builds and CI:

~~~bash
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python -B scripts/probe_semiprime_row_structure.py --output docs/semiprime-row-structure-audit.json
lake build RiemannGaussian.SemiprimeRowStructure --wfail
lake env lean -DwarningAsError=true scripts/CheckSemiprimeRowStructure.lean
~~~

## October 2, 2026: implicit Cartesian batching and the literal-centre gap

The follow-up implements one root-preserving bulk operation in
[the probe](../scripts/probe_semiprime_cartesian_completion.py), with
[a complete replay](semiprime-cartesian-completion-audit.json),
[12 public Lean theorems](../RiemannGaussian/SemiprimeCartesianCompletion.lean)
and [a focused checker](../scripts/CheckSemiprimeCartesianCompletion.lean).
The every-run, every-semiprime `Õ(N^(1/6))` bit-operation guarantee remains
**unproved**. The new detector does not provide a universal separating hit,
or a cost proof for recovering a proper factor from every coherent batch.

### What can actually be batched

For two short root lists, `grid_resultant_eq` proves in any nontrivial
commutative ring that

\[
\operatorname{Res}\!\left(\prod_{a\in A}(X-x_a),
                          \prod_{b\in B}(X-y_b)\right)
 =\prod_{a\in A}\prod_{b\in B}(x_a-y_b).
\]

`grid_resultant_eq_zero_iff` proves that over either hidden prime field
this has exactly the union of the original pair collisions as its zero
set. For unit y values, multiplying by their known unit product changes
neither the zeros nor the GCD signal: the quotient target `x_a/y_b=1` is
retained. Repeated roots are retained with multiplicity. The Python replay
checks the signed resultant orientation, including odd list sizes.

`rowAnchor_separatedCentre` connects this directly to weighted rows when
the centre is **additive**, `c(a,b)=r(a)+s(b)`:

\[
V_{a,b}=\frac{g^{aN-r(a)}}{g^{s(b)-b}}.
\]

The implementation reuses the existing classical `MonicBatch` product and
remainder tree, including exact GMP-packed multiplication and monic
division. No unknown field order, factor label, or division by a nonunit
is supplied. This is an implementation and formal root-preservation
result for a classical batching method, not a new resultant algorithm.
See [Harvey's one-fifth construction](https://arxiv.org/html/2010.05450)
for the related factoring use of product polynomials and multipoint
evaluation.

### Quantitative model replay

The timed model fixes a public centre from the primitive corner
`(width-1,width)` and applies that one centre to the entire Cartesian grid.
It does **not** substitute that centre for the literal one in a factoring
algorithm. Seed `2026100487` generates fresh exact 32-, 40-, 48-, 64- and
80-bit products, plus the saved four-rough 79-bit control. Reference primes
are used only for generation and descriptive validation. Every timed call
receives public N and width, and rebuilds its input-specific roots, powers,
integer square root and GCD. Imports are warm; three repetitions shuffle
the method order.

| Input | Width | Explicit pair product, median ms | Implicit resultant, median ms | Detector speedup |
| --- | ---: | ---: | ---: | ---: |
| Fresh 80-bit | 1,024 | 212.42 | 63.34 | 3.35× |
| Fresh 80-bit | 2,048 | 849.24 | 145.67 | 5.83× |
| Fresh 80-bit | 4,096 | 3,388.56 | 323.29 | 10.48× |
| Saved 79-bit control | 4,096 | 3,385.43 | 328.68 | 10.30× |

At width 4,096 the two lists contain 8,192 residues and represent
16,777,216 pairs. The implicit path performs no pair-product loop; the
saved counters include 11,720 polynomial convolutions, 8,191 monic
reductions and 4,096 final point products. Small widths can be slower
because of setup. These shared-environment measurements compare two
evaluations of the **same model**, not two full factoring algorithms.
All 17 large benchmark configurations have GCD one; none is a new
factorisation success.

The exact regression checks 128 batches over eight small composite/prime
rings and 11,968 normalized pair identities. A separate N=77, width-two
regression has aggregate GCD 77; retaining the leaves recovers proper
factor 7 after two leaf GCDs. This tests coherent-batch handling on a toy
input, not a universal recovery bound. The timed replay represents
45,062,144 pairs per repetition and saves every input, value, counter,
timing and runtime-source hash.

### The literal curvature survives

The actual unrounded centre is

\[
c(a,b)=2\sqrt N\sqrt a\sqrt b.
\]

`realCentre_mixed_increment` proves exactly

\[
c(a,b)+c(a+h,b+h)-c(a,b+h)-c(a+h,b)
 =2\sqrt N(\sqrt{a+h}-\sqrt a)(\sqrt{b+h}-\sqrt b).
\]

This factorization is genuine structure in the curvature. It does not
make the modular exponential an additive row/column centre. For the
literal integer centre `ceil(c)`, rounding changes the mixed increment
by less than two. `roundedCentre_mixed_lower` proves, when both weights
and their increments are at most B,

\[
D_{\rm ceil}>\frac{\sqrt N\,h^2}{2B}-2.
\]

For any additive row/column fit, `separated_correction_width` proves that
if all four integer corrections lie in one interval of width W, then
`|D_ceil| <= 2W`. `sixth_regime_correction_gt_budget` therefore proves
that with `B>=4`, `N>=(B-1)^6` and step two, necessarily **W>B**.
This rules out this particular width-B flattening. It is **not** a lower
bound on all algorithms: a longer interval might itself admit sublinear
processing, and an exact nonlinear root-preserving completion is not
excluded.

The saved primitive, balanced four-corner probes show the size of that
boundary without using floating-point centres:

| Input bits | Sixth-root budget B | Mixed integer defect | Required integer correction width, at least |
| --- | ---: | ---: | ---: |
| 32 | 38 | 3,331 | 1,666 |
| 48 | 240 | 134,652 | 67,326 |
| 64 | 1,586 | 6,196,839 | 3,098,420 |
| 80 | 9,880 | 240,772,214 | 120,386,107 |

The correction cannot simply be dropped. `flattening_can_erase_hit`
checks N=77 and primitive balanced corners `(8,11),(8,13),(10,11),(10,13)`.
Their literal centres are 165, 179, 185, 201; matching the first three by
an additive fit predicts 199 at the last corner. The literal anchor is
15 and reveals factor 7, while the flattened anchor is 60 and gives GCD
one. The two omitted units erase the hit. These toy weights exceed N=77's
sixth-root budget; the example certifies failure of the identity, not a
hard-input runtime claim.

### Validation and the remaining research target

The focused build passes with warnings as errors. All 12 public theorems
pass 14 linters; the audit checks all 30 declarations, including 27 proof
declarations with generated helpers, using only `propext`,
`Classical.choice` and `Quot.sound`. The main thread has registered the
proof module in the ordinary library; numerical replay remains optional.
The original replay hashes are retained. Separate validation hashes
record the currently compiled Lean source, including edits since replay;
all executable Python runtime hashes still match the measured replay.

The next required improvement is either a cheap, **exact** batch for the
nonlinear rounded-centre detector, or an independently proved cover that
needs fewer literal rows. A real-valued cancellation or an approximate
centre is insufficient unless the target roots and proper-factor descent
are preserved. The working resultant removes a quadratic pair loop only
where separability is actually established; it does not yet remove that
loop for all semiprime inputs.

The remaining proof obligations are distinct:

1. **Literal batching:** evaluate a root-preserving detector for the exact
   rounded centres, including their coupled correction, at the target cost.
2. **Coverage:** prove that every allowed semiprime supplies a separating
   collision in the searched public-input family; the constant-centre
   benchmark currently supplies no such guarantee.
3. **Recovery:** extract a proper factor even when the aggregate GCD is N,
   with all descent and ambiguous-collision work charged.
4. **Complexity:** prove the complete every-run `Õ(N^(1/6))` bit-operation
   bound, including setup, storage, modular arithmetic and recovery.

The 10.48× model-detector timing and compiled algebra address part of the
first obligation only. They do not discharge any of the four obligations
for the literal universal algorithm.

Focused replay and checks:

~~~bash
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python -B scripts/probe_semiprime_cartesian_completion.py --output docs/semiprime-cartesian-completion-audit.json
lake build RiemannGaussian.SemiprimeCartesianCompletion --wfail
lake env lean -DwarningAsError=true scripts/CheckSemiprimeCartesianCompletion.lean
~~~

## Recording future progress

Append dated entries with the exact observable/algorithm, known input,
sample generation and seed, control/baseline, measured results, mathematical
interpretation and remaining obstruction. Distinguish existing Lean
declarations, newly checked proofs, floating-point evidence and conjectures.

Earlier probes ran in memory through Python heredocs; their historical
aggregate results do not all have complete executable reproductions.
The modular decoder's fresh 108-input replay and the October 2 sparse/batch
probes are now saved as source and JSON artifacts linked above.
Preserve the source hash, seed, corpus,
baseline version and timing protocol when comparing future changes.
Do not conflate a historical prototype with a new replay.

## Primary references

- [NIST DLMF: Dirichlet series](https://dlmf.nist.gov/27.4#E12):
  the von Mangoldt logarithmic-derivative series.
- [SymPy number-theory documentation](https://docs.sympy.org/latest/modules/ntheory.html):
  factorization APIs, factor cache and quadratic-sieve implementation.
- [GNU coreutils factor implementation](https://raw.githubusercontent.com/coreutils/coreutils/master/src/factor.c):
  algorithm context; the linked development source is not a pin of the
  locally installed 8.32 executable.
- [CADO-NFS](https://cado-nfs.gitlabpages.inria.fr/):
  a number-field-sieve implementation for future large-input comparisons.
- [Harvey–Hittmeir, A log-log speedup for exponent one-fifth deterministic integer factorisation](https://arxiv.org/abs/2105.11105):
  weighted factor-sum collisions, sparse sieving and proven complexity.
- [Gao–Feng–Hu–Pan, On factoring and power divisor problems via rank-3 lattices and the second vector](https://eprint.iacr.org/2025/1004):
  a further balanced-semiprime lattice framework.
- [Harvey–Hittmeir, Deterministic methods for finding elements of large multiplicative order](https://arxiv.org/abs/2601.11131):
  large-order-or-factor machinery for rigorous collision searches.
- [Brent–Zimmermann, An O(M(n) log n) algorithm for the Jacobi symbol](https://arxiv.org/abs/1004.2091):
  fast colour acquisition does not by itself supply fast factor decoding.
- [Harvey, 2026 Arizona Winter School notes](https://swc-math.github.io/aws/2026/2026HarveyNotes.pdf):
  accumulating remainder trees and fixed-matrix product batching.
- [Montgomery–Kruppa, Improved Stage 2 to P ± 1 Factoring Algorithms](https://antsmath.org/ANTSVIII/files/kruppa.pdf):
  reciprocal Laurent symmetry, geometric evaluation and two-convolution
  quadratic-extension evaluation; precedents for the phase implementation.
- [Brent–Kruppa–Zimmermann, FFT extension for algebraic-group factorization algorithms](https://maths-people.anu.edu.au/~brent/pd/rpb264.pdf):
  product/remainder continuation, power and Dickson maps, and ECM.
- [Umans–Wang, 2025 factoring framework](https://arxiv.org/html/2511.10851v1):
  conditional one-sixth factoring requires efficiently prefactored structured
  difference covers; sparse signals alone do not satisfy those hypotheses.
- [He–Sahai, 2026 difference-cover obstruction](https://arxiv.org/html/2608.06681):
  a restriction on the one-dimensional arithmetic-progression variant,
  rather than a no-go for every higher-rank construction.
