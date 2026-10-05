# Prime-moment arithmetic frontier

The Riesz campaign is now treated as a checked reduction. The active
all-height arithmetic task is **non-coherence of the literal ordinary-prime
moments**, at every fixed height and every `1/2<u<=10001/20000`, for every
positive analytic multiplicity. No internal Riesz rearrangement earns
progress unless it supplies genuinely new arithmetic information.

The exact [canonical endpoint](zeta-prime-moment-noncoherence.md) composes
exposed-zero selection, the forward moment source, and the converse
`exists_zero_multiplicity_of_tendsto`. It does not assume a rightmost zero.
Block L² deviation and positive limsup are sufficient corollaries, not
the canonical premise. The premise is still open at uncovered heights.

## Exact Chebyshev-error representation

The new checked leaf
[`ZetaPrimeMomentChebyshev`](../RiemannGaussian/ZetaPrimeMomentChebyshev.lean)
uses the actual von Mangoldt sequence. Set

\[
s_0=3/2+iy,\quad c=s_0-1,\quad
e(t)=e^{-t}\psi(e^t)-1,\quad
E_k(c)=\int_0^\infty e(t)\frac{t^k}{k!}e^{-ct}\,dt.
\]

Every integral is genuinely integrable for `Re(c)>0`. The elementary
Chebyshev bound proves `|e(t)|<=5`; it is used for domination, not to bound
the source. The global substitution `x=exp(t)` and the L-series integral
formula prove, on `Re(s)>1`,

\[
-\frac{\zeta'}{\zeta}(s)
 =s\int_1^\infty\psi(x)x^{-s-1}\,dx
 =\frac{s}{s-1}+s\int_0^\infty e(t)e^{-(s-1)t}\,dt.
\]

For every **positive** factorial order `k`,

\[
\boxed{
a_k(u,y)=u^{k+1}\left[
c^{-k-1}+s_0E_k(c)-E_{k-1}(c)-Q_k(s_0)
\right],}
\]

where `Q_k` is the explicit proper-prime-power moment. In particular the
actual error occurs in the single centered signed integral

\[
s_0E_k(c)-E_{k-1}(c)
 =\frac1{k!}\int_0^\infty
 (\psi(e^t)-e^t)e^{-s_0t}
 \left(s_0t^k-kt^{k-1}\right)\,dt.
\]

`ordinary_moment_eq_psi_error_integral` proves the literal formula with
`k+1` indexing. The full phase `e^{-iyt}` stays inside this integral.
Order zero is retained separately by
`ordinary_moment_zero_eq_error`: its elementary term is `s_0/(s_0-1)`.
Dropping the extra constant there would lose a boundary term.

For `0<=u<1` and `|y|>=1`, the main-density moment and proper powers tend
to zero independently. `errorSource_tendsto_iff` proves that the original
moment limit is exactly the same limit for the normalized centered signed
error integral. This statement has no exposure or Riesz premise. It does
**not** assert that the literal error integral converges at `s=rho` below
the Euler half-plane, or that convergence of moments forces a pointwise
asymptotic expansion of `psi`.

## The persistent component

Put `rho=s_0-u`. A diagnostic Chebyshev component is

\[
\psi(x)-x=-\frac{m}{\rho}x^\rho,
\qquad e(t)=-\frac{m}{\rho}e^{(\rho-1)t}.
\]

`componentMoment_eq` evaluates its exact complex Laplace moment.
`component_exact_source` proves

\[
u^{k+1}\left[s_0E_k(c)-E_{k-1}(c)\right]=-m
\quad(k\ge1).
\]

The cancellation uses `s_0-u=rho`, not a norm bound. A conjugate component
restores a real signal; at fixed nonzero height it is separated from the
selected channel. This is a calculation of the component's response,
not a claim that the actual Chebyshev error consists of that one term.
The already-checked positive continuous-density model retains that
common phase and reproduces source `-1` with every factorial order kept.

## Strength audit of proposed external constraints

[`ZetaPrimeMomentArithmeticAudit`](../RiemannGaussian/ZetaPrimeMomentArithmeticAudit.lean)
proves the following rejection test, for every fixed `delta>0`:

\[
\ell(t)/t\to0\quad\Longrightarrow\quad
e^{-\delta t+\ell(t)}\to0.
\]

Here `delta=1-Re(rho)=u-1/2`. Consequently a fixed below-one mode is
eventually smaller than **every** subexponential relative-error envelope
`exp(-ell(log x))` with sublinear loss. The theorem is applied to the
existing continuous density, not an arbitrary per-prime phase assignment:
`positive_coherent_model_with_subexponential_error` gives a positive
density on an unbounded half-line, a coherent moment limit `-1`, and
vanishing relative error against all these envelopes simultaneously.
This is not a counterexample involving ordinary integer primes.

| Candidate constraint | Audit result |
| --- | --- |
| Positivity, common phase, log/factorial coupling, Hankel positivity | The positive continuous model passes them; they cannot independently exclude coherence. |
| Classical or VK-scale PNT errors | Their loss exponent is sublinear in `log x`; the checked strength audit permits a fixed `x^rho` component. |
| Generic full Selberg/Riccati symmetry or a normalized trace | Existing `ZetaRieszSelbergRenewalAudit` retains positivity and the full second convolution while preserving source `-1`; do not reuse that generic mechanism. |
| Actual integer identity `sum_{d|n} Lambda(d)=log n` and its logarithmic convolution | The literal integer identity is already available in `SuzukiLogarithmicConvolution`, but no quantitative source-breaking estimate follows from it alone. Its signed Möbius remainder still needs independent control; analogous identities also exist for generalized prime systems. |
| Averaged-height or averaged-modulus estimates | An average does not by itself prohibit one coherent fixed height. A proposed use must supply the missing uniform fixed-height conclusion. |
| Pair-correlation / random-variance predictions | Not unconditional inputs of the required strength; do not replace a hypothesis or numerical model by a theorem. |

For example, Johnston–Yang prove the explicit envelope
`9.39 x (log x)^1.515 exp(-0.8274 sqrt(log x))`.
It has the insufficient asymptotic scale just audited.
([paper](https://arxiv.org/abs/2204.01980))
Bellotti's newer PNT result optimizes the error obtained from a VK
zero-free region, but remains in the sublinear-loss class.
([paper](https://arxiv.org/abs/2508.02041))
Selberg's original scale-to-scale asymptotic identity has an `O(x)`
remainder. A fixed `x^beta log x`, `beta<1`, is smaller than that scale;
that remainder cannot itself prohibit this persistent component.
([original paper](https://www.math.lsu.edu/~mahlburg/teaching/handouts/2014-7230/Selberg-ElemPNT1949.pdf))
This last comparison is a strength audit, not a proof that an arbitrary
continuous model satisfies the literal integer divisor identities.

Adding a generic Euler product is not yet enough to distinguish ordinary
primes. Broucke constructs Beurling zeta functions with infinitely many
zeros on prescribed contours and studies the corresponding PNT error.
([primary paper](https://arxiv.org/abs/2507.13780))
Révész also constructs generalized prime systems with a given zero and
Chebyshev error bounded on its power scale.
([primary paper](https://arxiv.org/abs/2202.01837))
These are external generalized-prime counterexamples, not Lean imports
and not counterexamples for the ordinary primes. They sharpen the
candidate test: a proposed mechanism must use information that
distinguishes the actual integer prime sequence, or verify why its
quantitative assumptions exclude these generalized systems. No functional
equation or ordinary integer spacing is attributed to those constructions.

**Decision:** no sufficient published or existing repo estimate was found
in these tested mechanisms. Stop these generic PNT/positivity/Selberg
routes. A new useful theorem must exploit actual prime arithmetic across
infinitely many growing scales and exclude the fixed-height centered
error component. The canonical target remains non-coherence; no new floor
formulation has been substituted for it.

## Finite-height coverage, kept separate

[`ZetaPrimeMomentRegionCoverage`](../RiemannGaussian/ZetaPrimeMomentRegionCoverage.lean)
extends the Cauchy-radius transfer from `log(|y|+3)<=1800` to
`log(|y|+3)<=2000`, for `|y|>=54`, using the **already discharged**
signed-pole region. It proves a full arithmetic radius

\[
R=500051/1000000>10001/20000,
\qquad
\|a_k(u,y)\|\le C_y(500050/500051)^k
\]

uniformly for all `0<=u<=10001/20000`. Thus actual moments tend to zero
and are non-coherent at those covered heights. This is a transfer of
existing zero-free coverage, not a new region or all-height cancellation.
The full analytic disk is used; an exposed competing-mode disk cannot
substitute for it.

The primary literature audit identifies these import leads:

| Input | Published open-edge width | Proof-import status |
| --- | --- | --- |
| Bellotti–Trudgian–Yang (2026), Theorem 1 | `1/(4.896 log |t|)`, `|t|>=3` | Analytic proof and finite verification inputs not imported into Lean. |
| Yang's explicit Littlewood region | `log log |t|/(21.233 log |t|)`, `|t|>=3` | Actual analytic region proof not imported. |
| Bellotti's published VK region | `1/(53.989 (log |t|)^(2/3) (log log |t|)^(1/3))` | Actual analytic region proof not imported. |
| Yang thesis refinements reported in the 2026 paper | `19.62` and `51.34` replace the last two constants | Original thesis proof not independently audited here; not used as a checked input. |

The 2026 paper proves Theorem 1, while its `4.8594` Theorem 2 is presented
as dependent on establishing Lemma 2. This pass does not adopt the latter
as an unconditional input. It also retains the open inequality in the
theorem rather than using a stronger edge suggested by its abstract.
([primary source](https://arxiv.org/html/2603.21490v1))

`analytic_radius_of_explicit_region` is the checked adapter for a future
proof import. Its `hregion` premise is literal zeta nonvanishing, and its
width lower bound must hold on the **whole disk**, including ordinate
perturbations. No paper is installed as an axiom and no benchmark-width
comparison is reported as an imported analytic theorem.

The optional 90-digit preflight finds positive endpoint width margins at
logarithmic heights 3900 (BTY) and 8200 (Yang). These are numerical import
leads, **not checked coverage**: their modern nonvanishing proofs remain
unavailable in the compiled chain. Even importing them would extend only
finite-height coverage of the fixed campaign width.

## Validation and limits

The scoped Lean gates run namespace linters and collect the transitive
axioms of every declaration, including private helpers. The
[local proof audit](prime-moment-error-frontier-audit.json) records those
results, the exact theorem domains and the unimported literature inputs.
The optional
[`probe_prime_moment_error_frontier.py`](../scripts/probe_prime_moment_error_frontier.py)
tests analytic countermodel scales and width margins only. It does not
sample an actual complete prime population, certify a cofinal bound, or
run in ordinary CI.

The original checks were scoped. The
[terminal checkpoint](zeta-riesz-terminal.md) now registers this work in the
ordinary root and explorers; its
[publication audit](prime-moment-terminal-publication-audit.json) records
the wider gates separately. All previous proofs, no-go audits and semiprime
work are preserved. No global arithmetic floor, ceiling, all-height
non-coherence estimate, new zero exclusion or RH proof is claimed.
