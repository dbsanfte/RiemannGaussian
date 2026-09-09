# The signed phase bridge and the actual-cutoff RH target

This slice audits the connection between the new phase inequalities and
the literal Suzuki signal, then removes an additional canonical entropy
requirement from a sufficient arithmetic target. The required independent
prime-sum upper bound is still open. No RH theorem with its arithmetic
premise discharged is claimed.

## Prime positivity has a definite direction in the Suzuki bridge

Write

\[
 U(t)=4e^{t/2}-\sum_{n\le e^t}\frac{\Lambda(n)}{\sqrt n}(t-\log n),
 \qquad F(z)=\int_0^\infty U(t)e^{-zt}\,dt.
\]

These are the existing literal `suzukiChebyshevLogAverageLaplaceSignal`
and `suzukiChebyshevLogAverageComplexLaplaceTransform`. The integral is
proved to converge for `Re z > 1/2`. Put `z=lambda+i*v` and

\[
 C_\lambda(v)=\Re(z^2F(z)),\qquad
 D_\sigma(v)=\Re\!\left(-\frac{\zeta'}\zeta(\sigma+iv)\right).
\]

`suzukiPhaseCurvature_prime_identity` proves, for `lambda>1/2`,

\[
 \boxed{C_\lambda(v)+D_{\lambda+1/2}(v)
 =4\lambda+2+
 \frac{\lambda-1/2}{(\lambda-1/2)^2+v^2}.}
\]

The complete real response is

\[
 C_\lambda(v)=(\lambda^2-v^2)\Re F(\lambda+iv)
                 -2\lambda v\Im F(\lambda+iv).
\]

The sine channel is therefore essential. The proved time representation is

\[
 C_\lambda(v)=\int_0^\infty U(t)e^{-\lambda t}
   \bigl[(\lambda^2-v^2)\cos(vt)+2\lambda v\sin(vt)\bigr],dt.
\]

`suzukiPhaseCurvatureResponse_eq_integral` proves both the identity and,
through `integrableOn_suzukiPhase_curvature`, its genuine integrability.
Finite superpositions with arbitrary signed coefficients retain the full
test inside the integral.

For arbitrary real frequencies and summable nonnegative coefficients,
`hasSum_suzukiPhase_curvature` and `suzukiPhase_curvature_add_primeWork`
also prove the complete countable response identity. The full real response
is summable without a second frequency moment. This is not a claim that
an infinitely differentiated time kernel exists under that hypothesis.

The independent prime-power floor from the previous slice gives
`suzukiPhase_curvature_primePower_bound`: an **upper** bound on this Suzuki
curvature combination. It is not the lower bound on `U` required for RH.
All these formulas remain in the proved Laplace half-plane; no inequality
is silently continued through the convergence boundary.

There is also a checked obstruction to discarding the operator's sign.
For the everywhere nonnegative polynomial `1+cos(2*lambda*t)`, its complete
curvature test at `t=0` is `-2*lambda^2<0`.
`suzukiPhaseCurvature_positive_phase_negative_test` proves this for every
positive `lambda`. Positivity of a phase polynomial alone does not make
its Suzuki time test nonnegative.

## The canonical minimization carries an extra entropy cost

At the actual endpoint `N=count+2`, let

\[
 E(N)=\sum_{n\le N}\frac{\Lambda(n)}{\sqrt n}\log(N/n)-4\sqrt N,
 \quad M_N=\sum_{n\le N}\frac{\Lambda(n)}{\sqrt n},
 \quad q_N=\frac{M_N-c}{2\sqrt N}.
\]

Here `c=suzukiArchimedeanSlopeConstant` is the existing fixed constant,
and `q_N` is proved positive. Let `b` be the existing Archimedean
intercept and let `B_N` be the unchanged mass Legendre potential.
`suzukiMassLegendrePotential_eq_actualEndpoint_sub_entropy` proves

\[
 \boxed{B_N=-E(N)+c\log N+b
            -4\sqrt N\,(q_N\log q_N-q_N+1).}
\]

The last term is nonpositive because the relative entropy is nonnegative.
A direct bound on `E(N)` can bypass a separate bound on this entropy term.
The already proved comparison between `B_N` and the canonical gap remains
valid; it is simply not needed for the direct route below.

## Integer cutoffs suffice, with a proved one-sided allowance

For every real `x>=1`, let `N=floor(x)`. The full signed cell identity is

\[
 E(x)=E(N)+M_N\log(x/N)-4(\sqrt x-\sqrt N).
\]

It is proved by `suzukiChebyshevLogAverageError_cell_eq`. The common prime
prefix is retained exactly. Only afterwards, the existing bound
`M_N<=12*sqrt(N)` gives

\[
 \boxed{E(x)\le E(N)+\frac{12}{\sqrt N}.}
\]

This is `suzukiChebyshevLogAverageError_le_floor_add_inv_sqrt`. It controls
every physical point between consecutive cutoffs, independently of a
canonical minimizer and without an entropy estimate.

Consequently the following **still-open arithmetic estimate** suffices:
for some real `C`, `D>=0`, and all sufficiently large natural `N`,

\[
 \boxed{\sum_{n\le N}\frac{\Lambda(n)}{\sqrt n}\log(N/n)
           \le4\sqrt N+C+D\log N.}
\]

`riemannHypothesis_of_suzuki_finite_logAverage_eventually_upper` proves
the full implication to Mathlib's `RiemannHypothesis`. It absorbs finitely
many exceptional cutoffs into a finite constant, pays the interpolation
allowance, and invokes the already checked affine-compensator Laplace
argument. The literal prime-power weights and the original cutoffs appear
in its hypothesis. This is a sufficient condition, not a proof of it.

The research target is therefore an independent **upper** bound on the
complete signed logarithmic-average error. The previous `o(sqrt(N))`
estimates do not provide the displayed logarithmic bound. Another positive
prime-work floor cannot simply be substituted for it.

The logarithmic allowance is one sufficient target. A route giving a larger
but sub-source allowance should still be investigated: it would require
checking the corresponding compensator or direct zero-specific transfer,
not declaring that it fails merely for missing the displayed log rate.

## Validation

`SuzukiPhaseCurvature.lean` contains 11 public theorems;
`SuzukiActualCutoff.lean` contains 10. Both passed direct Lean elaboration
with warnings treated as errors. Focused builds and the full root/default
build passed (9782 jobs). Whole-project declaration lint and both verbose
module lints passed. All 21 public theorem axiom reports were checked and
contain only `propext`, `Classical.choice`, and `Quot.sound` transitively.
The source integrity and whitespace checks passed.

No novelty or new zero-exclusion claim is made. No files were staged,
committed, or pushed, and no remote CI, README, or generated-status update
was performed in this slice. The global goal remains open.
