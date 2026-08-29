# RiemannGaussian agent guide

## Project mission

RiemannGaussian is a research project seeking a complete, kernel-checked Lean
proof of the Riemann hypothesis. The target is Mathlib's
`RiemannHypothesis`; finite models, numerical certificates, asymptotic
experiments, and reformulations are useful only when they strengthen a
rigorous chain to that target.

The proof is not complete. The generated dashboard in
`docs/proof-status.svg` is the canonical compact status summary. At present,
the Gaussian/Weil and Suzuki/contour branches prove that the complete
safe-axis logarithmic defect is asymptotic, with `o(1)` error, to its positive
Poisson linearization, which is exactly height-scaled Blaschke derivative
variation. A checked dyadic Tauberian theorem now identifies decay of those
quantities with `H(T) / T → 0`, where `H` is cumulative upper spectral height.
The literal correctly normalized arithmetic Suzuki `Psi` is now identified
with the transport hinge model, and Lean proves it strictly positive on an
unconditional nonzero punctured neighborhood of the origin. Lean also derives
the transport smooth curvature as the second derivative of the literal
Archimedean term on positive time and proves its exact tail normalization with
computed frozen base value and slope. At the canonical first-event base
`t = log 2`, Lean now proves the exact event cut and strict negativity of the
frozen slope, so the literal tail-positivity criterion has no remaining
base-data assumptions. The literal frozen base value is also proved greater
than `7 / 125`, and the first frozen slope is greater than `-3 / 10`. Exact
curvature bounds then prove the synthetic cutoff-one transport gap strictly
positive, so cutoff zero and cutoff one are both discharged. The remaining
criterion begins at cutoff two, where every prefix contains a future
von Mangoldt event. Lean now identifies the mass and log-moment of every such
complete prefix with exact finite Abel transforms of `Chebyshev.psi`, proves
that its canonical transport point solves the literal Archimedean
slope-matching equation, and rewrites the open gap as the Archimedean value
plus a centered Chebyshev log-moment. Lean now evaluates the continuous
`psi(x) = x` part of that moment in closed form and isolates the remainder as
one explicit boundary term and signed integral against `psi(x) - x`. Exact
Chebyshev mass and Archimedean slope bounds now locate every canonical center
at `r >= log N - 2`; consequently the elementary derivative kernel is
nonnegative and strictly decreasing on every unresolved prefix. Its negative
derivative is a second strictly positive kernel. A checked
absolute-continuity argument rewrites the open moment through the cumulative
error `integral_1^x (psi(u) - u) du`, and a finite Abel identity identifies
that primitive with an exact triangular von-Mangoldt sum minus
`(x^2 - 1) / 2`. Further exact curvature and Chebyshev-mass estimates trap
the canonical center at every endpoint `N` in
`log N - 2 <= r_N < log N + 5`; hence the endpoint coefficient left outside
the cumulative moment is at most `5 * N^(-1/2)` in absolute value. The open
arithmetic statement is therefore a uniform two-level cumulative PNT-error
bound against positive kernels, with its endpoint coefficient now controlled.
Lean further proves that the complete cumulative moment is at most
`45 * sqrt N` in absolute value, the direct boundary term is at most
`25 * sqrt N`, and the full centered PNT remainder is at most `70 * sqrt N`.
Consequently that remainder divided by `N` tends to zero along the canonical
centers. The smooth baseline is now split exactly into a nonnegative
exponential convexity reserve and a lower-order term. The latter is bounded
by an explicit logarithmic envelope and is `o(sqrt N)`. Hence Lean proves the
dimensionless asymptotic frontier
`gap_N / sqrt N = 4 * (exp(delta_N/2) - 1 - delta_N/2) +
PNTError(r_N,N) / sqrt N + o(1)`, where `delta_N = r_N - log N`.
The center equation is now coupled to the same arithmetic measure: if
`E_mass` and `E_log` are its weighted mass and log-moment errors, Lean proves
exactly `PNTError(r_N,N) = E_log(N) - r_N * E_mass(N)` and proves
`E_mass(N) / sqrt N = 2 * (exp(delta_N/2) - 1) + o(1)`. Lean now performs the
corresponding Legendre elimination exactly. For the corrected mass ratio
`q_N = exp(delta_N/2)` and relative entropy
`H(q) = q * log q - q + 1 >= 0`, the literal finite gap is
`gap_N = E_endpoint(N) - 4 * sqrt N * H(q_N) + smooth_correction_N`, where
`E_endpoint` is a direct finite weighted von-Mangoldt sum and the source-exact
correction is `o(sqrt N)`. The missing arithmetic theorem must show that this
fixed-endpoint error dominates the entropy cost uniformly and ultimately
derive a genuine global zero-location constraint. Lean further proves the
quantitative upper bound
`4 * sqrt N * H(q_N) <= (E_mass(N) - smooth_slope(r_N))^2 / sqrt N`, so a
specific fixed-endpoint quadratic mass--moment inequality is sufficient for
every gap and for the uniform tail. Its premise is open and may be strictly
stronger than the exact entropy condition. The fixed-endpoint error now also
has a checked discrete work law
`E_endpoint(N+1)-E_endpoint(N) = D_N-log((N+1)/N)E_mass(N)`, with every smooth
drift `D_N >= 0` and strictly positive evaluated initial margin at `N=2`.
Lean telescopes this into initial margin plus cumulative smooth drift minus
cumulative signed mass-error work, and proves a corresponding block-work
inequality sufficient for the literal tail. For the literal weighted
Chebyshev logarithmic-average error `A_N`, Lean now proves exactly
`E_endpoint(N) = -A_N-log(N)-4` and identifies the cumulative signed work as
`A_N+log(N)-log(2)+4*sqrt(2)+sum D_j`. The exact entropy condition and the
sufficient quadratic majorant are therefore explicit quantitative upper
bounds for this single logarithmic average. Lean further proves
`0 <= D(b,b+1) <= b^(-3/2)` for `b >= 1`, so the smooth drift series is
summable and cumulative signed work minus `A_N+log(N)` converges to an
explicit finite constant. The smooth term therefore cannot provide an
unbounded margin. Lean now extends the literal formula for the logarithmic
average to every real endpoint `b >= 1`, proves each real logarithmic Mellin
atom integrable, and evaluates its weighted integral as the corresponding
von-Mangoldt Dirichlet term divided by `(sigma - 1/2)^2`; the square-root main
term is exactly `4/(sigma-1)`. Lean now also proves absolute summability of
the supported atom norm integrals, performs the infinite sum-integral
exchange, and identifies the complete transform on every real `sigma > 1`
with `(zeta'/zeta)(sigma)/(sigma-1/2)^2 + 4/(sigma-1)`. After exposing every
completed-zeta pole and Archimedean term, Lean proves that this same literal
arithmetic integral recovers the genuine spectral-xi negative logarithmic
derivative at `-i(sigma-1/2)`. Lean also proves genuine integrability and the
global substitution `x=exp(t)`, then complexifies the literal one-sided
Laplace transform on `Re z > 1/2`. It proves integrability of the parameter
derivative, differentiation under the infinite integral, and holomorphy. The
real-ray zeta response extends by the identity theorem throughout that same
half-plane, where the transform recovers the genuine spectral-xi negative
logarithmic derivative at every corresponding complex spectral point. Lean
now cancels the apparent pole at `z=1/2` and constructs a zero-adaptive
completed continuation whose open holomorphy domain contains the closed safe
half-plane and genuinely crosses to `Re z<1/2`. It agrees with the literal
integral on `Re z>1/2`, recovers spectral xi throughout its holomorphic
domain, and has residue `m_rho/(rho-1/2)^2` at every nonzero shifted zeta-zero
coordinate. The original integral is not asserted to converge in the
continued region. Lean now removes the inherited `z^(-2)` normalization and
proves that the pole-cleared response has residue `m_rho` at every shifted
nontrivial zero, without an exceptional-coordinate hypothesis. Applying the
fixed-positive-time heat weights to these arithmetic residues gives exactly
the genuine spectral-xi heat residues, and their absolutely convergent series
sums to the complete existing fixed-time heat. In the same shifted coordinate,
Lean now derives the smooth boundary heat kernel and its full real derivative,
proves its Cauchy--Green source is nonzero on the critical boundary, and proves
an exact arithmetic area--boundary identity for the heat-weighted pole-cleared
response on every zero-free rectangle. Lean also isolates each xi-zero
puncture and proves its shrinking circle integral recovers the exact
moving-kernel residue. It now proves the rectangular base case for excision:
four zero-free rectangles glue around one shrinking square, the square
boundary has the same exact residue limit, and the resulting improper
four-piece area integral converges to the outer boundary minus that residue.
It now proves the same fixed-radius and improper identities for the smooth
heat kernel times an arbitrary principal part `L / (z-c)`, providing the
termwise interface needed for finite principal-part regularization. Lean now
constructs that finite regularization unconditionally on every positive
shifted-coordinate slab of bounded imaginary height: the finite window is
proved complete for the xi divisor, every local multiplicity-weighted
principal part is subtracted, and one analytic representative patches the raw
remainder across all selected zeros. The heat-weighted response is therefore
a proved finite sum of the exact weighted principal parts plus one weighted
analytic remainder away from the divisor. Lean proves the integrability
prerequisite: every weighted principal-part source is locally Lebesgue
integrable through its pole, the project's iterated rectangular area equals a
genuine complex-plane set integral, and the actual finite-window arithmetic
source is integrable through its complete finite xi divisor. Lean also
constructs a single rectangle minus the finite union of common-radius complex
balls and proves its actual-source integral converges to the full planar area.
A checked half-open-square decomposition now identifies the termwise
shrinking-square approximation with that same ordinary through-divisor limit.
The resulting parameter-free finite Cauchy--Green identity states that the
actual arithmetic area equals the outer boundary minus the complete finite
multiplicity-weighted heat-residue sum; the literal common-ball integral
converges to this value. Lean now also retains exactly the selected off-axis
half-divisor on every eligible negative-real rectangle. The real part of the
selected finite heat sum is nonnegative and is strictly positive when its
window contains an off-axis zero; the sum converges to the existing
RH-equivalent boundary-heat total and equals an explicit arithmetic
boundary-minus-bulk functional. Lean now constructs canonical cofinal
rectangles using explicit finite real-coordinate extrema and the existing
quantitative zero-free heights. The corresponding actual boundary-minus-bulk
sequence converges to `2*pi*i` times the complete detector, and its convergence
to zero is equivalent to RH. Its real part is identically zero, while its
imaginary part is exactly `2*pi` times the selected finite heat sum. Lean proves
this scalar is nonnegative, monotone along the quantitative heights, strictly
positive when a window contains an off-axis zero, and zero exactly when that
window is empty. Lean now also constructs a genuine near-edge half-strip
exhaustion: the horizontal sides converge to `-1/2` and `0` while staying an
explicit positive distance from the bounded-height divisor, the vertical
height tends to infinity, and every fixed selected zero enters eventually.
Each stage satisfies the exact filtered positive Cauchy--Green identity.
Lean now passes those non-nested filtered sums to the complete detector by
dominated convergence and obtains a global near-edge arithmetic
boundary-minus-bulk limit. Lean also splits that functional exactly into four
named oriented boundary sides and one bulk term; its imaginary part is
stagewise nonnegative, strictly positive when a selected zero is present, and
converges without height normalization to the complete detector scalar. Lean
now proves a uniform exponential bound for the pole-cleared response across
both selected horizontal sides, including the Archimedean digamma correction.
The fixed-positive-time Gaussian dominates this bound, so both horizontal
integrals tend to zero unconditionally. The live contour frontier is therefore
exactly the two vertical sides minus the bulk. Lean now also splits both the
weighted response and its source pointwise into the genuine xi logarithmic
derivative and the explicit Archimedean regular correction. The regular
correction is analytic on every selected rectangle, so its boundary equals
its bulk exactly; its horizontal sides vanish by the same Gaussian mechanism,
and its vertical-minus-bulk term tends to zero. Subtracting the entire regular
piece leaves the unnormalized detector limit unchanged. The live three-term
remainder is therefore concentrated in the `xi'/xi` component. Lean now
proves this at the integral level rather than only pointwise: both selected
vertical lines lie in the zero-free pole-cleared domain, their interval
integrals split exactly, the bulk split is justified through genuine planar
integrability, and the regular-subtracted functional equals the two explicit
xi-logarithmic-derivative vertical terms minus the explicit xi source bulk at
every stage. This literal three-term functional retains the unnormalized
detector limit. Lean now takes its imaginary part through every integral using
proved interval and planar integrability. The result is a fully real scalar:
two vertical integrals of the real heat kernel times `Re (xi'/xi)`, minus an
explicit planar integral involving both real and imaginary logarithmic-
derivative components. Lean proves that the bulk coefficients are exactly the
two partial derivatives of the real heat kernel, so the remaining source is a
first-order heat-gradient pairing. Turning that pairing into a Green/Dirichlet
or explicit-formula identity with an unconditional vanishing estimate remains
open arithmetic rigidity. Lean now also defines the shifted xi log-norm
potential `U(a,y) = log |xi(1/2+a+I*y)|` and proves away from the divisor that
`U_a = Re (xi'/xi)` and `U_y = -Im (xi'/xi)`. The finite bounded-height divisor
inside every selected rectangle is proved planar-null, so the off-divisor
identity promotes to an almost-everywhere equality, the gradient pairing is
genuinely integrable, and its ordinary planar integral equals the explicit xi
bulk. Both vertical boundaries are zero-free, making the entire live scalar
exactly a boundary-minus-`grad K · grad U` functional with the same
unnormalized detector limit. The xi functional equation and conjugation
symmetry now prove `U` even in its shifted real coordinate; its horizontal
derivative and the real heat kernel are odd, so their boundary product is
even. Lean uses this to reflect the near-`s = 0` left boundary to positive
shifted coordinates in `(1/4, 1/2)`, equivalently actual xi coordinates in
`(3/4, 1)` tending to `1` from below, without changing any finite scalar or
its detector limit. This does not enter the absolute Dirichlet-series region.
Lean further differentiates the reflection symmetries and proves the complete
pairing `grad K · grad U` odd in the shifted real coordinate. Both boundaries
and the entire bulk are now reflected, with genuine through-divisor planar
integrability proved on the positive rectangles. Thus every finite live
scalar is an exact boundary-plus-gradient functional wholly in actual xi
coordinates `1/2 < Re s < 1`; its inner edge tends to `1/2` from above and its
outer edge to `1` from below. No decay in that open strip has been proved.
Lean now also removes the upper-quadrant restriction from the existing paired
Dirichlet-eta construction. On every point of `1/2 < Re s < 1`, its absolutely
convergent paired series equals `(1-2*2^(-s))*zeta(s)`, the elementary factor
is nonzero, and the paired series therefore retains exactly the zeta divisor.
A valid next step must retain the distributional zero contributions in any
Green or integration-by-parts argument; erasing them would merely erase the
detector.
These estimates are not RH and do not exclude a finite or sparse off-line
divisor; a restatement, hidden limit interchange, or conditional implication
is not a substitute.

## Soundness invariant

The repository must remain a continuous, bottom-up Lean proof chain after
every commit.

- Do not use `sorry`, `admit`, introduce custom axioms, use compiler-trusting
  proof shortcuts, or add declarations whose purpose is to assume the missing
  mathematics.
- Do not weaken `RiemannHypothesis`, redefine a frontier quantity to make it
  trivial, hide the frontier in a typeclass or hypothesis, or report a
  conditional reduction as a proof of its premise.
- Lean's standard logical axioms `propext`, `Classical.choice`, and
  `Quot.sound` are permitted. Any other transitive axiom dependency is a
  failed gate unless the user has explicitly approved and documented it.
- Every mathematical progress claim must name a compiled theorem. Comments,
  Markdown, Python output, numerical evidence, and successful examples are
  not proof.
- External research notes are leads, not trusted inputs. Re-derive every fact
  in Lean from already checked definitions and theorems.
- Numerical and symbolic computation may explore conjectures, find constants,
  or produce exact certificates. The final theorem must check in Lean without
  trusting Python or floating-point output.
- Preserve genuine definitions and all analytic side conditions, including
  convergence, integrability, zero avoidance, multiplicity, domains, and
  limit hypotheses. Never silently totalize a singular expression and then
  reason as though the original identity held there.

The compiled project must contain no project-defined axioms. The status
generator rejects any such axiom, even when it is disconnected from a
displayed frontier theorem.

## Proof-slice workflow

Work in one coherent slice at a time. A slice should close a real lemma or
interface needed by the current RH frontier, not merely add parallel
abstractions.

1. Inspect `git status`, the imported theorem chain, the current dashboard
   data, and any newly supplied research dispatch before editing.
2. State the exact mathematical obstruction and the theorem that removes a
   concrete part of it. Check that its assumptions are available upstream.
3. Put new mathematics in a focused module with a module docstring and
   theorem-level documentation. Import it from `RiemannGaussian.lean` so the
   root environment and full build contain it.
4. Compile the changed module directly with warnings treated as errors.
5. Run the whole-package declaration linter, which includes every new public
   declaration. Use its verbose form during an audit when the individual
   results need to be recorded. Fix all findings; do not suppress them merely
   to pass.
6. Run `#print axioms` on the slice's terminal theorems. The result may contain
   only `propext`, `Classical.choice`, and `Quot.sound`.
7. Run the source placeholder scan, whole-project declaration lint, focused
   build, full build, generated-status check, and whitespace check described
   below.
8. Update the README only for stable explanatory changes. Update the milestone
   list in `scripts/GenerateProjectStatus.lean` when and only when a new
   theorem genuinely advances the displayed frontier, then regenerate the
   artifacts.
   The generated panel is a theorem inventory, not a proximity meter: never
   draw a causal edge between milestones unless a checked theorem proves that
   implication, and label RH equivalences as reformulations rather than
   progress on their open direction.
9. Commit and push the complete slice. Wait for GitHub Actions on that exact
   commit SHA to finish successfully before beginning another slice.

Lake builds independent modules in parallel. Direct elaboration of one Lean
module is normally one process; do not mistake that focused check for the
parallel full-library build.

## Commit and check-in invariant

The repository history is the durable record of verified progress. Enforce
this regime yourself; do not rely on the user to request individual commits,
pushes, or CI checks.

- Begin a new slice only from a clean worktree whose current `HEAD` has a
  successful GitHub Actions run with exactly the same full commit SHA.
- Keep one coherent mathematical or infrastructure slice per commit. Do not
  mix unrelated cleanup into it, and do not leave concrete verified progress
  only in the working tree.
- Before committing, stage the complete intended slice and verify the staged
  content with all applicable local gates, `git diff --cached --check`, and
  the tracked pre-commit hook. Documentation-only and CI-only commits are not
  exempt from the gate.
- Do not bypass the pre-commit hook. If an exceptional environment prevents
  the hook from running, execute every command it enforces manually and record
  that fact in the handoff.
- Push each passing commit promptly, record its full SHA, locate the workflow
  run whose `headSha` is exactly that SHA, and require a `success` conclusion.
- While exact-SHA CI is pending, do not start or commit the next slice. If CI
  fails, work only on repairing that same slice, rerun every affected local
  gate, push the repair as a new commit, and verify the replacement SHA.
- Progress reports and handoffs must distinguish local success from remote
  verification and should cite both the exact commit SHA and CI run number.

## Mandatory local gates

Use the repository's pinned Lean toolchain. In environments where `lake` is
not already on `PATH`, invoke the pinned binary through the configured
`ELAN_HOME` rather than changing the project version.

Enable the tracked pre-commit gate once in every fresh clone:

```bash
git config core.hooksPath .githooks
```

The hook repeats the staged placeholder scan, warning-as-error build,
whole-project declaration lint, compiled-environment/dashboard audit, and
staged whitespace check. CI remains authoritative because local hooks can be
bypassed and a partially staged commit may differ from the working tree.

For a changed module `RiemannGaussian/NewSlice.lean`, the minimum gate is:

```bash
lake env lean -DwarningAsError=true RiemannGaussian/NewSlice.lean
lake env lean -DwarningAsError=true /tmp/RiemannGaussianAudit.lean
if git grep -nE '\<(sorry|admit|sorryAx)\>' -- '*.lean'; then exit 1; fi
lake env lean -DwarningAsError=true scripts/LintProject.lean
lake build RiemannGaussian.NewSlice --wfail
lake build --wfail
lake env lean -DwarningAsError=true scripts/GenerateProjectStatus.lean
git diff --exit-code -- docs/proof-status.json docs/proof-status.svg
git diff --check
```

The temporary audit file must import the root library. Its verbose lint command
and explicit axiom commands for terminal theorems have this form:

```lean
import RiemannGaussian
import Mathlib.Tactic.Linter
#lint+ in RiemannGaussian
#print axioms RiemannGaussian.newFrontierTheorem
```

The generator is also a soundness gate. It scans every declaration in
compiled project modules for indirect placeholder dependencies, rejects all
project-defined axioms and disallowed transitive axioms, and verifies that
every green dashboard milestone is an actual project theorem using only the
three permitted standard axioms.

## GitHub gate

Do not infer remote success from a local build or from a workflow attached to
another commit. After pushing:

1. Record `git rev-parse HEAD`.
2. Locate the GitHub Actions run whose `headSha` is exactly that value.
3. Wait for it to finish and require conclusion `success`.
4. Confirm the worktree is clean before starting the next proof slice.

If CI fails, repair the same slice, rerun every affected local gate, push the
repair, and verify the new exact commit. Never stack a new mathematical slice
on an unverified commit.

## Research discipline

- Prefer exact identities, coercion lemmas, summable dominators, and explicit
  quantitative estimates that can be reused downstream.
- Distinguish finite-window, infinite-sum, boundary-limit, and large-height
  statements in names and hypotheses.
- Treat division, logarithmic derivatives, contour deformation, exchanged
  limits, derivatives under integrals, and sum-integral swaps as proof
  obligations requiring their own hypotheses and Lean theorems.
- New mathematics is welcome. Grow it from the checked chain, isolate its
  genuinely novel lemma, test finite or numerical shadows when useful, and
  then prove the general statement in Lean.
- Never claim RH is proved until the completion audit reaches an unconditional
  term of `RiemannHypothesis` and all local and exact-commit remote gates pass.
