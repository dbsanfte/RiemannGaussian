# Actual sixth-power symmetry and the remaining determinant source

2026-10-19. This continues the [small-window audit](arithmetic-operator-theta-support-small-window.md) and the [Siegel interpolation review](siegel-interpolation-review.md). The new work proves an actual finite-profile symmetry, closes a class of ordinary-logarithm source tests, and identifies the exact arithmetic correlation exposed by the unsaturated product. It supplies no independent RH inequality or extension of the imported strict `Re(s)>7/8` endpoint.

## The actual native coefficient passes the sixth-power test

The previous modulus-72 example remains correct: a primary good unit can have sixth power 37 rather than 1 modulo 72. Periodicity alone was insufficient. The actual coefficient has more structure.

[QuasiRHNativeRaySixthAudit.lean](../scripts/QuasiRHNativeRaySixthAudit.lean) proves that the repo's literal `numeratorBadTwist` is unchanged under multiplication of its argument by a supported sixth power, at **every input**, including zero and nonunits. Its sixth power is exactly the native principal-support mask. The apparent modulus-8 difficulty disappears because the actual quadratic supplement depends on the Eisenstein norm: multiplication by 37 changes that norm by `37^2`, which is 1 modulo 8.

The theorem also reaches the actual canonical calibration, fixed physical ray and primary numerator mask. Writing their existing assembled coefficient as `H`, it proves

\[
H(nx^6)=H(n)\,\mathbf1_{(x,C)=1}.
\]

Here `C` is the original calibration generator. The exclusion is essential; merely being good at 2 and 3 does not make a prime coprime to the whole calibration. The original masked `lowArithmeticCoefficient` is likewise invariant under admissible sixth-power multiplication.

This closes the **finite arithmetic profile** requirement. It does not identify the transformed sextic residue with a published fixed-cusp vector, with the imported cubic theta coefficient, or with the Patterson model. Norm-height phases, Gaussian profiles, spectral cube strata and marked coefficients still need their exact analytic assembly. See the [native proof audit](../.lake/arithmetic-operator-native-ray-sixth-gate/preflight.md).

## A larger fixed determinant does not repair the ordinary-log source

The [paper-level class theorem](../.lake/arithmetic-operator-fixed-qdet-source-gate/preflight.md) applies to a fixed-size determinant built from finitely many sums/products of Gaussian binomials with fixed integer affine indices and fixed integer base `b>=2`. Indices must be admissible on a tail. The polynomial degrees may grow quadratically; the **construction complexity** is fixed. The theorem does not cover arbitrary varying bases, floor/residue-coded indices, growing matrix sizes or physical prime-power phases.

Join the determinant before taking its logarithm. Exact Gaussian reciprocity and the convergent q-product express it as finitely many quadratic-height groups with meromorphic germs in `b^(-n)`. Either the whole determinant vanishes eventually, or

\[
D_n=c\,b^{An^2-\ell n}\bigl(1+O(b^{-n})\bigr),\qquad c\ne0.
\]

Thus its ordinary logarithm, after retaining **both** the polynomial height and `log|c|`, has an exponentially small residual. Its row-index Dirichlet series has only the possible elementary poles at 3, 2 and 1; the completely centered series is entire. There is no required off-line zeta-zero pole in this observation. More fixed-order cancellations change `ell`, not this conclusion.

[ArithmeticOperatorFixedQLogAudit.lean](../scripts/ArithmeticOperatorFixedQLogAudit.lean) checks the conditional analytic-germ step, including a vanishing germ at the origin, eventual nonzero samples, the exact logarithmic constant, and summability of every polynomial absolute moment of the residual. The general Gaussian-to-germ identification, grouping of quadratic heights and entire-continuation conclusion are **paper-level**, independently reviewed. The 1,336 integer/Fraction regressions include actual rank-two and rank-three determinants with equal leading areas; they do not certify an infinite analytic claim.

Freeze this ordinary-log source test for the stated class. Do not extrapolate it to row Möbius reweighting, which can reintroduce `1/zeta`, or to prime-power packets whose valuation depths carry a phase.

## Above the saturated window, the exact prime trace is a shifted-divisor statistic

Let the same once-counted integer product be

\[
C_N(b)=\prod_{2\le n\le N}\Phi_n(b).
\]

For `p>N`, the new [ArithmeticOperatorQDetUnsaturatedTraceAudit.lean](../scripts/ArithmeticOperatorQDetUnsaturatedTraceAudit.lean) uses actual integer bases representing each nonzero residue modulo `p`. It proves

\[
\#\{b\bmod p:p\mid C_N(b)\}
=\sum_{\substack{d\mid p-1\\2\le d\le N}}\varphi(d).
\]

The proof uses exact cyclotomic root orders and the cyclic finite field. It is not an assumed equidistribution of prime orders. The base representatives are at least two; the artificial integer base one is never used.

Consequently the complete base trace, normalized by `p`, has prime weight `1-1/p` through `N`, and the displayed truncated divisor sum divided by `p` above `N`. Character orthogonality separates the latter into the reference `(N-1)/p` plus **all** nonprincipal characters modulo `2,...,N`. On the window `N<p<=X`, that exact remainder is

\[
E_N(y)=\sum_{d=2}^{N}\ \sum_{\substack{\chi\bmod d\\\chi\ne\chi_0}}
 \sum_{N<p\le X}\frac{\log p}{p^{1+iy}}\chi(p).
\]

It cannot be deleted: at `N=22,p=47`, the literal weight is `1/47`, its principal reference is `21/47`, and the character correction is `-20/47`. This is one finite witness, not a statement about an infinite prime population.

The [unsaturated source audit](../.lake/arithmetic-operator-qdet-unsaturated-gate/preflight.md) retains every proper prime power and the exceptional prime 2. It proves at paper level that their total complete-trace mass is `O_eta(N^(1/2+eta)(1+log N))`, uniformly in the outer cutoff. Taking `eta<beta-1/2` pays that entire portion below any candidate `N^beta` source. This removes a genuine error term; it does not bound the prime-layer correlation.

The character and Mellin arguments are also paper-level. For `X=N^kappa`, the principal reference's Mellin residue at a matched zero of multiplicity `m`, chosen rightmost at its **fixed ordinate**, is `-m/[beta(1-beta)]`. This is an **N-scale** source; no globally rightmost zero is assumed. The complete trace's source is not established because `E_N` may cancel it. Averaging separately over a complete residue system for each prime is not a free replacement for one common finite integer-base interval. The period discrepancy and height cost remain.

This isolates the next source gate: a new estimate must control the *joint* growing-modulus character correction or establish that it preserves the zero source in the actual common-base construction. Existing principal-density or generic order-average statements are insufficient. Do not build a larger carrier around the unproved source.

## The whole-divisor Type-I reordering gives no new rate

The separate [joined Type-I audit](../.lake/arithmetic-operator-joined-divisor-typei-gate/preflight.md) retains the full physical sextic residue, moving profile and model. On a divisor block `Norm(D)~L`, its exact joined coefficient has bound

\[
\|\alpha\|_2\ll L^{1/2}S^{-5/6+\epsilon}.
\]

Applying the already used full-residue Type-I input recovers `Z^(61/144-d/6+epsilon)`. This application is paper-level and conditional on rStation8/v1, an AI research preprint whose analytic theorem is not imported into Lean. It is **the same prior allowance**, still too large by `Z^(17/72+d/3)` against the old comparison scale. Reindexing `n=Dm` retains `rho(Dm)`; it does not turn the theorem's numerator length into `K/D` for free. Empty short-n incidence blocks leave an explicit affordable density boundary. The first Voronoi pole is not cancelled by the second-density identity.

Freeze that reordering as a proposed improvement. A genuinely new theta estimate would have to retain the complete additive-fraction/residual coupling and the actual finite profile proved above; another divisor norm bound is not such an estimate.

## Scope of the checkpoint

The [validation record](arithmetic-operator-joined-typei-ray-window-gates.json) separates strict Lean leaves, exact finite checks and paper-level analytic arguments. All prior results and scoped no-gos are preserved. These tests resolve applicability and source questions; they do not furnish a signed bound for an RH endpoint. Work remains local. The roadmap is active: eight Tier-1 families visited, none exhausted.
