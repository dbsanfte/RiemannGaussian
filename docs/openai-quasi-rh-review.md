# OpenAI quasi-RH: proof review and campaign consequences

Review date: 2026-10-07. Upstream revision:
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

The main project now imports the pinned `7/8` proof through
[ZetaQuasiRHOpenAI](../RiemannGaussian/ZetaQuasiRHOpenAI.lean), with Lean
4.34.1 and matching dependencies. The
[integration record](zeta-riesz-quasi-rh-discharge.md) describes the
unconditional frozen endpoint and its current-project verification.
This review preserves every existing no-go audit and the earlier isolated
verification history. Both the `23/24` intermediate theorem and the
unconditional `7/8` zeta/Dirichlet endpoints passed that isolated rebuild
and transitive standard-axiom check before integration.

## Exact result and current verification boundary

The [formalization scope](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/docs/003.md)
states all-height nonvanishing on `Re(s) > 7/8` for Riemann zeta, every
Dirichlet L-function, and finite-order Hecke L-functions over the
Eisenstein field. Principal-character poles are excluded where needed.
The boundary `Re(s) = 7/8` is not excluded. This is not RH.

The actual [zeta theorem](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/DirichletL/Nonvanishing.lean#L26)
targets Mathlib's `riemannZeta`, with only `7/8 < s.re` as an assumption.
Its proof calls `ProbeFinalAssemblyUnconditional.zeta_nonzero`.
The comparator's `sorry` is a statement template, not this solution.

The pinned final-assembly source closure contains 2,923 OAI modules,
25,007,954 bytes. Static inspection found no `sorry`/`admit` occurrences
or explicit new axiom declarations in that closure. This is source
inspection, not by itself a kernel-verification result. The isolated review
then completed the actual endpoint build (7,061 jobs) and audited its
transitive axioms: exactly `propext`, `Classical.choice` and `Quot.sound`.
The review build
uses the upstream's own Rellich and PrimeNumberTheoremAnd compatibility
patches; omitting them produces dependency API errors.

The smaller `23/24` baseline excludes `s=1` explicitly. Its isolated audit
also wraps this into the total-function statement using Mathlib's existing
`riemannZeta_one_ne_zero` at that one point. This is only the convention for
the total function; it does not assert that the meromorphic pole is analytic.
The general local transfer is compatible with that wrapped statement.

The baseline audit returned exactly `propext`, `Classical.choice` and
`Quot.sound`. A separate native campaign audit also passed: it proves
`riemannZeta s != 0` for `19999/20000 <= s.re` and nonvanishing of the
literal candidate `3/2-u+i*y` for every `u <= 10001/20000` and every real
height. Neither endpoint assumes exposure or simplicity. This is an
unconditional isolated-toolchain checkpoint credited to the upstream
theorem. The later main-project integration instantiates the same transfer
with the stronger checked `7/8` import.

The completed stronger audit checks `reviewed_quasi_rh`, the original
closed campaign corollary, every candidate `3/2-u+i*y` with `u<5/8`,
and the actual upstream Dirichlet-L endpoint for all positive moduli.
Every one has only the same three standard axioms. The completed build
and audit are recorded in `seven-eighths-build.log`,
`seven-eighths-axioms.log` and `verification-status.json` under the isolated
review directory. There is no new axiom connecting toolchains.

## Checked transfer to our frozen endpoint

[ZetaRieszQuasiRHDischarge](../RiemannGaussian/ZetaRieszQuasiRHDischarge.lean)
takes the exact external nonvanishing statement as a theorem parameter.
It has locally checked consequences:

* Nonvanishing throughout the original closed campaign
  `Re(s) >= 19999/20000`, at all heights and all multiplicities.
* Strip-wide prime-moment non-coherence and the terminal
  `ZetaPrimeMomentTerminal.NoPersistentError` condition.
* Non-coherence on every radius strip `1/2 < u <= U < 5/8`.
* A fixed Cauchy disk of radius `3/5` around `3/2 + i*y` for `|y| >= 54`.
* An explicit geometric estimate for the existing coupled energy `D-Q`:

  ```text
  |D_N(u,y) - Q_N(u,y)|
      <= (41/12) C_y^2 (10001/12000)^(N-1),   N >= 65536.
  ```

The last bound keeps the whole correlation credit, every moment order,
and the original complex phase. Its ratio is approximately `0.833417`,
strictly below one. It follows by applying our existing arithmetic-radius
theorem to the external half-plane, not by solving the old Riesz floor
internally. The main-project `ZetaQuasiRHOpenAI` module now instantiates
these transfers with the pinned proof, giving unconditional versions of
all these conclusions through the ordinary root.

## What is new relative to our audited mechanisms

The [main paper](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf)
compares reflected and Poisson representations of completed metaplectic
theta sums. Cubic indices, sixth-power-free dual rows, residue characters
and zero-on-nonunit masks stay coupled. Its marked inverse and plain
moments use the same row character and height. These are structured
arithmetic-family estimates, not bounds for arbitrary twisted weights.

The specific estimate to study next is Lemma 18.1, together with Lemma
17.1 and their finite-width inductions. Equal-product-scale comparisons
retain both profiles through transformations so exceptional main terms
cancel before estimation. The hypothesis is not transferable to arbitrary
hard masks or unrelated prime pairs. A separate exact bridge would be
needed for any such application to our carriers.

This supplies a plausible missing constraint in our operator search:
actual finite-field residue characters coupled to the actual Eisenstein
lattice and its reflection/Poisson identities. Our free-weight and
deleted-prime controls are not endowed with these identities. That is
a reason to test the mechanism; it is not itself an independent bound for
any of our open sums.

## The reusable analytic closure

[HeckeCommonProbe](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/DirichletL/Hecke/CommonProbe.lean)
works with a supremum of zero real parts, not an attained rightmost zero.
Its sufficient contract has a physical probe `J`, a nonvanishing
holomorphic correction `H` with `norm(H-1) <= 1/2`, and:

```text
J(Z)                  = O(Z^(3/16 + omega)),
J(Z) - signal(Z)      = O(Z^(beta_* - 11/16 - sigma)),
0 < omega < beta_* - 7/8,   0 < sigma.
```

The positive exponent margins are shared across the character family;
constants and eventual thresholds may depend on the target character.
This closes by reciprocal continuation past the supremum. It avoids the
rightmost-attainment issue encountered in our earlier masked-mode work.
The contract alone is a reduction; its arithmetic construction is essential.

## What still obstructs RH and the next priorities

After the published bound is imported, the unresolved right half becomes
`1/2 < Re(rho) <= 7/8`, equivalently `5/8 <= u < 1`. Our existing narrow
Riesz campaign is covered; the Gaussian/Weil and Suzuki all-zero endpoints
are not discharged.

The paper's exponent balance explains why replacing `7/8` by `1/2` is
not a parameter substitution. Its low exponent is `3/16`; its signal
exponent at `1/2` would be `-3/16`. Keeping this probe would require a
further `3/8` power improvement, or a genuinely different calibrated
comparison. The current proof provides neither automatically.

[ZetaQuasiRHProbeCalibration](../RiemannGaussian/ZetaQuasiRHProbeCalibration.lean)
checks a stronger, narrowly scoped scale preflight. Retain the algebra of
equations (12.4), (15.6) and (15.9), with `x=l_x`, `y=l_y`, total slot
length `ell`, `h=1+ell-x`, and `b=y-x`. Then:

```text
low exponent       = x/2 + (y-x)/12,
signal exponent    = beta + x/2 - 1 + (1+ell-x)/6,
calibrated boundary= 5/6 + (x+y-2ell)/12.
```

The fully rescaled term in the finite modification subtracts `ell` from
both averaging lengths. Even imposing only the necessary nonnegative
length conditions `ell <= x,y`, the retained formula has boundary at
least `5/6`. With `x+y+ell=1` it is `11/12-ell/4`, and `ell <= 1/3`.
The published parameters recover `7/8` exactly. A nonzero diagnostic
complex power mode at or left of `5/6` obeys this low allowance at every
scale, even with comparison error identically zero.

This is an exponent-only obstruction for this retained formula and
rescaling class. The paper proves its estimates at its stated geometry;
the preflight does not extend those estimates to arbitrary new scales or
claim a `5/6` zero-free theorem. Nor does it rule out stronger coupled
arithmetic, other comparisons or the metaplectic framework. It tells us
to seek a stronger joint low estimate instead of optimizing slot lengths
within this formula. The focused local audit passed 14 linters and
checked all 33 declarations (29 theorems including generated helpers)
with only standard axioms. It is separate from the 86-module audit.

The same leaf checks a centering preflight without taking any norm. For
arbitrary finite complex comparison coefficients, the diagnostic power
signals at ANY two exponents/heights differ by one common nonzero factor.
Thus exact cancellation at one reference exponent cancels every other
source if only geometric scales change and the normalized Mellin shape
stays common. This is not an identity for the entire physical probe or a
claim that its exceptional Gram mean was canceled. The actual principal
signal in equation (10.3) has this same affine scale dependence. Any
proposed physical centering must therefore verify a genuinely different
Mellin factor or a joint cancellation preserving the principal signal.

## Next coupled-estimate gate

The specific loss in Proposition 15.2 is the `Pa^(1/6)` exceptional
Fourier-frequency allowance. Nonexceptional frequencies have a vanishing
complete CRT mean; the remaining frequencies have sixth-power form
outside the frozen bad/common primes. Lemma 18.1 removes analogous
exceptional main terms in its long-product case by an equal-product-scale
comparison, retaining the same character, mask and norm twist.

These are different uses of the transforms. It is not yet proved that
the latter cancellation applies to the former Gram allowance. In
particular, centering the normalized principal signal itself fails the
source preflight above. The next useful estimate must join the actual
additive and completed-theta row factors BEFORE their separate
Cauchy--Schwarz bounds, or construct a profile comparison whose exact
principal Mellin factor remains nonzero at the target. An identity-only
row reindexing or a sharper bound for arbitrary coefficients is not that
estimate. Extending toward RH also needs continuation/control of the actual Euler
correction and the full high comparison beyond their supplied domains.
The principal correction has now been extended separately as detailed
below; this does not extend the complete three-variable contour estimates.

The checked low-side strength target at the fixed published geometry is
exactly:

```text
3/16 - gain < 1/2 - 11/16    iff    gain > 3/8.
```

A full square-root saving across the `5/6`-width row family would have
`gain=5/12` and leave margin `1/24`. This is a hypothetical benchmark,
not an arithmetic independence, random-phase or row-cancellation theorem.
Nor is a low-side saving alone sufficient: the high comparison and Euler
correction would also need valid continuation/control toward `Re(s)=1/2`.

Perfect removal of the entire `Pa^(1/6)` allowance would only remove the
`(l_y-l_x)/12=1/96` loss after the existing Cauchy--Schwarz step. At the
published geometry its calibrated boundary would still be `83/96`, with
critical-line exponent gap `35/96`. The same leaf proves these exact
rational identities and that a nonzero critical-line power signal obeys
that hypothetical strengthened allowance at every scale. This is not a
proof of a `83/96` region: the exceptional cancellation, stronger high-side
comparison and required Euler-correction continuation have not been proved.
It rules out treating exceptional-frequency removal alone as the missing
RH-strength saving.

A separate native preflight, `verification/PrincipalMaskAudit.lean`, has
also passed its standard-axiom check against the pinned upstream imports.
It uses the actual `sixthFrequencyEquiv`, `principalFreeRow` and
`fullHighCoefficient`, not a diagnostic scalar model. Every high-Poisson
frequency in the principal row has the exact form `idealGenerator(a)^6`.
Any mask deleting every sixth-power frequency therefore makes every
actual high coefficient in that row, and its whole sixth-indexed slice,
exactly zero. The target reciprocal-L signal is supplied by that principal
row in the paper's Section 10.1. Deleting that row fails source preservation.

This preflight does **not** identify the low additive Gram frequency `k`
with the original high-Poisson frequency. The two have separate transforms
and indexing; the Gram exceptional set also depends on the common-prime
modulus. An actual coupled estimate could avoid this deletion and remain
viable. No signed estimate for that coupled object is proved here.

The existing exact upstream object to investigate is
`ProbePhysical.lowSeparatedIntegrand`, with `B` instantiated by
`lowSelectedInverseRow` as in `compensation_tuple_low_polynomial`.
Its signed row sum retains, in the same summand:

```text
outer annular mask * calibration character * radial height twist
    * lowRayAmplitude(same row, same height)
    * lowSelectedInverseRow(same row, actual selected prime slots).
```

`LowTupleGram.compensation_tuple_actual_gram` currently separates those
last two factors by their squared row norms. The prospective new estimate
must concern this actual instantiation, not the theorem's arbitrary `B`.
The row-independent slot coefficients, disjoint prime supports, common
nonunit masks and joint Gaussian profile must remain intact. First isolate
the exceptional contribution with both factors present and test its exact
principal Mellin multiplier. Only a source-preserving coupled cancellation
with a quantified gain is progress beyond the published proof. The power
benchmark above is a necessary strength test, not a proof that the actual
probe permits that saving; its other singularities must also be audited.

1. Preserve the completed pinned `7/8` native verification and its
   standard-axiom endpoints as the external checkpoint.
2. Use the completed main-project import and its unconditional transfer.
   Credit the literature theorem explicitly; the generic parameterized
   bridge remains available but is no longer the instantiated endpoint.
3. Study the coupled reflected/Poisson energy and marked/plain moment
   induction as the new arithmetic input. Preserve conductors, nonunit
   masks, shared phases and the exact joint comparisons.
4. Before new RH machinery, demand a quantified improvement to that
   exponent balance or an exact application to an existing Gaussian/Weil
   or Suzuki endpoint. A new transform or the common-probe contract alone
   does not count as an arithmetic saving.

This review does not close the overall arithmetic-operator goal or mark
any Tier-1 family exhausted. The 86-module operator audit remains a separate
validated checkpoint. No README, explorer or ordinary CI record is advanced
by this local review.

## Checked principal Euler extraction and analytic extension

[QuasiRHPrincipalEulerAudit](../scripts/QuasiRHPrincipalEulerAudit.lean)
is an explicit native-toolchain research leaf against the pinned upstream imports.
Its original isolated Lean 4.34.1 verification remains recorded; the main
project now uses that same toolchain and imports the upstream proof. This
research leaf is not registered in the ordinary root. It retains the
actual `principalLocal`, `principalCorrection`, prime ideals, angular
phases and target-character coefficients.

At the actual principal residue `w=1`, `z=1/6`, write

```text
q = Norm(P)^(-1),
D = eta(primaryGenerator P) Norm(P)^(-s),
R = actualAPhase eta (primaryGenerator P) Norm(P)^(3-6s).
```

The exact identity is

```text
principalLocal = G / (1-R),
G = (1-q^2) [1-q(R-D)/(1-D)].
```

It uses the exact relation `K=D(1-q)`; treating the local variables as
independent would miss that cancellation. The finite product identity is
checked without norms. The infinite identity is also checked where its
Euler products converge, `Re(s)>2/3`, outside a frozen set containing the
prime ideals of norm below four:

```text
residualCorrection = product_P(1-R_P) * principalCorrection.
```

The extracted coefficient is itself an actual multiplicative ideal map:

```text
chi_eta(I) = conjugate(angularFactor(primaryGenerator I))^6
            * eta(primaryGenerator I)^6,
R_P = chi_eta(P) Norm(P)^(-(6s-3)).
```

Here `angularFactor` is the normalized complex embedding of the actual
Eisenstein generator. It is not a freely chosen phase and not a claim
that a Gauss sum equals its own angular part. The leaf proves ideal
multiplicativity. It does not import an infinite-type Hecke continuation
or nonvanishing theorem for this new Euler channel.

For every fixed `sigma>1/2`, set

```text
e_G = min(2, 6sigma-2, sigma+1) > 1.
```

The checked uniform estimate is `|G_P(s)-1| <= 9 Norm(P)^(-e_G)` for
`Re(s)>sigma` and `Norm(P)>=4`. After a finite cutoff depending on
`sigma`, the residual product is holomorphic and within `1/2` of one
throughout that half-plane, uniformly in the finite-order target character.
All actual angular phases stay in the factors; the estimate does not
assume their statistical cancellation.

For the unmodified principal correction, every fixed `sigma>2/3` has

```text
e_H = min(e_G, 6sigma-3) > 1,
|principalLocal(s)-1| <= 20 Norm(P)^(-e_H).
```

The same finite-tail argument proves that the original
`principalCorrection` is holomorphic and within `1/2` of one on
`Re(s)>sigma`, after a cutoff depending on `sigma`. This improves the
published principal-correction domain. It is **not** a `2/3` zero-free
theorem: the low arithmetic bound, nonprincipal rows, compensated factors
and high contour comparison have not been extended by this leaf.

The finite cutoff depends on the distance to the boundary. Neither result
asserts one uniform cutoff and contraction on the entire open boundary
half-plane. The exact extraction identifies the remaining channel:
`Re(6s-3)>1` is equivalent to `Re(s)>2/3`. Below that point, normal
Euler convergence no longer pays the angular channel. This equivalence
is not a natural-boundary theorem or a proof that further continuation
is impossible.

This is useful analytic prerequisite work, not the new independent
arithmetic inequality required by the operator goal. The coupled low
estimate still remains open. At the fixed published geometry it must
improve by more than `3/8` to reach the critical line; simply extracting
this Euler factor provides no such saving.

The leaf passes the native 15-linter namespace audit and checks all
66 declarations, including 52 theorems and generated helpers, with only
`propext`, `Classical.choice` and `Quot.sound`. Run it from the isolated
verification project with:

```text
/home/dbsanfte/.elan/bin/lake env lean /home/dbsanfte/riemann/formal/scripts/QuasiRHPrincipalEulerAudit.lean
```

The log and all-declaration axiom report are `principal-euler-check.log`
and `principal-euler-axioms.json` in that project. No ordinary build,
public endpoint, README or explorer is changed.

## Coupled finite-period matching audit

[QuasiRHCoupledResidueAudit](../scripts/QuasiRHCoupledResidueAudit.lean)
is checked directly with the upgraded main project's pinned dependencies.
It tests the proposed complete-period orthogonality payment before any
large coupled-estimate development. It concerns an actual local row, not
the whole physical probe or a hypothetical zeta-zero response.

For a multiplicative character `chi` on a finite field of cardinality `q`
and a primitive additive character `psi`, keep the negative-frequency
convention of the actual low row:

```text
A_chi(m) = sum_x chi(x) psi(-m*x).
chi(m) A_chi(m) = chi(-1) gaussSum(chi,psi)   for m != 0,
chi(0) A_chi(0) = 0.
```

This pointwise identity remains exact inside any finite complex-weighted
mask. In particular, neither a mask nor a phase is completed or discarded:

```text
sum_m w(m) chi(m) A_chi(m)
    = chi(-1) gaussSum(chi,psi) sum_{m != 0} w(m).
```

The complete-period projection of a second residue character `phi` is
zero exactly for nonmatching characters. When `phi=chi`, its joined mean,
normalized by `q*sqrt(q)`, has norm `1-1/q >= 1/2`. Both separate rows have
mean zero when `chi` is nonprincipal. Thus separate nonprincipal means,
even for the actual arithmetic characters, do not imply a vanishing or
power-small joined mean. These are finite residue means, not assertions
about prime density or cancellation of the zeta pole.

The leaf proves the bridge to the actual `sexticGauss`, `quotientTrace`
and `idealRowHom` at a genuine good Eisenstein prime. For its order-six
character, the surviving completed-index valuation is exactly
`e = 1 mod 6`. A completed index `I*J^3` has valuation `i+3j`, where
squarefree `I` has `i=0` or `1`. The exact local matching condition is:

```text
(i+3j) mod 6 = 1  iff  i=1 and j is even.
```

Consequently the actual columns `I=P, J=P^(2t)` retain the same matching
character for every `t>=0`, including all their prime powers. The masked
identity retains the full complex weight and the nonunit deletion. This
is a clean no-go for blanket complete-period cancellation of the joined
row. It does not give an estimate for the complete Gaussian theta sum,
remove its annular masks, or establish that the full low probe has no
source-preserving cancellation across its columns or profiles. Those are
the remaining candidates; none of the eight Tier-1 families is declared
exhausted by this test.

The focused warning-as-error check passes all 15 namespace linters and
audits 44 declarations, including 39 theorems and generated helpers, with
only the three standard axioms. Its evidence is in
`.lake/quasi-rh-coupled-residue/{check.log,axioms.json}`. Run:

```text
/home/dbsanfte/.elan/bin/lake env lean -DwarningAsError=true scripts/QuasiRHCoupledResidueAudit.lean
python3 scripts/probe_quasi_rh_coupled_residue.py
```

The second command is a floating regression only. At eight prime-field
sizes it checks 96 valuation projections and eight complex-masked
identities. Separate normalized means are at floating zero, while the
matching joined norms range from `6/7` to `192/193`. The Lean proofs do not
use these samples. This is neither a new zero-free region nor the
independent signed estimate required to reach RH.

## Finite smooth-profile centering: exact source gate

[QuasiRHProfileCenteringAudit](../scripts/QuasiRHProfileCenteringAudit.lean)
closes a different, precisely limited comparison before attempting an
arithmetic bound. At fixed `X,Y,Z`, target character, correction and prime-slot
multiplier, the actual imported `sourceMultiplier` has the exact factorization

```text
sourceMultiplier(W0,W1; s,1,1/6) = mass(W0,W1) * G(s),
mass(W0,W1) = Mellin(W1,1) * Mellin(radialFourier(W0),1/6),
G(s) = X^(1/3) Z^(s-5/6) exp((s-5/6)^2)
       * H(1,1/6) * B(1,1/6) / L(eta,s).
```

Every Gaussian, complex scale, reciprocal-L factor, actual correction and
prime-slot multiplier is retained. The formula is exact for arbitrary
finite complex profile coefficients. Consequently

```text
sum_i c_i * mass(W0_i,W1_i) = 0
    implies sum_i c_i * sourceMultiplier(W0_i,W1_i; s,1,1/6) = 0
```

for **every** `s`. The leaf also proves this for the double residue, its
normalizer, the joined vertical source integral, and the literal detector's
finite prime-slot pools with their actual exclusions and global correction.
The integral result uses the already-zero joined integrand; it does not
assume an unproved contour shift or interchange nonintegrable terms.

This is a failed source-response gate for scalar profile centering: if a
comparison cancels this common Mellin scalar, it cancels all reciprocal-L
detector channels. It cannot remove only an unwanted contribution while
retaining the selected zero. This statement is **not** an identification of
the low Gram exceptional row with the high principal residue. It does not
prove that this centering cancels the low exception, nor estimate the full
physical probe or the remaining contours.

The boundary of the no-go is also explicit. If two profiles use different
arithmetic multipliers `B0,B1`, their scalar-centered source is

```text
mass(W) * sourceMultiplier(V; H,B0)
  - mass(V) * sourceMultiplier(W; H,B1)
    = mass(V) * mass(W) * G_{B0-B1}(s).
```

The actual signed arithmetic difference survives. No bound on that
difference is assumed or proved. Profile-dependent prime-column weights,
noncommon arithmetic factors and different normalized spectral shapes
remain separate candidates. Any next comparison must first prove a
nonzero source for its actual slot/correction difference, then preserve the
literal row correlations in an independent estimate. Merely introducing
this difference does not count as an arithmetic saving.

The focused native check passes warning-as-error and all 15 namespace
linters. All 18 declarations, including 16 theorems and generated helpers,
use only the three standard axioms. Evidence is in
`.lake/quasi-rh-profile-centering/{check.log,axioms.json}`. Run:

```text
/home/dbsanfte/.elan/bin/lake env lean -DwarningAsError=true scripts/QuasiRHProfileCenteringAudit.lean
```

No new zero-free claim, RH endpoint discharge, full-family exhaustion,
ordinary CI run or public proof-tree change follows from this audit.
