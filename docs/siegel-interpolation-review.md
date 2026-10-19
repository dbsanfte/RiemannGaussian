# Siegel interpolation: what transfers to this project

Research review, 2026-10-18. Primary source: William D. Banks,
[On the OpenAI proof that Landau–Siegel zeros do not exist, v1](https://arxiv.org/html/2610.15483v1).
Three user-authorized Sol 6.1 agents reviewed the argument, its transfer
conditions, and possible extensions independently. The original local
review and every previous determinant audit remain in force.

## The useful arithmetic mechanism

The paper links a near-one real-character zero to a strong bias toward
one Frobenius class. Weighted interpolation then constructs **one nonzero
algebraic-integer determinant**. At each favorable prime, lower-weight
row substitutions preserve that determinant while extracting prime
powers. Their combined divisibility exceeds its Archimedean size bound.
See Lemma 2.1, Proposition 3.4, and Lemmas 4.1, 5.1, 6.1–6.2.

This is a collective restriction on actual integers. An arbitrary list of
prime weights cannot simply be substituted into it. The key transferable
requirement is common columns, exact integral congruences, and an earlier-row
span closed under the substitutions. Separate prime-dependent determinants
cannot supply the same conclusion. The whole paper and its cited finite
computation have **not** been verified in Lean here.

## New audit: extract all visible coordinates together

Our extension uses the same determinant and its three coordinates
`1, sigma, sigma*tau`. For each unramified prime, apply the Frobenius
difference to every coordinate whose image remains visible. Each
nonleading term still has lower weight when `p>H`. Thus, at the level of
the finite algebraic argument, the simultaneous extraction is

\[
E_p=\sum_{\alpha}\sum_{i:\,g_p i\text{ visible}}
       \left\lfloor\frac{\alpha_i}{p}\right\rfloor.
\]

Writing `S_i` for the retained degree sums and `S=S_1+S_2+S_3`, its main
coefficient is:

| Frobenius class | Visible coordinates extracted | Main coefficient |
|---|---|---|
| `1` | 1, 2, 3 | `S` |
| `sigma` | 1, 2 | `S_1+S_2` |
| `sigma*tau` | 1, 3 | `S_1+S_3` |
| `tau` | 2, 3 | `S_2+S_3` |

The finite Fraction-arithmetic regression checks the **same** determinant
before and after substitution. In `Q(sqrt(5),sqrt(2))`, a 16-column example
at `p=3` extracts exponent 2 where the first-coordinate calculation gives
0; its norm has 3-adic valuation 8. A second field, `Q(sqrt(13),sqrt(2))`,
gives exponent 2 from the previously omitted `tau` class. All 36
prime/determinant/norm checks passed, including 3 positive exponents and
33 zero exponents. This is exact finite evidence, not a Lean proof of the
general determinant extraction or an asymptotic estimate.

There is also a precise limitation. The uniform class average is `3S/4`,
exactly the leading geometric cost at this interpolation scale. More
generally, for a finite group `G`, visible coordinates `V`, and arbitrary
complex degree weights,

\[
\frac1{|G|}\sum_{g\in G}\sum_{h\in V}
  \mathbf1_{gh\in V}S_h
 =\frac{|V|}{|G|}\sum_{h\in V}S_h.
\]

This identity and the exact four-character expansion are now checked in
[ArithmeticOperatorFrobeniusBalanceAudit.lean](../scripts/ArithmeticOperatorFrobeniusBalanceAudit.lean).
If an independently proved interpolation theorem has slope `|V|/|G|`,
the uniform leading terms cancel. The finite-group identity does not
prove that interpolation theorem or supply a rational-prime Frobenius
rewrite in a nonabelian extension.

## Density removal does not provide a free zeta source

The four-class coefficient decomposes as

\[
\frac{3S}{4}
 +\frac{-S_1+S_2+S_3}{4}\chi
 +\frac{S_1+S_2-S_3}{4}\eta
 +\frac{S_1-S_2+S_3}{4}\chi\eta.
\]

The checked finite ledger retains arbitrary complex prime weights and
distinguishes two operations:

- Subtracting the **actual uncoloured prime row** removes its entire
  trivial-character component. The analytic interpretation therefore
  removes the guaranteed zeta-zero residue. Quadratic L-functions could
  have coincident zeros; their absence is not assumed.
- Subtracting only **smooth density** leaves the uncoloured arithmetic
  error. It retains the zeta source, but conductor/coordinate height,
  the actual nonnegative floor loss, the small-prime head, and ramification
  remain in the inequality.

Even granting a perfectly matched height phase, one fixed diagnostic zero
`rho=beta+iy` contributes to this harmonic channel only

\[
-m\int_H^M x^{\beta-2}\,dx
=-m\frac{H^{\beta-1}-M^{\beta-1}}{1-\beta}.
\]

For `beta<=7/8` and `H>=1`, its magnitude is at most `8m H^(-1/8)`.
This is bounded, rather than a positive multiple of `log M`. The actual
determinant comparison does not itself permit an external complex phase
as a prime valuation. The analytic source discussion is a transfer audit;
the new Lean leaf proves the finite centering identities, not a new
logarithmic-derivative continuation.

## Other extensions tested

**A larger common algebraic grid.** Five conjugate coordinates in
`Q(sqrt(5),sqrt(2),sqrt(3))` span all 256 Boolean-grid columns at total
degree 8. Exact reduction modulo the split prime 1009 proves the selected
minor is nonzero in characteristic zero. The degree-8 lower bound follows
from the Boolean top-parity functional. This does not establish uniform
anisotropic interpolation as the grid grows. Its optimistic `5/8` slope
also does not repair the missing actual zeta-to-Frobenius source bridge.

**A direct cubic-Gauss algebraization.** The imported cube relation gives
a monic degree-three relation. In the natural weighting that makes its
right side strictly smaller, every Gauss-coordinate exponent at least
three is already dependent on earlier rows. Hence that coordinate has
no remaining prime-floor extraction at `p>=3`. This rejects that particular
strict monic lift, not every use of native Gauss sums.

**Automatic improvement of the imported quasi-RH estimate.** A real-zero
gap of the form `c/log D`, at a growing conductor `D=X^kappa`, alone permits
`X^beta=X exp(-c/kappa)`. It is not a fixed power saving in `X`. The native
joint Gauss/Mobius estimate still needs its own theorem.

## Decision

Keep the common-integral-object strategy. The new simultaneous extraction
is a real finite strengthening, and the balance theorem specifies what
it does and does not buy. Do not launch a broader determinant library or
claim a new zero exclusion from it.

A useful next candidate must retain the actual zeta source in the same
common integral object and prove a surplus **after** height, floor,
conductor, and literal-mask costs. An additional conjugate, a larger norm
degree, or a subtraction of the actual prime row alone does not meet that
condition. The strict imported `Re(s)>7/8` endpoint is unchanged.

Evidence and hashes are recorded in
[arithmetic-operator-siegel-all-class-gates.json](arithmetic-operator-siegel-all-class-gates.json).
The local Lean leaf passed warnings-as-errors, all 15 namespace linters,
and an audit of every local declaration using only standard axioms.

## Follow-up: retain the actual Gauss/sign relation

The native Gauss factors and the prescribed Möbius sign are not independent
coordinates. The new strict
[QuasiRHRawSignRelationAudit.lean](../scripts/QuasiRHRawSignRelationAudit.lean)
uses the imported, actual squarefree Eisenstein-ideal Gauss sums. Writing
`q = Norm(I)`, `pi` for the primary generator, `T_j` for the unnormalized
Gauss factors and `D` for their native mixed denominator, it proves

\[
T_1T_2=\mu(I)D,\qquad |D|=q,\qquad
T_2^3=\mu(I)\pi q,\qquad T_2^6=(\pi q)^2.
\]

Thus the sign can be encoded faithfully. Eliminating it requires degree
six; an unsigned cubic replacement would lose information. But clearing
`D` from the **whole** determinant column multiplies its absolute value by
exactly `q`. At auxiliary primes away from the conductor, the denominator
is a local unit (the local-integral assertion is paper-level here). For an
odd exponent and any common ring map fixing integers, the checked identity

\[
(T_1T_2)^\ell-\sigma(T_1T_2)
=\mu(I)\bigl(D^\ell-\sigma(D)\bigr)
\]

shows that recovering the sign this way supplies no additional prime
valuation. This is a limitation of this particular substitution, not of
every possible mixed-row determinant. A new relation between rows could
still matter; merely clearing the sign denominator does not produce it.

There is a further common-field obligation. For distinct split rational
prime columns, the raw cubic Gauss radicals generate extensions of growing
degree: their radicands have independent valuations modulo three.
Kummer theory gives degree `3^c` for `c` such columns over the Eisenstein
field. This deduction is paper-level and pinned to Milne's Kummer theorem;
it is not a formal impossibility result, since normalized degree factors
can cancel. It does mean the paper's fixed biquadratic interpolation
theorem cannot be imported with those hypotheses silently unchanged.

The precise remaining opportunity is a common integral construction whose
**whole source-bearing matrix** has a new divisibility surplus after its
coordinate heights, conductors and field growth are accounted for. Neither
the paper nor these audits supplies that surplus for our joined statistic.
The full paper has not been Lean-verified here. Follow-up validation is in
[arithmetic-operator-comparable-pair-raw-gates.json](arithmetic-operator-comparable-pair-raw-gates.json).

## Follow-up: the whole matrix and its physical profile

The next audit tests a collective operation, rather than independent choices
of column signs. At a finite pool of actual good Eisenstein prime ideals,
choose actual residue units with canonical sextic value `-1`. Their common
CRT multiplication realizes `mu(I)` on **every** squarefree subset column,
including overlapping columns. The conditional finite statement, with the
actual units and characters as hypotheses, is checked in
[QuasiRHCommonUnitGaugeAudit.lean](../scripts/QuasiRHCommonUnitGaugeAudit.lean).
The general existence/CRT bridge remains paper-level.

The complete-period Gram is invariant under this common permutation. For a
nonconstant physical weight `w`, however, the exact statement transports
`w` to `w(a·)`. The full native Gauss join also acquires the physical Liouville
factor `(-1)^Omega(A)` and a cube-order factor; these cannot be dropped.
In particular the native `alpha` Gauss factor is invariant under the relevant
change of its defining additive character. It is incorrect to infer a free
Möbius flip of `alpha` from the numerator-column permutation.

Thus complete orthogonality or a phase-invariant PSD bound is not the missing
arithmetic input. The original signed source stays in the **transformed
physical profile and its correlation with the columns**. Keeping the old
profile after the permutation changes the statistic; its paper-level Euler
audit removes the old reciprocal-L source instead of estimating it. This
does not rule out a constraint involving the actual, fixed source vector.

A second strict audit addresses whether untwisted factorial total positivity
can be retained after attaching the height phase. The exact adjacent-minor
criterion reduces to monotonicity of `sum_(d|n) Lambda(d) cos(y log d)`.
At every nonzero height there are negative adjacent minors arbitrarily far
out, even for the matrix of entry moduli. The proof keeps every prime power
and uses an existing unconditional prime-window theorem; it is not inferred
from floating samples. See
[ArithmeticOperatorFactorialTN2Audit.lean](../scripts/ArithmeticOperatorFactorialTN2Audit.lean).
Untwisted factorial positivity remains valid and available.

These checks sharpen the transferable idea from the paper. A useful new
constraint must act on the same integral, source-bearing object **with its
physical profile retained**, and extract a surplus after all height and
conductor costs. Complete-period symmetry and a twisted extension of Pascal
positivity do not supply that constraint. No new zero exclusion follows.
The strict checks and their limits are pinned in
[the new checkpoint](arithmetic-operator-native-gauge-digital-tn2-gates.json).

## Follow-up: conservation checks and a narrower analytic opportunity

The native averaging test is now explicit in
[QuasiRHGaugeAverageAudit.lean](../scripts/QuasiRHGaugeAverageAudit.lean).
Averaging actual calibrated minus-one residue-unit families has modulus-one
action on the physical Gauss row. Correct compensation restores it
pointwise and preserves every fixed original Fourier coefficient. The
common permutation exists at the finite level, but it does not provide
an estimate for the incomplete physical profile that still carries the
source. No global sixth-power-frequency invariance is assumed.

The [cyclotomic factorial test](arithmetic-operator-cyclotomic-source.md)
provides another useful source check. Actual integer cyclotomic norms
give a residual with Dirichlet series `C_b/ζ`, where the entire numerator
is nonzero in the relevant half-plane. However, its exact invertible
Mobius convolution shows that the small factorial aggregate cancels
the same source. An independent bound for the unaveraged residual is
still needed. The finite identities are checked in Lean; the analytic
source and inverse-convolution argument are paper-level.

A related literature search identified a more specific analytic
opportunity, recorded in
[the sextic continuous-remainder audit](arithmetic-operator-sextic-continuous-frontier.md).
A recent AI-authored preprint supplies a candidate full-Kubota mean
whose continuous part could save a factor `Z^(-1/96)` under the native
normalization. Its theta residue remains at the original critical cost.
Our literal coefficient is a character sum, while the available residue
Type-I estimate treats a divisibility sum; those cannot be interchanged.
Calibration, imprimitive moduli, marks and source transfer remain explicit
obligations. Neither preprint is imported as a Lean axiom.

These results preserve the useful lesson of the Siegel argument: a new
arithmetic restriction must constrain the **whole source-bearing
correlation**. The next precise candidate is the theta-residue pairing
with the same-weight spectral residual. Its signed estimate remains
open; there is no new zero-free region from this review.
## Follow-up: a stronger common determinant still pays its own source

The paper's common-integer-object principle was tested with a genuine
two-row q-binomial determinant, before taking any norm. The equal-area
rows cancel the second-order cyclotomic defect and give `Phi_n(q)^3`
divisibility. The derived third-order coefficient has one strict imaginary
sign at the principal primitive root for every `n>2`, so this exponent is
exactly three; `n=2` has order four. This is a paper-level derivation from
[Zudilin's q-binomial congruences](https://arxiv.org/abs/1901.07843),
supported by 509 exact finite checks, not a new Lean theorem.

The decisive source audit is also explicit. At every integer base `b>=2`,
the centered full logarithmic norm has error at most `1280*b^(-n)`.
Extracting `Phi_n(b)^3` leaves an actual integer quotient whose tracked
residual is `-3*R_b(n)` plus that exponentially small error. The full
determinant therefore provides no estimate for the surviving source.
All indices and extra quotient valuations are retained. The result is
specific to ordinary logarithmic norms; nonzero prime-power phases cannot
be split additively across the factorization without their exact order
transport. See the [full derivation](arithmetic-operator-higher-q-determinant.md).

In parallel, the native Gauss audit now formalizes the actual canonical
calibration power and fixed-numerator transfer, and the principal character
weight created by the native theta twist. The same-weight Patterson
subtraction leaves a Mobius pole coefficient. A second Type-I application
reaches a legitimate longer divisor dual, but its available estimate is
too large. See the [theta-twist audit](arithmetic-operator-theta-twist-frontier.md).
This does not rule out a stronger signed covariance estimate; it rules out
calling the existing componentwise bound such an estimate.

The transferable lesson from the interpolation paper remains concrete:
divisibility must exceed the height of the **same source-bearing integer
object**, after its quotient, phases and all masks have been included.
Neither extra divisibility alone nor cancelling a pole in an auxiliary
transform establishes that surplus. The strict imported endpoint remains
unchanged, and no complete operator family has been exhausted.

## Follow-up: retain valuation depth and the moving cutoff

The [next audit](arithmetic-operator-joined-dual-valuation.md) tests the
two remaining shortcuts directly. Lean now proves the literal native
Möbius–Ramanujan join; a prime numerator beyond the ideal cutoff makes
its complete finite coefficient one. The cheap fixed-numerator density
therefore leaves an unestimated moving-cutoff correlation. It cannot
be used uniformly as a replacement for the source-bearing statistic.

For the same higher-q determinant, a second checked audit retains the
phase at every prime-power depth. An actual seven-adic example kills
the full fiber while leaving its extracted cyclotomic fiber nonzero.
Thus ordinary divisibility cannot be transferred through a reset of
the depth phase. A root-of-unity evaluation lowers the available height,
but its extracted, degree-normalized norm has only logarithmic mass and
loses the power-size source. The complete row product also vanishes at
those roots; restrictions or regularization would need a new audit.

These results narrow the transferable requirement further: common
integrality must constrain the **joined physical phase and cutoff**.
The paper's determinant idea remains valuable, but these tested versions
do not produce the necessary source-sensitive surplus. Both native
finite leaves are checked; the analytic rate and resultant calculations
are explicitly paper-level. No new zero exclusion is claimed.

## Follow-up: the small-window source survives, but the coding disappears

The [small-window audit](arithmetic-operator-theta-support-small-window.md)
now proves in Lean that the once-counted cyclotomic product through N
contains every prime power through N, except those over primes dividing
the base. The original full determinant product restores those base
primes on paper. Its packet is therefore exactly twisted Chebyshev on
that window. The growing family retains the genuine zero source, but
this observation supplies no independent constraint on it. This closes
the small-window shortcut left open by the earlier full-envelope bound;
unsaturated windows and other row correlations remain separate questions.

The parallel literature check also distinguishes the explicit imported
cubic theta coefficients from the physical sextic residue needed for the
candidate coupled estimate. Known sextic local relations leave the prime
coefficients unresolved. Aligning prime/cube incidences preserves the
transformed kernel, but leaves `W(t)-v*(q-1)q^-2*W(qt)`, not zero. Its
application still requires the exact cusp/ray bridge and model weights.
The next credible gain must therefore come from the whole signed
correlation or another common arithmetic constraint, rather than a
support substitution or a factorization already equal to Chebyshev.

## Follow-up: identify the exact source before enlarging the determinant

The [next audit](arithmetic-operator-native-ray-fixed-q-source.md) gives a
stronger stopping rule for ordinary logarithmic norms. For fixed-size
Gaussian-binomial constructions with fixed affine data and integer base,
the complete determinant is either eventually zero or a quadratic-height
term times a nonzero finite-order analytic germ. Its fully centered
ordinary logarithm has an exponentially small residual and an entire
row-index Dirichlet series. That general statement is paper-level; its
analytic-germ step is Lean checked and the scope independently reviewed.
Further fixed-order divisibility alone cannot restore the missing source
in this particular observable. Physical prime-power phases remain distinct.

The unsaturated product trace is now exact in Lean and does retain actual
prime structure: it is a truncated divisor sum on p−1. All higher depths
are affordable below any N^beta,beta>1/2, by a paper-level lift calculation.
But its nonprincipal-character aggregate can compensate the principal
reference. A zero source for that reference is therefore not a source
theorem for the full average. The required correlation and common-base
averaging costs are explicit, rather than replaced by a prime model.

In parallel, the actual native sixth-power calibration symmetry is now
checked with all masks intact. This closes one finite transfer requirement
for the sextic route; its global cusp/model and signed covariance estimates
remain open. None of these tests changes the proved zero-free endpoint.


## Follow-up: the whole source must survive (2026-10-19)

The [new total-source and section audit](arithmetic-operator-total-source-section.md)
tests extensions of the paper's collective-integer principle. A natural
rank-N boxed determinant has an exact Lambert expansion; after all height
and constant terms its ordinary logarithm decays geometrically. That
particular growing-rank extension therefore loses the zeta source too.
The finite-product result is Lean-checked; its classical Jacobi--Trudi
identification is independently reviewed at paper level.

For the cyclotomic complete-base trace, summing ALL divisors retains a
max-cutoff weighted shifted-prime series. A selected source in its principal
reference is insufficient: the growing-divisor covariance must be determined.
The new finite arbitrary-weight reindexing exposes this exact requirement.
It neither proves cancellation nor noncancellation. A no-Siegel theorem
for fixed characters cannot supply that missing uniform source conclusion.

On the separate native sextic branch, fixed calibration and the required
rescaled Fourier extraction are now explicit. Principal and sextic
profiles are formally unequal; automatic residual projection would remove
the full unpaid covariance, so source retention must be checked before
using it. These are scoped applicability/source gates, not a new RH bound.
See [the checkpoint](arithmetic-operator-total-source-section-gates.json)
for strict checks, exact probes, primary sources and formal/paper boundaries.

## Follow-up: retain a common object without averaging away its information

The [common-base audit](arithmetic-operator-common-base-section.md) tests
another direct lesson of the interpolation argument. A single base is
essential, but averaging it over a complete CRT period makes the
distinct-prime incidences independent. Lean now proves that cancellation
for the actual cyclotomic product. It does not apply to an incomplete
base interval without its explicit discrepancy and height costs.

A moving algebraic base was also tested with every conjugate retained.
Its complete norm carries nontrivial divisor arithmetic, but the reviewed
row transform has no nontrivial-zero pole. The exact finite profile and
its primitive tail are now formalized; the general norm and continuation
remain paper-level. This narrows the useful observation rather than
disproving all interpolation-based approaches.

Separately, the native sextic route now has a direct construction using
the literal arithmetic coefficient. Finite row/support identities are
Lean checked, and the exact paper-level sextic and Fourier calculations
have an independent review. The complete transformed-cusp source pairing
and its signed estimate remain open. These checks reinforce the paper's
useful requirement: constrain the same source-bearing arithmetic object
through every averaging, norm and spectral operation. No new zero
exclusion follows from this checkpoint.

## Follow-up: preserve integrality, prime depth, and the whole source

The [source/cusp checkpoint](arithmetic-operator-cusp-source-frontier.md)
tests two further transfer conditions. Signed row inversion preserves
an exact rational cyclotomic product, but need not preserve integrality:
the checked sixth-row quotient at base3 is4235/2. Even when the quotient
is an integer, the linear combination of phased prime-power rows need
not equal its own phased divisor sum. These are literal arithmetic
obstructions to carrying the paper's common-integer comparison through
an inversion, not counterexamples to the paper.

On the imported sextic branch, a new strict theorem extends the actual
source correction to each fixed half-plane right of2/3 after fixed
enlarged exclusions. Its exact factorization exposes an angular Hecke
factor at6s-3 beyond that boundary. Native finite-character nonvanishing
cannot silently be applied to this nonzero infinity type.

The whole cusp audit retains the original marked/cube coefficients;
their energy is already bounded in the imported proof. What remains
is the physical full-D transfer and complete source/exterior accounting,
followed by the independent signed covariance estimate. A finite cusp
identity or a nonzero residue coordinate supplies neither automatically.
The source-correction result is analytic progress, but the existing
strict Re(s)>7/8 zero-free endpoint is unchanged.


## Follow-up: preserve the native object through the analytic application

The [exterior/physical checkpoint](arithmetic-operator-exterior-physical-transfer.md)
provides concrete analytic progress on the separate sextic route. Lean
now controls the unchanged correction on the actual two exterior contours
below its inherited7/8 restriction, and proves the required amended
marked-factor decay. This does not yet extend the full detector theorem.

The physical application is also more precise: actual calibration, fixed
prime exclusions and residue classes reduce to a specified finite family
in a quantitative full Gauss-series preprint. The conditional application
retains imprimitive terms and the native Fourier normalization; an
independent review verifies its arithmetic hypotheses. The analytic
preprint itself has not been imported into Lean.

This follows the interpolation paper's useful discipline of keeping the
same arithmetic object through every comparison. It does not transport
its real-character prime bias to the complex theta correlation for free.
The conditional continuous saving leaves that signed correlation and
whole source accounting open. The proved zero-free endpoint is unchanged.

## Follow-up: common-integer restriction and source accounting

The [native source/coupling checkpoint](arithmetic-operator-native-source-coupling.md)
proves a further literal integrality restriction suggested by the paper's
common-integer discipline. A primitive prime isolates a cyclotomic order
below its next collision, so an integral signed product cannot assign
that order a negative exponent. The supplied-witness theorem is checked
in Lean at a fixed integer base, even for growing signed row families.
Global primitive-divisor existence and Mellin consequences remain
paper-level; the total growing-cutoff zero response is still open.

The separate sextic work also identifies two precise non-solutions:
normalized calibration-character averaging preserves the common Fourier
coefficient, and the native cubic/sextic residue exchange is unitary after
its changed index is included. Neither provides a free signed saving.
Independent review of the broader source transport further clarifies
that the source is in the difference between the probe and the complete
central sum, not automatically in one theta term. These restrictions
keep the arithmetic object and its source linked through the analysis;
no new zero-free region is claimed.


## Follow-up: quantitative transport without resetting prime depths

The [primitive-depth checkpoint](arithmetic-operator-primitive-depth-frontier.md)
extracts another useful common-integer constraint. Actual integrality makes
the negative primitive factor divide the positive nonprimitive factor. A
child can pay only one nonprimitive prime. The exact incidence/valuation
ledger is now compiled; the collective height and packet consequences are
separately documented paper proofs.

A second new Lean inequality handles integral signed products whose factor
exponents lie in{-1,0,1}: the full phase differs from the cumulative-row
ledger only at repeated prime-power depths, with an explicit summed bound.
This preserves the literal physical cutoff. It does not justify averaging
over integral bases forfree; a concrete cyclotomic quotient is integral at
only one base. The remaining common-base/source estimate is therefore
visible rather than hidden in an exact-but-false phase linearization.

The parallel imported-proof audit pays central errors on PAPER in a small
range below7/8 using the actual native moment producer and a newly checked
1/5000exponentmargin. It leaves the physical theta term unbounded. Exact
theta/central joining retains the reciprocal-L source, and the corrected
physicaltheta locus isw+z=7/6. No new zero-freeregion or independent RH
endpoint bound is claimed.

## Follow-up: integral bases and a genuinely bounded subset

The [next checkpoint](arithmetic-operator-integral-primitive-moment.md)
formalizes a limitation of the common-integer strategy: any fixed signed
cyclotomic product containing a negative exponent can be integral at only
finitely many bases. Each base is bounded by the absolute value of the
actual numerator/denominator resultant. Moving exponents remain possible,
but their arithmetic and height costs cannot be averaged away.

The saturated positive primitive packet has a genuine source, yet its
prime layer is exactly ordinary Chebyshev outside a finite head. That
prototype therefore supplies no new cancellation. Its unsaturated total
multiplicative-order source remains a separate open theorem.

The parallel native investigation does give a bounded piece: an actual
Lean tuple estimate with weight L^(1/6), combined with known sextic
fourth/sixth-power relations on paper, pays that original numerator sector
at Z^(-13/144+small positive costs). All cube overlaps, marks, calibration
and the original source-normalizer loss remain. The full residue/section
identification is still a paper input. The general signed prime/square-core
theta correlation remains unpaid; no new zero exclusion is claimed.


## Next applicability gates and a full central payment — 2026-10-19

The [new checkpoint](arithmetic-operator-auxiliary-order-central.md) sharpens
the distinction between a useful collective integer restriction and a
formal rewrite. Positive same-base product/GCD/LCM cutoff words are now
proved to have exactly one original row's prime support. They therefore
cannot introduce a new prime-layer cancellation by composition alone.
Signed integral division and genuinely different bases remain outside
that result; the common-integer/source obligations from this paper still
apply to any such proposal.

The actual unsaturated primitive order packet also has a positive linear
absolute extra mass, by a checked square-base inclusion and a paper-level
fixed-progression prime estimate. This blocks absolute payment, not signed
order cancellation or the unknown total zero residue. In the sextic branch,
the direct auxiliary Hecke pair has disjoint original physical windows;
a cross-tuple rescue must prove its changed marked weights, not just the
coefficient recurrence.

There is one positive compiled estimate in this pass: the entire native
central row contribution, with all floor bins and original normalization,
is source-small by a power1/250000 for actual betaSup in[8749/10000,7/8].
The theorem permits every compatible fixed source datum after preparing
the fine slots. The physical probe/theta correlation remains unpaid, and
strictRe(s)>7/8 remains the imported endpoint. This is not a formalization
of the whole Siegel paper or a new zero-free claim.


## Cross-tuple and moving-tail follow-up — 2026-10-19

The [latest checkpoint](arithmetic-operator-cross-tuple-tail-window.md)
tests three further ways to preserve arithmetic and the source together.
The original-window Hecke transfer has a real conjugate-prime exception,
but its full weight is a partial q^(-1/2) comparison with an expensive
inverse and unpaired large prime numerators. It is not cancellation of
the original leading contribution.

A new Lean theorem shows that exact physical-window annihilation of the
theta hyperplane also deletes the existing principal double-residue
normalizer. A second proves that the first surviving cyclotomic tail
annulus is exactly primitive-root prime selection. These are useful source
and applicability gates, not new signed RH estimates. The total unsaturated
order-tail source remains unproved.

The global sextic literature supplies a precise conditional square-sector
target, but the needed actual finite-section identity remains conjectural.
Prime and odd-core correlations remain unpaid. The lesson from Banks's
common-integer determinant still applies: exact identities must control
the same arithmetic object carrying the source; changing that object or
only its normalization does not provide an independent contradiction.
