# Integral-base obstruction, native moments and a paid theta power sector

Local checkpoint, 2026-10-19. This continues the
[common-integer depth frontier](arithmetic-operator-primitive-depth-frontier.md)
and [Siegel interpolation review](siegel-interpolation-review.md).
It separates checked integer restrictions, checked native moment inputs and
a conditional paper estimate for an actual subset of the theta term.
The imported strict `Re(s)>7/8` endpoint is unchanged.

## Fixed signed products cannot be averaged over unbounded integral bases

For fixed `M` and a fixed integer exponent array, write the actual product as

\[
\prod_{2\le e\le M}\Phi_e(b)^{\beta_e}=A(b)/B(b),
\quad
A=\prod_e\Phi_e^{\max(\beta_e,0)},
\quad B=\prod_e\Phi_e^{\max(-\beta_e,0)}.
\]

[IntegralBasePopulation](../scripts/ArithmeticOperatorIntegralBasePopulationAudit.lean)
proves that the actual integer resultant `R=Res(A,B)` is nonzero. If some
supported exponent is negative and the product is integral at `b>=2`, then

\[
B(b)\mid R,\qquad b\le B(b)\le |R|.
\]

This is an explicit finite bound, with no supplied coprimality or Bezout
hypothesis. Unboundedly many integral bases exist **if and only if** all
supported exponents are nonnegative. Thus the earlier complete-base mean
cannot be conditioned for free on a fixed signed product being integral.

The quantifier order matters. With `M=4`, `b=2^k-1`, `beta_2=-1` and
`beta_4=k`, the product is integral and its resultant is `2^k=b+1`.
Moving coefficients can therefore escape the fixed-array obstruction.
They still have to pay their own growing resultant, height and source costs.
The theorem supplies no estimate at the finitely many permitted fixed bases.

## The saturated primitive packet has a source but no extra cancellation

[PrimitivePacketSource](../scripts/ArithmeticOperatorPrimitivePacketSourceAudit.lean)
constructs the actual primitive integer part of every `Phi_e(b)`, retaining
all prime multiplicities except primes dividing the index `e`. Let `R_M`
be their product over `2<=e<=M`. It proves for every literal prime `p<=M`

\[
p\mid R_M\quad\Longleftrightarrow\quad p\nmid b(b-1),
\]

and the corresponding identity for **arbitrary complex weights on those
same primes**. The two-adic and order-one heads remain explicit.

At physical cutoff `X<=M`, the higher-depth difference from ordinary twisted
Chebyshev is at most `sqrt(X) log(X)+O_b(1)` on paper. Hence at `X=M` the
packet retains every hypothetical zero source above `1/2`, but has reduced
to ordinary Chebyshev up to a smaller error. That closes this saturated
prototype as a new independent arithmetic mechanism.

For `X=M^kappa`, `kappa>1`, the exact paper-level total row Mellin is

\[
\frac1s\sum_{p\nmid b(b-1)}\log p
  \sum_{1\le r\le v_p(b^{\operatorname{ord}_p(b)}-1)}
  p^{-iry}
  \max\{\operatorname{ord}_p(b),p^{r/\kappa}\}^{-s}.
\]

Its initially convergent half-plane is `Re(s)>min(kappa,2)`.
The total continuation and zero residue remain unproved. Each fixed-order
prime set is finite; that does not justify an infinite-order residue
interchange. For `1<kappa<2 beta`, the precise missing input is that the
extra moving-order correction does not cancel the ordinary source residue
`-m/beta`. Beyond that range the higher-depth channel must also remain joined.
The audited multiplicative-order literature does not supply this theorem
unconditionally. No source from a separate reference term is credited to
the total packet.

## The actual four-field moment producer works below its final wrapper

[MomentBelowBoundary](../scripts/QuasiRHMomentBelowBoundaryAudit.lean)
now compiles the producer bridge that was paper-only last checkpoint.
For the actual Hecke-zero supremum in `[51/100,7/8]`, use an independent
`Delta>0`. The literal terminal certificate only needs

\[
\kappa_{\rm plain}\ge3/4,\qquad
2\beta_\star-1\le\kappa_{\rm plain},
\]

which hold for the native `kappaPlain=3/4+2 Delta`.
The resulting theorem retains all four actual moment fields, fine slots,
fixed source data and exclusions, calibration, selected marks, cubes and
moving height. A second theorem chooses the native positive height exponent
and absorbs its polynomial cost. No above-`7/8` wrapper is invoked outside
its domain, and no vendor source changed.

The full application to all normalized central rows remains the previous
paper composition for `betaStar>2187/2500`. The new compiled result supplies
its moment input, not that whole bound. In either case the source belongs
to `normalizedProbe-F_all`; paying `F_all` does not pay the physical probe.

## A genuine subset saving from the known sextic relations

The paper arithmetic audit isolates the original numerator sector with
every good prime valuation congruent to `0` or `4` modulo `6`:

\[
m=\epsilon a^4b^6,\qquad a\text{ squarefree},
\]

with overlap between `a,b` allowed. The known raw sextic coefficient
relations, retained as a finite section vector with its phases, give

\[
|\rho_h(-a^4b^6)|\ll (Na)^{-1/3},
\qquad
\sum_{Nm\le Q,\ m\text{ in this sector}}|\rho_h(-m)|^2\ll Q^{1/6}.
\]

Pairing only this original subset with the existing full marked/cube energy
costs `Q^(1/12) Y^(-1/3)`. At the native physical lengths this is
`Z^(-13/144) L^(1/6)`.
The literal unselected weight has norm `L^(-3/2)` times the bounded slot
profiles. Thus its remaining tuple sum has prime-ideal exponent `-4/3`,
strictly in the absolute convergence range.

This tuple payment is now independently checked in
[UnselectedWeightedMass](../scripts/QuasiRHUnselectedWeightedMassAudit.lean):

\[
\sum_{\text{actual tuples }a}|w_a|L_a^{\theta}\le C_{K,M,\theta},
\qquad \theta<1/2.
\]

The constant is uniform over the actual finite prime-slot supports, retained
tuple masks, selected-index set and scale-dependent profiles bounded by `M`.
The named `theta=1/6` corollary pays precisely the factor above. It assumes
no theta-residue recurrence or zero hypothesis; the number of slots `K`
and profile bound stay fixed before the scale grows.

Including the existing inverse source-normalizer cost, the conditional
paper bound for this whole sector is

\[
|\Theta_{04}|\ll Z^{-13/144+C_B\varepsilon+\nu_N},
\qquad 0<\nu_N\le\varepsilon.
\]

The actual raw residue/finite-section identification and global Hecke
transfer are still **paper inputs**, not imported Lean theorems. Every
original selected mark, cube overlap and fixed calibration remains in the
native energy; the sector is not assigned a separate nonzero source.
The source normalizer is the original full-slot one, not a new restricted
normalization. The continuous-mean estimate from AI paper 10 is not needed
for this subset norm, but remains a separate prerequisite in the broader
source ledger.

The generic sextic large sieve is not a replacement for the remaining
correlation. With all numerator powers retained, its optimistic Cauchy
cost is `61/144-d/6`, worse than the native `3/16-d/2` by `17/72+d/3`.
Restricting silently to sixth-power-free numerators would miss this cost.
These are comparisons of upper-bound methods, not lower bounds on the
actual signed sum.

## Remaining arithmetic decision

The useful next estimate is for the original prescribed theta/marked-row
correlation on the undetermined prime and square-core sectors. Neither
an arbitrary-coefficient sieve norm nor the known power-sector formula
supplies that signed estimate. In the narrow paper central band, a uniform
whole saving larger than `7/8-betaStar` plus the actual positive costs would
be sufficient; the deficit is not made zero by another representation.

The fixed signed-base average and saturated primitive prototype are now
closed at their precise scopes. Moving integral arrays and the unsaturated
total multiplicative-order source remain distinct open branches. No whole
Tier-1 family is marked exhausted: eight have been visited, zero exhausted.

Validation and immutable evidence are recorded in the
[checkpoint manifest](arithmetic-operator-integral-primitive-moment-gates.json).
Four strict leaves contain 75 local declarations and 64 theorem
declarations including helpers, with 15 namespace linters per leaf and
only standard axioms. Exact finite regressions make 31,527 checks; these
do not certify the unimported analytic residue identifications.
All changes remain local, with no public/root registration,
broad CI, commit or push.
