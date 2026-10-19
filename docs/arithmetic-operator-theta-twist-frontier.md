# Native theta twist: the pole survives and the long dual is unpaid

Research audit, 2026-10-18. This continues the
[continuous/theta split](arithmetic-operator-sextic-continuous-frontier.md).
The finite character and Gauss identities are isolated Lean results.
The residual-form functional equation, contour manipulations and Type-I
application below are **paper-level and conditional** on the analytic
inputs in [rStation paper 8/v1, §§5–6](https://rstation.ai/problems/riemann_hypothesis/papers/8/v1).
That AI-authored preprint is not imported as a Lean theorem or axiom.

The result is a precise failure of the proposed application of the
available Type-I bound. It is not an impossibility theorem for the signed
theta covariance. The strict imported `Re(s)>7/8` endpoint is unchanged.

## What the actual calibration permits

`localCalibration P` is a choice of a nonprincipal sixth-torsion character;
it is not definitionally the cubic character used in its existence proof.
At every good calibration prime, the actual canonical sextic character has
order six. Evaluating both characters on a generator of the residue-field
unit group proves

\[
 \operatorname{localCalibration}_P=\chi_P^{j_P},
 \qquad 1\le j_P\le5.
\]

The CRT calibration is exactly the product of these local characters,
including the nonunit zeros. For a good primary generator `p`, supported
primary physical modulus `s`, and the original coprimality exclusion,
reciprocity and the native Gauss scaling identity give

\[
 \frac{\chi_s(p)}{\operatorname{localCalibration}_P(s)}
 g_6(-m,s)
 =\epsilon(p,s)^{-j_P}g_6(-p^{j_P-1}m,s).
\]

This identity allows nonsquarefree physical moduli. The phase
`epsilon(p,s)` is the actual reciprocity phase, not an absolute value.
The finite CRT evaluation and this local transfer are checked in
[QuasiRHCalibrationNumeratorAudit.lean](../scripts/QuasiRHCalibrationNumeratorAudit.lean).

On paper, combining finitely many good calibration primes yields the
fixed numerator multiplier

\[
 M=\prod_P p_P^{j_P-1},\qquad NM\le\left(\prod_P NP\right)^4.
\]

Units and primes above 2 and 3 remain in fixed bad-prime/ray data. A
sufficient native period is 72: the two-supplement has period 8 and the
unit/lambda supplements have period 36. The global product assembly and
identification of that bad-prime character remain paper-level. The leaf
also proves a masked transfer of the canonical generator in the actual
`lowArithmeticCoefficient`, retaining its calibration denominator.
This does not give an unrestricted calibration theorem or uniformity in a
growing calibration conductor. The original exclusion mask is essential:
`j_P=1` removes `P` from `M`, but does not remove its exclusion from the
physical modulus. Multiplying the numerator can otherwise introduce new
imprimitive Gauss terms at excluded primes.

The analytic full-`D` mean must itself be established with these fixed
good-prime exclusions. The preprint advertises exclusions in its primitive
theorem, but its displayed full-series mean is not that theorem. A fixed
local-section extension or exact finite local inversion is still needed;
the exclusion mask cannot be dropped as part of the algebraic bridge.

## The native twist makes the dual character principal

Let a fixed residual form have multiplier `kappa^epsilon`, with the full
sextic residue using `epsilon=-1`, and write
`t(n)=N(n)^(1/12) rho(n)`. The native numerator twist is `chi_I(n)`, not
its conjugate. Expanding it by its additive Gauss sum and using the cusp
change `h d = 1 mod I` gives the unit weight

\[
 \chi_I(d)^{1+\epsilon}=1.
\]

Consequently the dual finite sum is principal. Its zero-frequency value
is `phi(I)` and its nonzero frequencies are the literal Ramanujan sums

\[
 c_I(n)=\sum_{d\mid(I,n)}Nd\,\mu(I/d).
\]

For the opposite orientation and a nontrivial squarefree `I>1`, the
constant term would vanish by character orthogonality. Applying that
conclusion to the native orientation would delete the term we need to
retain. The actual CRT/unit calculation, native model identity and
top-divisor statement below are checked in
[QuasiRHThetaTwistAudit.lean](../scripts/QuasiRHThetaTwistAudit.lean).

The resulting raw-residue twisted formula has a first polar term
proportional to

\[
 Q^{5/6}\,
 \frac{\phi(I)}{(NI)^{5/6}g(\overline\chi_I)}
\]

and a dual Ramanujan sum of length

\[
 K_I=\frac{(NI)^2}{Q}.
\]

Fixed cusp constants, ray phases, original smooth Mellin factors and the
fixed calibration level remain part of this formula. They cannot be
replaced by a universal scalar. The analytic formula is not a new Lean
Voronoi theorem; the finite principal-character cancellation is the
formally checked part.

## The same-weight Patterson subtraction does not remove that pole

The actual normalized native cubic factor multiplied by the normalized
sextic Gauss factor restores `mu(I)`. Retaining the original scalar model
gives the factor

\[
 \mu(I)\bigl(1-c\,r(I)\bigr),\qquad |r(I)|=(NI)^{-1/6}.
\]

Thus, on the unmarked `J=1` stratum, the first polar term has the form

\[
 (Q/Y)^{1/3}
 \sum_{I\asymp S}\mu(I)\eta_{\rm eff}(I)
 \bigl(1-c\,r(I)\bigr)(NI)^{-5/6}\frac{\phi(I)}{NI},
\]

with every fixed ray/cusp factor still in `eta_eff`. This is not
identically deleted by the same-weight Patterson subtraction, and is
not the same quantity as subtracting the physical theta vector. A fixed
cusp constant or the whole signed sum could still vanish; no universal
nonzero cusp constant or source nonvanishing is inferred here.
One must first identify `eta_eff` with a permitted finite combination of
fixed Hecke weights before applying a Hecke reciprocal estimate.

There is a potentially useful **conditional isolated-pole saving**.
If that identification and the smooth reciprocal estimate at
`7/8+epsilon` are supplied, its unmodeled part costs

\[
 (Q/Y)^{1/3} S^{1/24+\varepsilon}
 =Z^{1/6-3d/8+O(\varepsilon)}.
\]

The model part has the extra `(NI)^(-1/6)` and is bounded absolutely by
`(Q/Y)^(1/3)` up to subpowers. Against the old theta budget
`Z^(3/16-d/2)`, the first displayed exponent has margin `1/48-d/8`.
This margin is positive only before the depth endpoint `d=1/6`.
Neither the full native phase identification nor a bound for all marked
strata is asserted here. Paying this first pole would still leave the
following long dual.

## The second Type-I application has the wrong rate

Unlike the previously rejected direct substitution `a=I`, the transformed
dual has length `K=S^2/Q=Z^(3/2)`, which is longer than `S`. Divisor
incidences now exist. This removes the earlier support objection but
does not make their estimate strong enough.

Including the native `1/sqrt(NI)` spectral weight, the coefficient before
the dual Ramanujan sum has size `Q^(5/6)(NI)^(-11/6)`. After its exact
divisor expansion, write, suppressing only fixed bounded profiles,

\[
 \alpha_d=Nd\sum_{\substack{I\asymp S\\d\mid I}}
 a_I(NI)^{-11/6}\mu(I/d),\qquad |a_I|\ll1.
\]

Divisor Cauchy gives
`||alpha_(Nd~D)||_2 << D^(1/2) S^(-5/6)` up to subpowers. In the top
divisor annulus `D~S`, the unit cofactor survives: in a half-open annulus
`S<=Nd,NI<2S`, `d|I` forces `d=I`. There is no averaging over different
cofactors in that part of the coefficient array.

The raw-residue form of the available Type-I error is
`K^(1/3) D^(1/6) ||alpha||_2`. At `D~S`, the aggregate cost is therefore

\[
 Q^{5/6} K^{1/3} S^{-1/6}=\sqrt{QS}.
\]

With the original theta normalization `Q^(-1/2)Y^(-1/3)`, this becomes

\[
 S^{1/2}Y^{-1/3}=Z^{61/144-d/6}.
\]

It is worse than `Z^(3/16-d/2)` by `Z^(17/72+d/3)`. This is a comparison
of available upper bounds, not a lower bound for the actual signed sum.
The exact identity `mu(I)mu(I/d)=mu(d)` on squarefree `I` preserves a sign
in the joined expression; the cited Type-I norm estimate does not exploit
that sign to supply the missing saving.

The second density term is not a hidden cancellation of the first pole.
For the full transformed kernel, with
`W1(x)=x^(-1/12) Omega(x)` and `Htilde=x^(1/12) H[W1]`,

\[
 \widehat{\widetilde H}(5/6)
 =\frac{G(11/12)}{G(1/12)}\widehat W_1(1/12)=0.
\]

Here `G(s)` is the explicit two-Gamma factor in the cited functional
equation; `1/G(1/12)=0`. The small-argument behavior of `Htilde` makes
this Mellin value legitimate. Annular pieces can have nonzero individual
moments, so their boundaries must be retained when recombining them.
Separately, when the common fixed cusp/profile has been factored out,
the exact divisor density satisfies
`sum_d alpha_d/Nd = sum_I c_I sum_(d|I) mu(I/d)=0` for `I!=1`.
Both cancellations concern the second application only.

## Scope and next gate

The calibration and native orientation tests are useful infrastructure:
they specify exactly which analytic theorem would apply and prevent a
false pole deletion. The attempted two-step Type-I payment is frozen at
its explicit rate failure. No further sharpening of that componentwise
allowance is claimed as a new arithmetic mechanism.

A successful continuation must exploit a new signed relation in the
**whole** native theta/spectral-residual covariance, including the top
divisor block, or provide a stronger independent estimate for it. A
new transformation alone, an opposite character orientation, or another
scalar model subtraction would not discharge that obligation. Cube
rows, physical marks and growing calibration uniformity remain separate
obligations before any transfer to the existing endpoint.
