# Native source transport and arithmetic coupling gates

Research checkpoint, 2026-10-19. This continues the
[exterior/physical application audit](arithmetic-operator-exterior-physical-transfer.md)
and the [Siegel interpolation review](siegel-interpolation-review.md).
The imported strict `Re(s)>7/8` theorem is unchanged. None of the results
below is a new signed theta estimate or a new zero exclusion.

## Full transport must retain the central floor population

The full-source audit now treats the nonprincipal, ramified and moving-height
steps separately. On paper, the same normalized detector has the form

\[
 \operatorname{Probe}(Z)
 =\operatorname{Signal}(Z)+F_{\mathrm{all}}(Z)
  +O\!\left(Z^{\beta_* -11/16-\sigma_0}\right)
\]

for a suitable fixed positive saving, when
`83/96 < betaStar <= 7/8`. Here `F_all` is the original complete central
cube sum, **including its floor rows**, marks, calibration, ray phases and
moving heights. This is a paper-level replay, not a new Lean transport
wrapper. The conditional analytic full-`D` input from the preceding
checkpoint remains unimported.

The selected ramified local estimate has a real domain extension to check:
its strongest finite branch requires `Re(x)>=3/4`, rather than `7/8`.
The full branch table in the audit retains all residue classes and gives
the old constants `385/961`. Existing central-bin and arbitrary-saving
cube APIs already permit the required broader domain. The four remaining
error exponents are

\[
\begin{aligned}
 &\beta_*-11/16-63/800+8e+\nu, &&-A+\nu,\\
 &\beta_*-11/16-17/48000+\nu,
 &&\beta_*-11/16+e-\alpha\ell_{\min},\qquad \alpha=4/5.
\end{aligned}
\]

All small parameters and the enlarged exclusion set are fixed before
`Z` grows. The calibration must be rebuilt for that set. No attained
rightmost zero or uniformity as the margins vanish is assumed.

The source is preserved in **`normalizedProbe - F_all`**. The identity
alone does not place it in `F_all`, nor in the physical theta component.
The available `Z^(3/16+loss)` probe bound is not source-small below `7/8`.
Any later source-allocation claim needs a further estimate or the exact
joined accounting of both terms. Independent review caught and corrected
this distinction in the detailed transport audit.

The old step that *deletes* the floor rows cannot cover this whole band.
[QuasiRHFullSourceRateAudit.lean](../scripts/QuasiRHFullSourceRateAudit.lean)
proves, for the actual native exponent,

\[
 \operatorname{sourceExponent}(51/100,13/16,1,1/100)
 =109/600=3/16-7/1200.
\]

With loss `L>=0` and desired saving `sigma>0`, its exact budget is

\[
 109/600+L\le\beta_*-11/16-\sigma
 \quad\Longleftrightarrow\quad
 1043/1200+L+\sigma\le\beta_*.
\]

Thus this envelope only supports deletion above `1043/1200`, and exceeds
the source exponent at `83/96` by `11/2400`. This is a limitation of the
existing upper bound, not a lower bound on the actual signed floor sum.
Keeping the rows in `F_all` avoids that unsupported deletion. An estimate
for the whole signed sum must keep them too, or pay them by genuinely
stronger arithmetic.

## Calibration-character averaging is exactly rank one

Changing a calibration character is different from the earlier averaging
over residue-unit translates. Nevertheless, at fixed coprime Eisenstein
moduli `a,b`, fixed frequency `h`, and unchanged arbitrary physical
function `F`, the native CRT identity gives

\[
 \operatorname{mixed}_{\chi}(h)
 =\underbrace{\chi(b)\operatorname{Gauss}_{\chi}(h\bmod a)}
     _{\operatorname{factor}_{\chi}(h)}
   \operatorname{bare}_{F}(h).
\]

[QuasiRHCalibrationFamilyAudit.lean](../scripts/QuasiRHCalibrationFamilyAudit.lean)
proves this for the literal finite Eisenstein quotients. It then proves
that any finite normalized character code equals

\[
 \sum_\chi \lambda_\chi
 \frac{\operatorname{mixed}_\chi(h)}{\operatorname{factor}_\chi(h)}
 =\left(\sum_\chi\lambda_\chi\right)\operatorname{bare}_F(h),
\]

provided the actual factors being divided by are nonzero. Zero factors
give zero raw rows and remain explicit. A zero-sum code deletes the entire
common coefficient, including any source it carries; a sum-one code is
unchanged. Every identity holds for arbitrary `F`, so this proposed
averaging mechanism fails the collapse audit before an arithmetic bound
is attempted.

The conclusion does not cover changing moduli, changing `F`, or projecting
separate theta components. In particular, it is not an impossibility
theorem for a genuine signed theta estimate. Exact finite regressions in
`Q[zeta_546]` check 1,365 CRT identities and 1,092 rank-one relations,
including excluded frequencies and signed complex physical weights.

## The actual cubic–sextic phase cancels, but transfers the index

The native completed squarefree spectral factor is
`mu(I)*Gamma1(I)^(-1)`. Its numerator character forces `(m,I)=1`.
Consequently the tempting sextic `j=1`/`j=3` residue relation is outside
the actual support. The relevant relation is `j=0`/`j=4`.

Using the full finite-section sextic residue relation on paper, including
its CRT reciprocity factors, gives

\[
\begin{aligned}
 &\mu(I)\Gamma_1(I)^{-1}\chi_I(m)\rho_\nu(-M m)\\
 &\qquad=\mu(I)(NI)^{1/3}\nu(i)\chi_I(-M)^{-1}
          \rho_{\nu R_i}(-M m i^4),
 \qquad i=\operatorname{primaryGenerator}(I).
\end{aligned}
\]

The fixed calibration numerator `M`, the minus sign, the section twist
`R_i`, and every original mark/profile remain. This is a real coupling
between the native cubic Gauss phase and the sextic residue. But for the
correct normalization `t(n)=(Nn)^(1/12)rho(n)`, the transfer multiplier has
modulus **one**. It provides no automatic contraction.

For disjoint `I,J`, the actual cube character satisfies
`chi_J(m*i^4)^3=chi_J(m)^3`, including its nonunit zeros, because `12` is
divisible by `6`. For overlapping `I,J` that replacement is false: the
transformed numerator is a nonunit. The exact reindexing must retain
`chi_J(n/i^4)^3` and the condition `v_p(n)=4` for each `p|I`.

The transformed numerator scale is

\[
 Q S^4=Z^{11/2-6d},\qquad
 S=Z^{7/6-d},\quad Q=Z^{5/6-2d}.
\]

The exact restricted square sum transfers with factor `(NI)^(-2/3)`;
using that identity returns the old separate-energy bound. Replacing it
by a full interval square sum at the enlarged scale is worse. Thus a
Hecke annihilator or a norm reserve from this relation alone fails the
source/profile test. A collective signed estimate for the original
coupled weights remains possible and open.

The residue recurrence is not imported as a Lean theorem. Primary
references are [Kazhdan–Patterson](https://www.numdam.org/item/PMIHES_1984__59__35_0/),
with [the corrections](https://www.numdam.org/item/PMIHES_1985__62__203_0/),
and [Bröker–Hoffstein](https://arxiv.org/abs/1312.0568v1).
The full fixed-section application is paper-level. Its Gauss regressions
use floating arithmetic and are diagnostic, not exact certificates of
residues or analytic limits.

## A new common-integer restriction on signed cyclotomic rows

For the actual rational product

\[
 P_{b,M}=\prod_{2\le e\le M}\Phi_e(b)^{\beta_e},
 \qquad b\ge2,\quad \beta_e\in\mathbb Z,
\]

a supplied prime `q` for which `b mod q` has exact order `d` isolates
`Phi_d(b)` among all these factors whenever `M<d*q`. Indeed, if `q`
divides another `Phi_e(b)`, then `d|e`; below that cutoff `q` cannot divide
`e`, and the finite-field cyclotomic root theorem forces `e=d`.
The `q`-adic valuation of the full product therefore equals
`beta_d*v_q(Phi_d(b))`. Integrality forces `beta_d>=0`.

This is an actual fixed-base constraint for growing signed row families,
not an arbitrary-weight rearrangement. The witness-level proof is in
[ArithmeticOperatorTotalTraceSourceAudit.lean](../scripts/ArithmeticOperatorTotalTraceSourceAudit.lean).
It includes the exact signed-product valuation and a literal base-two
example. Global primitive-divisor existence and the following analytic
consequences remain paper-level.

The classical primitive-divisor theorem gives, for `M>=36`, nonnegative
exponents throughout `sqrt(M)<d<=M`; its exceptional small indices lie
outside this shell. With negative exponents bounded by `M^a`, their
linear complete-base prime trace has size
`O_kappa(M^(a+1/2)*log(M)^2)` at prime cutoff `M^kappa`, for fixed
`kappa>1`. Its row-Mellin transform is therefore analytic to the right of
`a+1/2`. For bounded signed corrections, any already established source
farther right must remain in the nonnegative packet.

This does **not** identify that linear trace with the prime-depth phase
of the integer product. Nor does it prove the total `kappa>1` Mellin source:
the growing modulus/nonprincipal covariance and the moving max boundary
remain unpaid. Primitive witnesses can exceed the physical prime cutoff.

## Research consequence

The new integer restriction is reusable, and the full-source audit prevents
an incorrect extension based on deleting floor rows. Two proposed free
cancellations—normalized calibration averaging and the unitary residue
exchange—are now precisely delimited. The missing endpoint input remains
an independent estimate for the source-bearing signed difference, with
the actual theta pairing and full central population accounted for, or a
genuinely source-sensitive integer constraint beyond these identities.
A theta estimate alone does not automatically pay the central term.
Eight Tier-1 families have been
visited; none is declared exhausted.
