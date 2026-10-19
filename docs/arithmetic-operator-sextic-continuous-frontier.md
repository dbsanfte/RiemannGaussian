# Sextic contour remainder and the retained theta covariance

Research preflight, 2026-10-18. This is a **conditional, paper-level
application audit**, not a new imported theorem or an RH estimate. The
new candidate input is bramble_trace,
[Primitive sextic Kubota means and a sharp sixth-power-free large sieve,
v2](https://rstation.ai/problems/riemann_hypothesis/papers/10/v2),
especially Proposition 3 and Corollary 5. It is an AI-authored research
preprint. Its analytic theorems have not been checked in Lean here.

## The actual physical vector is a full Gauss image

The imported `LowRowMellin.lowAdditiveCoefficient` and
`LowGaussEnergy.lowGaussColumn_row` retain every physical modulus, not only
squarefree moduli. Write `q=Norm(A)` and

\[
 f_C(A)=\mathbf1_{\text{calibration exclusions}}
 \frac{\chi_A(C_{\rm gen})}
 {C_{\tau}\,C_{\rm residue}(A)},\qquad
 w_v(x)=W_1(x)x^{-1/2+iv}.
\]

On one fixed native ray, the exact finite physical sum is

\[
 L_{Y,v}(m)=Y^{-1}\sum_A
 w_v(\operatorname{Norm}(A)/Y)f_C(A)
 \frac{g_6(-m,A)}{\sqrt{\operatorname{Norm}(A)}}.
\]

Compact support makes this a finite sum. The useful normalized image is
`P=Y^(1/2)L`. This keeps the original smooth profile, calibration and
imprimitive terms. It is not automatically the squarefree character
adjoint in the preprint's Corollary 5. At `A=p^2,m=p`, an imprimitive
Gauss term can be nonzero although `g_6(1,p^2)=0`. Factoring all rows as
`g_6(1,A) conjugate(chi_A(m))` would delete this term.

Accordingly, the relevant Mellin series is the **full** series

\[
 D_\nu(r,s)=\sum_A\nu(A)g_6(r,A)\operatorname{Norm}(A)^{-s},
\]

not the primitive series with `(A,r)=1`. For the canonical fixed
calibration, a finite reciprocity/character expansion should absorb
`f_C` into fixed numerator multiples and the permitted local sections.
That exact basis bridge must still be proved. An arbitrary fixed
`CalibrationData` must not silently be granted the preprint's restricted
local-character hypotheses; a growing calibration conductor would also
need uniform estimates not supplied there.

## An unrestricted full-series consequence of Proposition 3

Conditional on the preprint's Proposition 3, its `B=1` case gives

\[
 \sum_{a\asymp A}^{a\ \mathrm{squarefree},\,(a,h)=1}
 |D_\nu(ha,1+\eta+it)|^2
 \ll (\operatorname{Norm}(h)A)^\varepsilon
 \operatorname{Norm}(h)^{1/2}A(1+|t|)^6.
\]

Every nonzero ideal numerator has a unique decomposition `n=a h`, where
`a` is the product of the primes occurring to exponent one and `h` is
powerful. Thus `(a,h)=1`. For `Norm(n)<=Q`, the contribution of a fixed
`h` is at most `Q/Norm(h)^(1/2)`, up to subpowers and the height factor.
Writing uniquely `h=r^2 s^3` with `s` squarefree gives

\[
 \sum_{\substack{h\ \mathrm{powerful}\\\operatorname{Norm}(h)\le Q}}
 \operatorname{Norm}(h)^{-1/2}
 \ll\log(2Q),
\]

using the ideal harmonic sum for `r` and absolute convergence of
`sum_s Norm(s)^(-3/2)`. Consequently the full series has a candidate
unrestricted-numerator mean of size `Q^(1+epsilon)(1+|t|)^6`.
This argument retains all numerator valuations. Fixed numerator
multipliers can be handled with their fixed constants; they are not
uniform growing parameters for free.

Only the `B=1` proof is needed for this deduction. At the natural
modulus length `sqrt(A)`, its sextic sieve terms are
`A, sqrt(A), A, A^(3/4)`, each at most `A`. The functional-equation
length `K sqrt(A)` has `K` proportional to
`sqrt(Norm(h))(1+|t|)^5`. This yields the displayed full-series mean
without the preprint's quadratic-sieve or primitive-inversion steps.
The full finite-vector functional equation, sextic sieve, contour shift
and fixed local-section identification are still analytic inputs.

The internal large-sieve length calculation and pole-cancelling
functional-equation absorption were independently reviewed in this
session. That review found no algebraic gap in this deduction conditional
on Proposition 3. It does not certify the cited finite-vector analytic
continuation or all of the preprint's external inputs.

## The improved part and the part it leaves

After the calibration bridge and Mellin shift, the expected exact split
has the form

\[
 P_{Y,v}(m)=Y^{1/6}\widehat w_v(2/3)\rho_\nu(-m)+E_{Y,v}(m),
 \qquad \sum_{m\asymp Q}|E_{Y,v}(m)|^2\ll Q^{1+\varepsilon}.
\]

Here `rho` is the **fixed finite combination of full theta residues**
with the calibration scalars and fixed numerator multiples from that
bridge. It is not the scalar Patterson model `Norm(I)^(-1/6)` on the
spectral ideal. Fixed-form residual
Rankin--Selberg theory gives the comparison
`sum_(m~Q)|rho(m)|^2 << Q^(5/6+epsilon)`, with all numerator valuations.
The full-residue normalization and its relation to that Fourier bound
are described in
[Averaged Type-I estimates for primitive sextic Kubota residues,
v1, §§2--4](https://rstation.ai/problems/riemann_hypothesis/papers/8/v1).

The height profile also needs its real cost retained:
`widehat(w_v)(1/2+eta+it)=widehat(W1)(eta+i(t+v))`.
Its integral against `(1+|t|)^3` is `O((1+|v|)^3)` for the fixed smooth
annular profile. The existing outer Mellin transform of `W0` can pay
this polynomial factor; it must not be replaced by uniformity in `v`.

Retain the same literal spectral residual `R_D(m)`. Granting its existing
nominal energy `sum|R_D|^2 << Q`, a bounded fixed profile and normalizer
`(QY)^(-1/2)`, Cauchy gives two different budgets:

| Part | Budget | At `Q=Z^(5/6-2d)`, `Y=Z^(23/48-d)` |
|---|---|---|
| Continuous remainder | `(Q/Y)^(1/2)` | `Z^(17/96-d/2)` |
| Retained theta pairing | `Q^(5/12) Y^(-1/3)` | `Z^(3/16-d/2)` |

The continuous term is better by `Z^(-1/96)`. The theta term stays at
the old critical budget. These are conditional **unmarked-stratum
exponent calculations**, not a theorem for every native mark, height,
contour or profile. The remaining signed term is explicitly

\[
 Y^{1/6}(QY)^{-1/2}\widehat w_v(2/3)
 \sum_m \Omega(m)\rho_\nu(-m)R_D(m).
\]

No claim that this theta term alone carries the full original analytic
source is made before its contour/source bridge is proved. It certainly
cannot be deleted merely because the spectral cubic Gauss factor was
replaced by a same-weight Patterson model.

The pole-cancelling kernel in the auxiliary absorption proof is not the
original physical Mellin kernel. It removes a residue from that proof
step, not from the original native sum. The original kernel still has
the theta-residue term displayed above.

## Why the available Type-I theorem is not that signed estimate

In the simplest native `J=1` stratum the spectral residual has the form

\[
 R_D(m)=\sum_{\substack{I\ \mathrm{squarefree}\\NI\asymp S}}
 b_I\bigl(G(I)-c\,\operatorname{ray}(I)(NI)^{-1/6}\bigr)\chi_I(m),
\]

with the actual coefficients and masks. General strata keep
`chi_J(m)^3`, the completed-index condition and the marks. The cited
residue Type-I theorem instead treats weights `sum_(a|m) alpha_a`, with
`Norm(a)<=Q` and an otherwise unrestricted plain factor.

The direct substitution `a=I` is impossible at the current native scales:

\[
 S=Z^{7/6-d},\qquad S/Q=Z^{1/3+d}>1.
\]

Eventually those divisor incidences are empty on the numerator annulus,
whereas the actual character entries on units are nonzero. Reciprocity
or a further summation formula could change the indexing, but its
weights, boundaries and source would require a new proof. The existing
Type-I theorem does not perform that transformation.

## Decision

Preserve the full-image mean as a concrete external analytic candidate.
Its advantage over a generic large-sieve norm is confined to the
continuous remainder. The next genuinely new estimate must control
the **theta-residue/spectral-residual covariance** with the same
weights, including calibration, cube rows and marks. Do not replace
it by a divisor convolution, cancel it against the wrong Patterson
model, or use positivity of a projection as a signed estimate.

The strict imported `Re(s)>7/8` endpoint is unchanged. No theorem from
either rStation preprint is introduced as a Lean axiom.

## Follow-up: the exact native twist and its long dual

The [next audit](arithmetic-operator-theta-twist-frontier.md) now proves
the local canonical-calibration and masked numerator-transfer identities
in Lean. Global good/bad-prime assembly and applicability of the full-`D`
mean with the original fixed exclusions are still separate obligations.

It also checks the native twist orientation: the inverse Kubota multiplier
and numerator character give a principal unit sum. Its polar term survives;
the actual same-weight model subtraction leaves
`mu(I)*(1-c*pattersonRatio(I))`, with every native phase retained.
The further summation formula has a longer dual `K=S^2/Q`, so the earlier
empty-divisibility objection no longer applies there. Nevertheless the
available second Type-I error costs `S^(1/2)Y^(-1/3)`, worse than the old
theta budget. Its second density term vanishes and cannot be used to
cancel the first pole. These analytic/rate deductions remain paper-level,
conditional on the cited fixed-form theorem. The joined signed theta
covariance is still unpaid.
