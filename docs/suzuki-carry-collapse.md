# Carry determinant and global collapse audit

Local checkpoint, 2026-10-06; base `9213afd`. The rowwise/SBP payment
class remains closed. This checkpoint proves no arithmetic floor, zero
exclusion or RH statement.

## Actual fourth-order expansion

Write the exact signed tent moments as

\[
 M_j(x)=\sum_{k<\lceil6/x\rceil}
       (-1)^k\operatorname{tent}\left(\frac{(k+1)x}{2}\right)
       \left(\frac{(k+1)x}{2}\right)^j.
\]

For every `Re(s)>0`, Lean now proves the actual expansion

\[
 F(s,\tau)=F(s,0)+B_s\tau^2+C_s\tau^4+o(\tau^4),
\]

with the exact coefficients

\[
 B_s=\int_{\mathbb R}e^{st}
       [M_1(e^t)^2-M_0(e^t)M_2(e^t)]\,dt,
\]

\[
 C_s=\int_{\mathbb R}e^{st}
       \left[\frac{M_2(e^t)^2}{4}
       +\frac{M_0(e^t)M_4(e^t)}{12}
       -\frac{M_1(e^t)M_3(e^t)}3\right]\,dt.
\]

The proof controls the alternating profile uniformly as its spacing
tends to zero. It does not exchange an unbounded absolute jump count
with the Mellin integral. Odd terms cancel exactly before integration.
See [SuzukiCarryMellinJet](../RiemannGaussian/SuzukiCarryMellinJet.lean).

## Explicit exceptional equation

Every tent knot is on the common grid `12/n`. On
`12/(n+1)<x<=12/n`, define the finite alternating prefix

\[
 E_{j,K}(x)=\sum_{k<K}(-1)^k((k+1)x/2)^j.
\]

The moment polynomial is exactly

\[
 M_j(x)=2E_{j+1,n/3}-E_{j+1,n/6}-E_{j+1,n/2}
          +E_{j,n/6}+3E_{j,n/2}-4E_{j,n/3},
\]

where the integer divisions are literal. The upper endpoint and
coincident knots are retained. Substitution gives real polynomials
`bPolynomial n` and `cPolynomial n` for the two coefficient densities.
For a polynomial `P(x)=sum_j c_j x^j`, its cell response is exactly

\[
 I_n(P;s)=\sum_j c_j
   \frac{(12/n)^{s+j}-(12/(n+1))^{s+j}}{s+j}.
\]

Therefore

\[
 B_s=\sum_{n\ge1}I_n(b_n;s),\qquad
 C_s=\sum_{n\ge1}I_n(c_n;s).
\]

These identities and convergence are kernel-checked; no Hurwitz-zeta
identification from the optional probe is assumed. After the first N
cells, the certified errors are respectively

\[
 \frac{279}{\Re s}\left(\frac{12}{N+1}\right)^{\Re s},
 \qquad
 \frac{1296}{\Re s}\left(\frac{12}{N+1}\right)^{\Re s}.
\]

For `p=1-iy`, the exact fourth-order exceptional set is the set of
solutions of the explicit elementary series equation

\[
 B_p C_\beta=C_p B_\beta.
\]

`wedge_eq_zero_iff_explicit` and `exceptional_iff_wedge_zero` prove this
characterization using the polynomial series. **Emptiness of that set
for `|y|>=54`, `19999/20000<=beta<1` remains unproved.** This is an
explicit equation and a certified fixed-candidate evaluation method,
not a classification showing that every campaign candidate passes.

Outside that set, the actual expansion and the published determinant
gate give a fixed `tau>0` and a positive cofinal native source margin.
Merely replacing `0,tau,2tau` by `0,v*tau,w*tau` does not repair a
degenerate fourth-order wedge: its exact leading factor is
`v^2*w^2*(w^2-v^2)*(B_p*C_beta-C_p*B_beta)`. An exact sixth-jet regression
identifies the possible new minors, but no actual sixth-jet escape is
asserted. See
[SuzukiCarryMellinBranches](../RiemannGaussian/SuzukiCarryMellinBranches.lean).

## The complete arithmetic statistic

Let `K_H(d)` be the literal `familyKernel` with the native cyclic Mellin
code. All modulations, incidences, rows and lag orientations are already
joined. Lean proves exactly

\[
 S_H(y)=\sum_{1\le d\le3H}\Lambda(d)d^{-iy}K_H(d).
\]

There is no deletion of proper prime powers. The outer single-incidence
sector is zero exactly. With `f_H(d)=d^{-iy}K_H(d)`, a **global** finite
Abel identity, without any allowance, further gives

\[
 S_H(y)=-\sum_{0\le n\le3H}\psi(n)
                 [f_H(n+1)-f_H(n)].
\]

The boundary at `3H+1` is zero exactly. All integer kernel jumps and
the full height phase stay in this expression.

The normalized continuum kernel has exact Mellin symbol
`-continuumDet(p,s,tau)`. Its density/pole symbol is zero, while a
nonzero determinant retains the specified matched component. These
are response identities, not an actual-prime single-zero asymptotic.

## What the collapse does and does not imply

`weightedRows_eq_joined` proves the same row-to-denominator identity for
**arbitrary** weights `w(d)`. `weightedGram_eq_gcd` proves that the
endpoint-gcd identity also holds for arbitrary weights. Their equality
alone consequently adds no restriction on the arithmetic measure.
Indeed, universal annihilation for all weights is equivalent to a
pointwise zero kernel, as certified by exact delta-weight tests.

The untwisted von Mangoldt divisor identity still knows literal integer
factorization. At nonzero height its counterpart is the retained
twisted divisor sum; no bound on that observation at the required
source scale has been derived. This audit does not prove that future
prime-specific identities are impossible. It proves that the current
carry/gcd reindexings have collapsed to the displayed custom twisted
Chebyshev test and do not, on their own, estimate it.

The missing estimate `S_H=o(H^(1+beta))` (equivalently `S_H/H=o(H^beta)`)
is exactly a source-sensitive bound for that test. No such estimate is
proved here. Stop extending this carry route unless an independent
constraint on the actual prime sequence is supplied; do not replace
the dead rowwise payment by another equivalent prime-sum carrier.

See [SuzukiCarryCollapseAudit](../RiemannGaussian/SuzukiCarryCollapseAudit.lean)
and the focused [audit](suzuki-carry-collapse-audit.json).

## Local exceptional-equation follow-up

This follow-up starts at `2444467` and remains local. The earlier checkpoint
above records the proofs available at its publication; the following leaf
modules are not yet registered in the public root or explorer.

The real-exponent denominator is now proved nonzero independently of any
numerical evaluation:

\[
 B_\beta\ge\frac1{2000}>0\qquad(\beta\ge15/16).
\]

The proof uses exact rational Bernstein certificates for the literal cells:
`quadraticDensity x >= -x^2/8` for `0<x<=1`, nonnegativity for `x>=1`,
and the lower bound `243/2048` on `[9/4,11/4]`. Integrating these inequalities
proves the stated uniform margin. See
[SuzukiCarryRealJet](../RiemannGaussian/SuzukiCarryRealJet.lean).

Consequently the quartic exceptional equation is exactly either

\[
 B_p=C_p=0,
\]

or, when `B_p` is nonzero,

\[
 \Im(C_p/B_p)=0,\qquad
 \Re(C_p/B_p)=C_\beta/B_\beta.
\]

This is a proved classification equation, **not a proof that no campaign
point satisfies it**, or an enumeration of its solutions. The real and
imaginary wedge identities are in
[SuzukiCarryExceptionalPhase](../RiemannGaussian/SuzukiCarryExceptionalPhase.lean).

There is now a genuinely different finite code escaping proportional
nonzero jet vectors. Define the same-amplitude phase contrast at each scale

\[
 D_H(s,\tau)=C_{H,\tau/H}(s)-C_{H,0}(s).
\]

Use four responses, with phases `0,tau/H` at `H` and `0,tau/(2H)` at `2H`,
and coefficients

\[
 (-D_{2H}(p,\tau),D_{2H}(p,\tau),D_H(p,\tau),-D_H(p,\tau)).
\]

The coefficients sum to zero **at each scale separately**, cancelling both
diagonal populations exactly. Their complete pole response is also zero
exactly. A specified matched component of multiplicity `m` has response
`-m * nativeScaleDet`; this is a diagnostic component identity, not a
single-zero asymptotic of the actual prime measure.

The normalized native determinant converges to

\[
 (2^p-2^\beta)
 [F(p,\tau)-F(p,0)]
 [F(\beta,\tau)-F(\beta,0)].
\]

Since `Re(p)=1>beta`, its scale factor cannot vanish and its modulus is
at least `2-2^beta>0`. The actual fourth-order expansions supply a common
fixed positive `tau` whenever the complex jet `(B_p,C_p)` is nonzero;
the two exponents may have different first nonzero orders. The determinant
is then eventually at least half its limiting modulus times `H^(1+beta)`.
There is no nonzero-wedge premise. See
[SuzukiCarryPhaseScaleGate](../RiemannGaussian/SuzukiCarryPhaseScaleGate.lean)
and the combined campaign endpoints in
[SuzukiCarryExceptionalGate](../RiemannGaussian/SuzukiCarryExceptionalGate.lean).

This jet-based endpoint leaves `B_(1-iy)=C_(1-iy)=0` as its sole alternative.
No theorem here excludes those common zeros for every `|y|>=54`. The
all-jet follow-up below now bypasses that alternative without claiming that
the two coefficients cannot vanish together.

The actual literal series has sharper certified tails, for `N>=11`:

\[
 |B_s-B_s^{[N]}|\le
 \frac{10}{\Re s+2}\left(\frac{12}{N+1}\right)^{\Re s+2},\qquad
 |C_s-C_s^{[N]}|\le
 \frac{24}{\Re s+2}\left(\frac{12}{N+1}\right)^{\Re s+2}.
\]

At `Re(s)=1`, Lean certifies both tail errors below `10^-18` after
32,000,000 cells. This theorem evaluates no finite prefix and certifies no
exceptional root. See
[SuzukiCarrySmallCell](../RiemannGaussian/SuzukiCarrySmallCell.lean) and
[SuzukiCarryCellCertificate](../RiemannGaussian/SuzukiCarryCellCertificate.lean).

Optional probes locate a suspected quartic exception near
`y=202268.98326694674735`, `beta=0.9999785531654088`. Arb enclosures witness
an IVT sign-change root of the **boundary/Hurwitz model**, and a separate
one-million-cell floating prefix agrees diagnostically. Identification of
that model with the literal Mellin coefficients has not been proved in
Lean. The floating prefix is not outward rounded. Therefore neither
calculation is recorded as a certified actual exception, and neither
disproves universal actual-wedge nonvanishing here. The probe outputs
explicitly distinguish those obligations.

The [focused follow-up audit](suzuki-carry-exceptional-audit.json) records
leaf builds, namespace linters and all-declaration axiom checks separately
from publication. No new prime/carry estimate has been attempted. The
independent signed Chebyshev bound, Suzuki floor, zero exclusion and RH
remain open.

## All-jet source-detector closure

The user authorized an all-jet bypass of the common-zero question. This
follow-up proves it for the **literal** continuum response and the same
four-response native code. It changes neither the tent amplitude nor the
carry masks. No boundary/Hurwitz model identification or numerical
nonvanishing premise is used.

The exact lag reindexing first joins both incidences and cancels the
diagonal. Its ordinary tent overlap has the checked quadrature identity

\[
 S_h(v)=\frac{h}{v}I(v)+R_h(v),\qquad
 |R_h(v)|\le\frac{2v}{h}\quad(v>0,\ h\ge1),
\]

where

\[
 I(v)=
 \begin{cases}
  2/3-v^2+v^3/2,&0\le v\le1,\\
  (2-v)^3/6,&1\le v\le2,\\
  0,&v\ge2.
 \end{cases}
\]

All grid endpoints are retained. The summable remainders give a spectrum

\[
 \mathcal B_s(v)=-\eta(s-1)\frac{I(v)}{v}
   +\sum_{h\ge1}(-1)^h h^{-s}R_h(v).
\]

Here `eta` is its entire continuation, not an ordinary Dirichlet sum on
the line `Re(s-1)=0`. The functional equation and the proved nonvanishing
of zeta on `Re=1` imply `eta(-iy) != 0` for every nonzero real `y`.
Consequently

\[
 \lim_{v\downarrow0}v\mathcal B_{1-iy}(v)
   =-\frac23\eta(-iy)\ne0.
\]

The spectral bridge to the actual response is exact for every `Re(s)>0`:

\[
 F(s,\tau)-F(s,0)
 =e^{(s+1)\log2}
   \int_{\mathbb R}e^{st}
   (\cos(\tau e^t)-1)\mathcal B_s(e^t)\,dt.
\]

It is proved first where the ordinary lag integral converges absolutely,
then by analytic continuation. The signed bulk and correction are joined
before continuation. See
[quadrature](../RiemannGaussian/SuzukiCarryPhaseQuadrature.lean),
[eta nonvanishing](../RiemannGaussian/SuzukiCarryPhaseEta.lean),
[the small-lag spectrum](../RiemannGaussian/SuzukiCarryPhaseSpectrum.lean),
and [the literal bridge](../RiemannGaussian/SuzukiCarryPhaseContinuation.lean).

The density `exp((s+2)*t) * bracket s (exp t)` is integrable, vanishes
above `log 2`, and is not zero almost everywhere at `s=1-iy`. Two exact
derivatives of the phase contrast produce its cosine transform. That
transform is entire in the bounded coordinate, and cosine-transform
injectivity is proved for integrable complex densities via uniqueness of
finite-measure characteristic functions. Thus the contrast cannot vanish
on any positive interval next to zero. For every `y != 0` and
`epsilon > 0`, Lean proves that some `0 < tau < epsilon` satisfies
`F(1-iy,tau) != F(1-iy,0)`.

The real-exponent margin `B_beta >= 1/2000` supplies a common sufficiently
small modulation. The endpoint
`SuzukiCarryAllJetGate.exists_fixed_campaign_code_source_lower` now proves,
for every `19999/20000 <= beta < 1` and every `y != 0`, that there is one
fixed positive `tau` with nonzero limiting determinant and, eventually,

\[
 \|\operatorname{nativeScaleDet}_H(1-iy,\beta,\tau)\|
 \ge\frac12\|\operatorname{scaleDet}(1-iy,\beta,\tau)\|
       e^{(1+\beta)\log H}.
\]

The campaign `|y|>=54` is included. The code still cancels the pole and
the diagonal exactly; all prime powers and the full phase remain in its
native statistic. The conclusion requires no exposure assumption and no
nonzero quadratic, quartic or wedge premise. See
[the endpoint](../RiemannGaussian/SuzukiCarryAllJetGate.lean),
[the integrable density](../RiemannGaussian/SuzukiCarryPhaseDensity.lean),
and [cosine injectivity](../RiemannGaussian/SuzukiCarryPhaseInjectivity.lean).

This closes the analytic **source-detector gate**, including the common-zero
case, without deciding whether `B_(1-iy)` and `C_(1-iy)` can actually vanish
together. It is a source response theorem, not an upper bound for the
literal prime statistic. The independent signed twisted-Chebyshev estimate
remains open, as do the Suzuki floor, zero exclusion and RH. The closed
rowwise/SBP and generic carry/gcd payment classes remain closed. These
leaves and their [focused audit](suzuki-carry-exceptional-audit.json) remain
local and are not registered in the public root or explorer.
