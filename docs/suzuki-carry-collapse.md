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
