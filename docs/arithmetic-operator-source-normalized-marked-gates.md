# Actual source normalization and marked cancellation gates

Research checkpoint, 19 October 2026. This completes the same-data source
normalization of the native square-sector estimate and tests two distinct
uses of the remaining prime marks. The strict imported `Re(s)>7/8` endpoint
is unchanged. No RH or new zero-free result is claimed.

## The proved arithmetic bound

[QuasiRHSquareSourceNormalized.lean](../scripts/QuasiRHSquareSourceNormalized.lean)
now uses the **same** bounded-one source windows, moving ray-prime pools,
Gaussian profiles and nonzero normalizer as the original detector. Its
`original_source_normalized_square` theorem proves

\[
\left\|\frac{\mathrm{centralSquare}(Z)}{\mathrm{normer}(Z)}\right\|
\le C Z^{5/72+255\varepsilon+2\varepsilon_G+\nu}
\]

eventually, for fixed positive small losses. There is no assumed scalar
normalizer bound: the proof invokes the actual native ray-normalizer
theorem after checking the identical pool data. Distinct positive slot
lengths give eventual disjointness of those pools. The finite Gaussian
profile family is constructed from the same source windows, and the
theorem also returns their original full-probe identity.

This term still grows with Z. Its exponent is smaller than the candidate
source exponent near the current `7/8` boundary; it is not a theorem that
the whole detector tends to zero. All marks, cubes, physical masks and
normalizations remain. The exact source accounting is still

\[
\frac{\mathrm{rawProbe}}{\mathrm{normer}}-F_{\rm all}
=\frac{\mathrm{centralSquare}}{\mathrm{normer}}
 +\left(\frac{\mathrm{centralOdd}}{\mathrm{normer}}-F_{\rm all}\right)
 +\frac{\mathrm{remoteAll}}{\mathrm{normer}}.
\]

The whole series ledger follows by assembly of the existing exact native
identities; it is not advertised as an additional newly compiled theorem.
RemoteAll stays joined. No hypothetical-zero source is assigned to the
square sector or any other subset. The signed central-odd term remains open.

## Join the compensation marks before estimating

The complete subset polynomial already exists in the native `TuplePrincipal`
infrastructure. At one prime it is a factor

\[
B\,\mathbf1_{P\mid I J^3}-c.
\]

[QuasiRHJoinedMarkVarianceAudit.lean](../scripts/QuasiRHJoinedMarkVarianceAudit.lean)
proves the exact join for the actual completed mask and high summand,
retaining cubes and exclusions. It then proves, on the actual prime
quotient with `q=Norm(P)`,

\[
\frac1q\sum_{a\bmod P}|B\mathbf1_{a=0}-c|^2
=\frac{|B|^2(q-1)}{q^2}+|B/q-c|^2.
\]

Thus even perfect mean centering leaves positive variance for B nonzero.
The joined product energy over prime-quotient coordinates is also exact.
This closes the universal shortcut from zero mean to zero recovery energy.
It does **not** prove a lower bound for the actual incomplete annular sum
or show that the signed estimate is impossible. In particular, the old
`D_g` recovery cost is a method cost, not an actual signed lower bound.

## A conditional marked harmonic gain does survive

A separate paper-level audit extends the pinned
[harmonic Möbius recovery argument](https://github.com/Gaozhongpai/seven-eighths-refinement-certificates/blob/8c995528481f144debf70ffd25678a3fdf379fd4/methods/harmonic_mobius_ratio_recovery.md)
to a fixed number of distinct prime marks. For one mark outside a fixed
cube, the exact original negative Mellin opening replaces `P_Z(s)^2` by

\[
(1-c)P_Z(s)^2-
 (1-\psi(P)q^{-s})P_Z^P(s)^2.
\]

After reflection, the restricted common-factor coefficient is exactly
`1_(x,A)=1 * S_Z(x;R union A)`. The finite Euler children keep their
different kernel scales. Using the full three-term HR.7 bound, rather
than only its short-dual corollary, preserves the original fixed-x range
`X<=D/sqrt(U)`. For k fixed marks in the stated coefficient range, the
extra norm constant is at most `3*3^k`, with the stated subpower factors.

This is a conditional deduction from the external HR analytic estimates,
not a newly imported Lean theorem. The native coherent sum over growing
prime pools, its prescribed Gauss/plain coefficient, cube-child ranges
and the balanced large internal-ratio complement remain unpaid. A bound
for each fixed tuple does not pay their collective sum for free.

## The two common divisors are different

HR's reflected common factor pairs the same inducing character with its
conjugate, so that phase cancels on units. The physical/spectral Gauss gcd
does not have that property. In the squarefree subcase with cube equal to
one, write b=g b0 and I=g I0. Native CRT factorization gives

\[
\frac{\gamma(gb_0)}{\gamma(gI_0)}
=\frac{\gamma(b_0)}{\gamma(I_0)}
  \chi_g(b_0)\chi_{b_0}(g)
  \overline{\chi_g(I_0)\chi_{I_0}(g)}.
\]

The common Gauss root cancels but its cross-factor phase remains. Exact
Eisenstein-prime examples of norm157, in the same primary and mod-four
ray class, give different phases for the same residual pair. This rules
out silently applying HR's uncoloured harmonic estimate to this different
gcd sum. A theorem controlling its moving cubic phase and actual weights
would be new input. The deduction uses existing native CRT theorems;
the accompanying exact finite probe is not a new asymptotic proof.

## Validation and next target

The two new strict isolated leaves have 14 explicit theorems and two
literal definitions, with 41 all-local declarations and 27 theorems
including generated helpers. Both pass all 15 namespace linters,
file/CLI warnings-as-errors, and recursive all-local standard-axiom
audits. Independent source and mathematical reviews distinguish compiled,
conditional-paper and finite-diagnostic claims. The three exact probes
perform 115,475 checks; these do not certify asymptotic estimates.

The precise remaining target is the collective signed
`centralOdd/normer-F_all` estimate with the original marks, cube powers,
phases and principal boundaries. The small-ratio harmonic identity is a
possible tool, but neither fixed-mark recovery nor mean centering closes
that target. Eight Tier-1 roadmap families have been visited; none is
claimed exhausted. The research goal remains active.

The [checkpoint manifest](arithmetic-operator-source-normalized-marked-gates.json)
records source hashes and the formal/paper boundaries. The publication
also preserves the accumulated [Siegel review](siegel-interpolation-review.md)
and previous scoped positive and negative results.
