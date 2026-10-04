# Finite complete-prime jets do not settle the ceiling

The independent **42/25 ceiling throughout the original fixed candidate
strip at every height remains open**. This slice gives a checked method
obstruction and **zero new arithmetic ceiling credit**. It preserves the
paid Fejer balance theorem, the signed profile and every earlier no-go.

The next idea under examination was to constrain the unpaid unbalanced
profile by actual low-order Euler moments, or by detecting that the frozen
root-cloud model has an unrealistically flat low-order jet. The audit shows
why matching any finite collection of such moments is insufficient when the
remaining analytic part is controlled only by a geometric coefficient bound
with an unspecified constant.

## Exact arithmetic head, unchanged obstructive tail

Let `b` be the frozen array in `ZetaRieszCeilingClusterPowerAudit`, with
`M=131072`, `u=10001/20000`, exposed synthetic selected residue `-2` and
the unchanged finite local synthetic negative integer divisor. For any
finite head length `J` and any actual height `y`, define the regression
control

\[
b^{J,y}_n=
\begin{cases}
u^{n+1}\operatorname{ordinaryPrimeLogMoment}_n(3/2+iy),&n<J,\\
b_n,&n\ge J.
\end{cases}
\]

The head uses the **complete ordinary-prime series**, rather than a prime
sample or a thinned population. The patched infinite tail is **not**
identified with that series. No synthetic position is identified with an
actual `NontrivialZetaZero`.

The exact correction is the finite polynomial

\[
Q_{J,y}(t)=\sum_{n<J}(A_n(y)-b_n)t^n.
\]

`patched_local_ledger`, `hasSum_patched_regular` and
`patched_generating_analytic` prove that this polynomial changes only the
regular part of the frozen local model. The singular modes, their
multiplicities, exposure and strip geometry stay unchanged. All endpoints,
including orders zero and one, remain in the polynomial and the evaluator.

The complete head itself satisfies the independently proved, height-uniform
Euler envelope

\[
\|A_n(y)\|\le (2u)^{n+1}
 +640u(n+1)(10u/7)^n.
\]

`complete_ordinary_envelope` proves this using ordinary-prime coverage and
the **complete real-axis von Mangoldt mass**. It does not compare the norm
of an ordinary-prime series to the norm of a phased von Mangoldt series.
The frozen tail passes the same envelope, so the patch passes it at **every
order**, with no extra allowance at the splice.

## The analytic patch cost is explicit

Keep the whole coefficient price

\[
H_J=\sum_{n<J}\|A_n-b_n\|(4/3)^{n+1}.
\]

Then every order satisfies

\[
\|h_n^{\rm patched}\|
\le(4M+H_J)(3/4)^{n+1}.
\]

This is a genuine analytic representative and exact power-series identity,
not a radius inferred solely from sampled coefficients. The constant is
retained. It is not claimed to be the actual zeta remainder, nor to satisfy
every correlation or every sharper height-dependent bound of that remainder.

For **512 exact complete-prime moments**, rational block estimates give,
uniformly in `y`,

\[
H_{512}\le10^{77},\qquad
\|h_n^{\rm patched}\|\le10^{78}(3/4)^{n+1}.
\]

The proof uses no numerical zeta evaluations. The elementary blocks are
`(10001/10000)^512 <= 2` and `(4/3)^128 <= 10^17`. A crude complete head
bound `200000` suffices. These are model remainder constants, **not** native
carrier costs or a price already paid in the endgame.

## The same signed evaluator still exceeds the target

Finite modification preserves `b^{J,y}_n -> -2`. Therefore the **same**
`-traceError - harmonicEvaluation` expression, with the original moving
length, both factorial prefixes, adjacent orders and single diagonal, has
limit

\[
-2+4c_{\rm ret}(10001/20000)
=1.68051281186022328837\ldots>42/25.
\]

`eulerPatch_matches_joined` also proves exact agreement with the complete
arithmetic finite evaluator at every `N` with `N+1<J`. Thus matching the
signed finite evaluator, rather than only its individual moments, does not
settle the infinite tail either.

The terminal theorem `no_ceiling_from_finite_euler_head` rules out a
generic ceiling deduction based **only** on finite complete-prime head
agreement and the every-order Euler norm envelope. Additional information
about the actual complete prime tail or its correlated actual analytic
remainder remains essential. This theorem is not a counterexample to the
ceiling for actual zeta zeros, and supplies no native entry-order certificate.

## Numerical normalization and precision audit

The optional probe encloses **64 complete ordinary-prime coefficients** at
each of heights 54 and 1000. It uses the exact prime-power Mobius inversion

\[
u\sum_{q\ge1}\mu(q)(-\zeta'/\zeta)
       \bigl(q(3/2+iy-ut)\bigr).
\]

The divisor identity `sum_{q|m} mu(q)=1_{m=1}` removes proper powers before
any signed detector scan. Dilations through 128 are evaluated; the omitted
analytic tail is enclosed coefficientwise by
`20*(3/5)^129*(3/4)^n`. On `|t|<=4/3`, the base real part exceeds `4/5`.
For large dilations the elementary complete integer-series bound at four
gives `|Z(qs)|<=16*2^(-4q/5)`. The replay checks its explicit integral
bound and the geometric constants. This auxiliary numerical Mobius
implementation is not imported into the Lean proof.

The independent **420-bit** replay extracts coefficients from log series,
rather than the probe's derivative quotient. It evaluates the uncollapsed
trace and harmonic formulas independently, with every diagonal and integer
boundary retained. It checks 128 coefficient enclosures, ten finite joined
evaluations and six exact pre-resonance zero plateaux of the patched model.
The eventual reverse inequality comes from Lean, not a sampled plateau.

An earlier 512-order, 360-bit attempt is retained as
`.lake/riesz-ceiling-euler-jet-audit/probe-512-inconclusive.json`. Its wide
high-order Taylor intervals give inflated norm-price upper bounds, including
one above `10^199`. Those numbers are **interval uncertainty**, not actual
prime mass, and cannot contradict the formal `10^77` bound. The replay of
that data was stopped after the precision problem was identified. The
successful lower-order regression is a normalization check; it is not
described as a numerical verification of 512 actual coefficient values.
The arbitrary-`J`, all-height and concrete-512 results are proved in Lean.

## Literature check and next mathematical requirement

[Ivic's multiplicity paper](https://arxiv.org/abs/1706.08268) studies bounds
depending on height and local zeta moments. It does not give fixed-strip
all-height simplicity to complete this goal.

[Seip's Helson-zeta paper](https://arxiv.org/abs/1812.11729), Section 1.2,
separates compact Euler-half-plane vertical-translate convergence from
meromorphic continuation and zero data. Its unconditional prescribed-zero
Theorem 1.4(i) reaches real part `39/40`; the full-strip alternative assumes
RH. It is a warning against an unjustified continuation inference, not a
counterexample in our `Re rho >= 0.99995` region and not a Lean premise.

The next arithmetic target remains a **cofinal signed constraint on the
actual unbalanced divisor/complete-prime aggregate**. Another finite jet,
another free analytic-remainder model, or another conditional coherent-phase
sector cannot substitute for it. No full ceiling, simple-zero floor, zero
exclusion or RH claim is made here.

Proof: [ZetaRieszCeilingEulerJetAudit.lean](../RiemannGaussian/ZetaRieszCeilingEulerJetAudit.lean).
Scoped check: [CheckRieszCeilingEulerJetAudit.lean](../scripts/CheckRieszCeilingEulerJetAudit.lean).
Audit: [riesz-ceiling-euler-jet-audit.json](riesz-ceiling-euler-jet-audit.json).

The leaf, 14 linters, transitive standard-axiom check and optional numerical
replay run locally. No root registration, public metadata edit, wider gate,
subagent, commit or push is part of this slice. Prior proof/probe pins and
concurrent semiprime work remain preserved; the full goal stays active.
