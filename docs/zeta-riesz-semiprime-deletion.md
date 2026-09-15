# Actual semiprime deletion at exposed zeros

Lean proves that the **original, uniquely counted semiprime band with a
prime factor at most (N^2)** has vanishing source-normalized response at
an exposed hypothetical right-half zero. It also removes that class from
the current full arithmetic carrier while preserving every earlier cut,
the exact negative multiplicity source and the signed Euler bridge.

The whole residual's independent cofinal signed floor remains open.
This result does not prove RH, a larger zero-free region, a numerical
starting order or a new zero-proportion certificate. No historical
novelty claim is made.

## Exact controlled component

Write (ho=eta+igamma), (1/2<eta<1), and

\[
u=\frac32-\beta,\qquad
D_N=\left\lfloor\frac{u^{-N}}{N+1}\right\rfloor,\qquad
X_N=(D_N+2)^2,\qquad L_N=\log X_N.
\]

The original band and fixed polynomial kernel remain

\[
\mathcal B_N=\{n:1\le n\le 2^{32N},\quad N\log(2)/4<\log n\},
\qquad
K_{P,N}(s,n)=n^{-s}\sum_{j\in\operatorname{supp}P}
 P_j\frac{(\log n)^{N+j}}{(N+j)!}.
\]

For squarefree nonprime (n), the original signed coefficient is

\[
C_L(n)=-\frac{\log n}{L}
 \sum_{d\mid n}\mu(d)\max(0,L-\log d).
\]

It is zero on other labels. Let

\[
\mathcal S_N=\{n\in\mathcal B_N:
 n=ap,\ a,p\text{ prime},\ a\le N^2<p\}.
\]

The compiled theorem
[`tendsto_actual_semiprime_integer_band`](../RiemannGaussian/ZetaRieszSemiprimeBand.lean)
proves

\[
u^{N+1}\sum_{n\in\mathcal S_N}
 C_{L_N}(n)K_{P,N}(3/2+i\gamma,n)\longrightarrow0.
\]

It allows every fixed complex polynomial (P) and any varying selection
of the small primes (a\le N^2). It retains the integer floor, all factorial
shifts and the full product phase. The selected prime set need not be fixed
as (N) varies. This does **not** license arbitrary restrictions of a
completed infinite prime sum.

## Why an exposed zero is available

The exact exposure condition is

\[
\tau\ne\rho\quad\Longrightarrow\quad
 |3/2+i\gamma-\tau|>u
\]

for every other actual nontrivial zero (	au).
[`exists_exposed_right_half_zero`](../RiemannGaussian/ZetaExposedZero.lean)
selects such a (ho) from any hypothetical right-half zero, with real
part at least as large. It does not assume a globally rightmost zero or
that a supremum is attained.

A competing zero inside the source disk forces a strictly larger real
part and pays its squared vertical displacement by twice that increase.
An infinite chain would have squared height at most linear in its index,
contradicting the proved inverse-square summability of the actual divisor.
Local finiteness then supplies a slightly larger isolating radius.

The complete canonical divisor, reflected modes, pole and analytic
remainder yield a uniform bound for normalized complete prime moments.
The ordinary-prime and unlogged-prime versions retain genuine convergence
and the order-zero term. See
[`ZetaExposedPrimeMoments`](../RiemannGaussian/ZetaExposedPrimeMoments.lean).

## Estimates and exact transfers

| Component | Checked result | Scope |
| --- | --- | --- |
| Completed prime/cofactor head | (C N^{-(\beta-1/2)}) eventual bound | Exposed zero; arbitrary cofactor selections in ([1,N^2]), fixed filter; constants may depend on the zero and filter. |
| Actual physical semiprime prefix | Explicit allowance tending to zero | Every (0<u<1), no zero premise; arbitrary dominated pair masks. |
| Actual-minus-completed coefficient | Same prefix budget; exactly zero above (X_N) eventually | Both prime logarithms and the physical (1/L_N) are retained; diagonal deletion is checked. |
| Both omitted original-band tails | Vanishing error under the actual divisor majorant | Genuine integer reindexing and series convergence are proved. |
| Integer counting | Exact prime-factor uniqueness | Double-small-prime products lie below the original band eventually; each remaining semiprime counts once. |
| Overlap with earlier deletions | Vanishing physical-prefix error | Above-cutoff semiprimes survive every earlier adaptive cut, with all old interval fallbacks intact. |

The exact normalized physical-prefix allowance is

\[
9\left(\sum_j|P_j|\right)\frac{N}{L_N}
 \left(1+\frac{\log(N^2)}{\log2}\right)
 \left(\frac{u}{N+1}+2u^{N+1}\right).
\]

The actual floor gives (L_N\ge cN) eventually for some (c>0).
Thus this allowance vanishes throughout (0<u<1), including the scalar
contact of the older unrestricted smooth-cofactor estimate. Preserving
both prime logarithms makes the Chebyshev prime-density bound available
before estimating the pair sum.

The completed-head power bound is in
[`ZetaRieszCompletedCofactor`](../RiemannGaussian/ZetaRieszCompletedCofactor.lean).
The exact factorial convolution and complete product-logarithm series are
in [`ZetaPrimeCofactorCompletion`](../RiemannGaussian/ZetaPrimeCofactorCompletion.lean).
The finite-prefix estimates and their limits are in
[`ZetaRieszSemiprimePrefix`](../RiemannGaussian/ZetaRieszSemiprimePrefix.lean) and
[`ZetaRieszSemiprimePrefixDecay`](../RiemannGaussian/ZetaRieszSemiprimePrefixDecay.lean).
The original-band transfer is in
[`ZetaRieszSemiprimeCompletion`](../RiemannGaussian/ZetaRieszSemiprimeCompletion.lean).

## What remains in the full carrier

The new integer support is literally the earlier adaptive support minus
(\mathcal S_N). The overlap proof in
[`ZetaRieszSemiprimeSupport`](../RiemannGaussian/ZetaRieszSemiprimeSupport.lean)
ensures that this subtraction preserves all previous arithmetic bounds.

| Source scale | Remaining nonzero labels |
| --- | --- |
| (1/2<u<\exp(-1/2)) | Eventually every label has at least two distinct primes above (N^2). The small-prime/large-prime semiprime alternative has been removed. |
| (\exp(-1/2)\le u<1) | Small-prime/large-prime semiprimes are still removed, but composite-cofactor classes outside the older proved range remain alongside terms with several large primes. |
| Additional restriction when (2u^2<1) | The complete (N^2)-smooth factor stays below (X_N), with arbitrary rough-prime count. This keeps exactly the earlier range. |

All earlier optimized cofactor restrictions also remain. The
[exact three-layer and boundary-divisor identities](zeta-riesz-extreme-prime-window.md)
remain available on their stated support. Large primes still occur in the
integer, logarithm, phase and factorial kernel even where they disappear
from the divisor profile.

In [`ZetaRieszSemiprimeDeletion`](../RiemannGaussian/ZetaRieszSemiprimeDeletion.lean),
`tendsto_normalizedResidual` proves that the **whole** new normalized
residual tends to (-m_\rho), with actual positive analytic multiplicity.
`tendsto_quadraticResidual_sub_residual` preserves the link to the complete
signed Euler-window representation, including its mixed and boundary terms.

The open arithmetic target is any independent cofinal floor

\[
\operatorname{Re}R_N\ge-c\quad\text{for some }c<1.
\]

`rh_of_exposed_residual_floors` proves that such floors at all exposed
right-half zeros imply Mathlib's `RiemannHypothesis`. The selection and
source steps are proved; the floors are explicit unproved premises.
Decay of a component cannot replace this joint bound.

## Evergreen proof inventory

The supporting explorer endpoint is `semiprime-class-deletion` in
[`docs/rh-proof-explorer/metadata.json`](rh-proof-explorer/metadata.json).
Its source links, theorem statements, dependency edges and transitive axiom
audits are generated from the ordinary compiled library. The default
whole-carrier frontier remains
`ZetaRieszCriticalProfile.exists_original_band_critical_profile`.
The generated [family index](theorem-families/README.md) contains all ten
modules in this slice. Exhaustive numerical certification is unaffected.
