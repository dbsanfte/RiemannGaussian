# A narrower signed cosine carrier with bounded outer tails

Lean removes both outer pieces of the actual remaining arithmetic
carrier, leaving

```math
\frac{2N}{5}\lt \log n\le 8N\log 2.
```

The original outer window was $N\log(2)/4\lt \log n\le32N\log2$.
Every earlier arithmetic support deletion is retained. Independently,
exposed-zero selection allows the constant filter $P=1$ to preserve the
full negative multiplicity source. The resulting real target is an exact
signed cosine sum, with no zero-isolating polynomial.

The independent lower floor for the **whole remaining sum is open**.
This slice supplies component bounds and a simpler source-preserving
target, not RH, a new zero-free region or a numerical zero bound.
No historical novelty is claimed for the exponential-tilt argument.

## Actual coefficient, cutoff and remaining sum

For a hypothetical exposed zero $\rho=\beta+i\gamma$, put

```math
u=\frac32-\beta,\qquad
D_N=\left\lfloor\frac{u^{-N}}{N+1}\right\rfloor,\qquad
X_N=(D_N+2)^2,\qquad L_N=\log X_N.
```

Here $1/2\lt u\lt 1$. For squarefree nonprime labels the actual coefficient is

```math
C_L(n)=-\frac{\log n}{L}
 \sum_{d\mid n}\mu(d)\max(0,L-\log d);
```

it is zero otherwise. Let $\mathcal R_N$ denote the previous
[semiprime-free residual](zeta-riesz-semiprime-deletion.md), including
all its earlier adaptive restrictions. Define

```math
\mathcal T_N=\mathcal R_N\cap\{n:2N/5\lt \log n\le8N\log2\}.
```

[ZetaRieszNarrowCarrier.re_normalizedResidual_eq_cosine_sum](../RiemannGaussian/ZetaRieszNarrowCarrier.lean)
proves the exact real identity

```math
\operatorname{Re}R_N=
u^{N+1}\sum_{n\in\mathcal T_N}
C_{L_N}(n)\,
\frac{e^{-3\log n/2}(\log n)^N}{N!}\,
\cos(\gamma\log n).
```

The factorial amplitude is nonnegative. The arithmetic coefficient's sign,
product phase, actual integer floor and common physical length remain.

## The two independent arithmetic bounds

Write $M(n)$ for the original divisor-logarithm majorant and

```math
\mathcal M_\sigma=\sum_{n\ge1}M(n)n^{-\sigma},\qquad
A(P,q,\sigma)=\mathcal M_\sigma\sum_j|P_j|q^{-j}.
```

The imported arithmetic theory proves genuine convergence for every
$\sigma>1$. The fixed polynomial $P$ may be arbitrary.
For the **actual difference** $E_{P,N}$ between the old and narrowed
residual responses, Lean proves

```math
|u^{N+1}E_{P,N}|
\le u^{N+1}\left[
r_-^N A(P,2,17/16)+r_+^N A(P,1/5,121/120)\right],
```

where

```math
r_-=\frac12e^{5/8}\lt 1,\qquad
r_+=5e^{-(7/3)\log2}\lt 1,\qquad r_+^3=\frac{125}{128}.
```

The upper rate is certified by an exact rational cube. The lower kernel
range reuses the repository's existing Chernoff machinery.
[norm_normalized_residual_sub_narrow](../RiemannGaussian/ZetaRieszNarrowCarrier.lean)
retains the physical floor and source factor.
The theorem tendsto_actual_residual_sub_narrow proves this error tends
to zero for every $0\lt u\lt 1$, **without a zero assumption**.
The unnormalized two-rate bound is uniform in the ordinate and every
positive physical length; the constants depend on the fixed filter.
These constants have not been numerically evaluated.

[ZetaArithmeticLogWindow](../RiemannGaussian/ZetaArithmeticLogWindow.lean)
allows arbitrary finite support masks and coefficient families varying
with $N$, provided they retain the actual divisor majorant. Its general
source-adapted tilt criterion remains available for further windows.
The exact signed partition precedes the norm estimate; the inside sum
stays coupled.

## Why the full source survives

At an exposed zero every other actual nontrivial zero is strictly farther
from $3/2+i\gamma$ than $u$. A fixed polynomial vanishing at the selected
source therefore has vanishing normalized complete prime response.
The proof retains all canonical zero modes, the pole, reflected modes
and analytic remainder. Comparing the original isolating filter with
the constant polynomial one preserves its selected value and source.
See [ZetaExposedPrimeFilter](../RiemannGaussian/ZetaExposedPrimeFilter.lean).

[ZetaRieszUnfilteredSource](../RiemannGaussian/ZetaRieszUnfilteredSource.lean)
pays the complete prime-to-arithmetic transport, including proper prime
powers, the physical Vaughan average and original band errors.
Prior component deletions hold for every fixed filter, so they apply
to one. Finally,
[ZetaRieszNarrowCarrier.tendsto_normalizedResidual](../RiemannGaussian/ZetaRieszNarrowCarrier.lean)
proves

```math
R_N\longrightarrow-m_\rho,\qquad m_\rho\ge1.
```

The new outer-tail deletions spend no source margin. This source limit
assumes the hypothetical exposed zero; it is not an independent
arithmetic lower bound.

## What remains to bound

| Component | Status in the narrowed window |
| --- | --- |
| Both new outer logarithmic pieces | Independently bounded by the geometric allowance above. |
| Earlier smooth, cofactor and semiprime deletions | Retained exactly, with their original parameter ranges. |
| Products containing several primes above $N^2$ | Their full coupled signed contribution is unpaid. On $1/2\lt u\lt e^{-1/2}$, every nonzero survivor eventually has at least two such primes. |
| Composite-cofactor fallback cases | Still present outside the earlier complete-composite range; narrowing does not extend that range. |
| Complete smooth factor | Still below $X_N$ where $2u^2\lt 1$; this restriction is not extended to all source scales. |

The [three prime layers and signed boundary-divisor identities](zeta-riesz-extreme-prime-window.md)
remain available on their original support. A large prime can disappear
from the divisor profile while still occurring in $n$, its logarithm
and its cosine phase.

Any independent cofinal floor $\operatorname{Re}R_N\ge-c$ with $c\lt 1$
suffices. The theorem rh_of_exposed_narrow_floors proves that such floors
at exposed right-half zeros imply Mathlib's RiemannHypothesis.
Selection, source, deletion and the final contradiction are checked;
the whole-sum arithmetic floors remain explicit open premises.

## Explorer and audit

The [narrowed carrier explorer](https://dbsanfte.github.io/RiemannGaussian/rh-proof/#endpoint=unfiltered-narrow-carrier)
uses compiled theorem statements, source lines, dependency paths and
transitive axiom audits from the ordinary root. Metadata lives in
[rh-proof-explorer/metadata.json](rh-proof-explorer/metadata.json).
The default whole-carrier frontier remains the theorem
ZetaRieszCriticalProfile.exists_original_band_critical_profile.
The five modules appear in the generated [family index](theorem-families/README.md).
No exhaustive numerical-certificate computation is part of this slice.
