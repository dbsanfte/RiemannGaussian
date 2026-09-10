# Signed divisor cancellation inside the Fourier carrier

Lean now removes complete mixed-prime divisor fibres from the actual
Möbius coefficient before taking an absolute value. It also evaluates the
surviving two-prime boundary, including a middle range whose magnitude is
independent of the ambient product. These are finite arithmetic identities
and bounds. They do not prove the independent source-beating inequality or
exclude an additional zeta zero.

## The coefficient and its exact cancellation

Keep the existing literal coefficient

\[
c_D(m)=\sum_{ab=m,\ a>D}\mu(a)\log b.
\]

For coprime positive integers `P,n`, define the signed fibre

\[
F_{D,P,n}(d)=\sum_{a\mid P,\ ad>D}
 \mu(a)\bigl(\log(Pn)-\log(ad)\bigr).
\]

Lean proves, with the strict cutoff unchanged,

\[
c_D(Pn)=\sum_{d\mid n}\mu(d)F_{D,P,n}(d).
\]

A fully retained fibre, `d>D`, is evaluated exactly:

\[
F_{D,P,n}(d)=
\mathbf1_{P=1}\bigl(\log(Pn)-\log d\bigr)+\Lambda(P).
\]

Thus when `P>1` is not a prime power, that entire fibre is zero. A fibre
with `Pd<=D` is empty. The actual coefficient becomes

\[
c_D(Pn)=
\sum_{\substack{d\mid n\\d\le D<Pd}}
 \mu(d)F_{D,P,n}(d).
\]

The cancellation uses the classical complete identities for `sum mu` and
`mu * log`. No claim of historical novelty is made for those identities.
The new repository interface applies their cancellation at the cutoff
inside the current arithmetic carrier.

Compiled entry points in
[ZetaMoebiusDivisorBoundary.lean](../RiemannGaussian/ZetaMoebiusDivisorBoundary.lean):

- `sum_moebius_log_affine`
- `zetaMoebiusLogTailCoefficient_eq_fibres`
- `zetaMoebiusLogDivisorFibre_complete`
- `zetaMoebiusLogTailCoefficient_eq_boundary`

## An independent boundary bound

Write `B={d | n : d<=D<Pd}` and let `tau(P)` be the number of divisors
of `P`. After the cancellation, Lean proves

\[
|c_D(Pn)|\le |B|\,\tau(P)\log(Pn).
\]

If `B` is empty, the actual coefficient is exactly zero. No contribution
from the cancelled complete fibres is charged to this bound. This can
improve the finite allowance when the annulus has few divisors; no uniform
improvement in its growth exponent is established.

The compiled theorems are
`norm_zetaMoebiusLogTailCoefficient_le_boundary` and
`zetaMoebiusLogTailCoefficient_eq_zero_of_boundary_empty` in the same module.

## The surviving two-prime sign profile

For distinct primes `p<q`, take `P=pq` and `d|n` with `gcd(pq,n)=1`.
The exact four-term profile gives:

| Cutoff position | Signed fibre before multiplying by `mu(d)` |
| --- | --- |
| `pqd<=D` | `0` |
| `qd<=D<pqd` | `log(n/d)` |
| `pd<=D<qd` | `-log p` |
| `d<=D<pd` | `-log(pqn/d)` |
| `D<d` | `0` |

All endpoints are retained. In the middle range the large product
logarithm cancels completely, so the fibre norm is exactly `log p`.
The outer factor `mu(d)` is still signed; the table does not assert the
sign of the sum over different `d`.

There is also a checked limitation: for `1<=D<p,q`,

\[
c_D(pq)=-\log(pq).
\]

Consequently the remaining boundary contains nonzero negative arithmetic
terms. Complete-fibre cancellation alone does not remove it.

Compiled entry points in
[ZetaMoebiusPrimeFibre.lean](../RiemannGaussian/ZetaMoebiusPrimeFibre.lean):

- `zetaMoebiusLogDivisorFibre_two_primes`
- `zetaMoebiusLogDivisorFibre_middle`
- `norm_zetaMoebiusLogDivisorFibre_middle`
- `zetaMoebiusLogDivisorFibre_inner`
- `zetaMoebiusLogDivisorFibre_outer`
- `zetaMoebiusLogTailCoefficient_rough_semiprime`

## Transport through all complex weights and Fourier products

The cancellation holds for every finite complex weight family. For a
chosen eligible factor `P`, the sum splits into the boundary formula on
products `m` satisfying `P|m` and `gcd(P,m/P)=1`, plus the original sum
on all complementary products. The complement is not discarded.

The full centered Fourier interaction is also reconstructed exactly as

\[
C_N=\sum_{n\in B_N}c_D(n)W_N(n),\qquad
W_N(n)=n^{-5/4}\frac1{q_N}
 \sum_{k\in S_N}(\chi(k)^n-1)\widehat f_N(k).
\]

Here `B_N`, `q_N`, the quarter-line kernel `f_N`, and `S_N` are the existing
finite-band objects. The identity is proved for every polynomial, every
divisor cutoff, every ordinate, and every frequency subset. The sum over
frequencies remains complex inside `W_N`; its terms are not replaced by
their individual magnitudes.

Applying the divisor identity to this weight gives the exact full carrier
as boundary fibres plus complementary products. In particular, the
physical reconstruction retains the already proved selected-zero limit

\[
u^{N+1}C_N\longrightarrow-m_\rho,\qquad u=3/2-\Re\rho.
\]

Compiled entry points in
[ZetaMoebiusDivisorFourier.lean](../RiemannGaussian/ZetaMoebiusDivisorFourier.lean):

- `sum_zetaMoebiusLogTailCoefficient_eq_boundary_add_compl`
- `zetaMoebiusCenteredFourierPart_eq_physical`
- `zetaMoebiusCenteredFourierPart_eq_boundary_add_compl`
- `tendsto_zetaRightHalfMoebius_centered_physical`

## The finite-prefix test now gives actual sector decay

The proposed analytic test has been completed and strengthened. Lean now
proves both finite-prefix convolutions, genuine convergence, the complete
coprime Euler response, and an independent source-normalized bound for
moving coprime factor sectors with `P_N^2<=D_N`.

A second exact identity groups all multiples of `P` using the least common
multiple with each retained head divisor. Preserving the physical Dirichlet
weight until after estimating its logarithm removes the factor-size cost.
The entire actual multiple sector now has a uniform source-normalized
geometric bound, even for arbitrarily growing mixed-prime factors. Moving
finite complex families with total absolute weight at most `D_N` also decay.

See [the exact responses, checked decay theorems, and remaining gap](zeta-moebius-factor-decay.md).
The literal complement retains the full negative multiplicity source. The
global goal still requires an independent signed inequality for that
remaining arithmetic; neither a new zero exclusion nor RH follows.
