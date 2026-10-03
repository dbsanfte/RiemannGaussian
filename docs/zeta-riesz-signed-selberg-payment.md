# Joined Selberg payment on the retained signed boundary

Local Lean slice, 2026-10-03. Under a **simple exposed zero**, the actual
complete-period Selberg prime/pair combination is now proved to tend to zero.
Its completion error has an independent geometric bound. The remaining
masked signed pair defect is **unbounded by this slice**; the floor, multiple-zero
ceiling and zero exclusion remain open.

The leaf is [ZetaRieszSignedSelbergPayment.lean](../RiemannGaussian/ZetaRieszSignedSelbergPayment.lean).
It was locally validated in the slice and is now registered in the ordinary
root and public status/explorer by the combined checkpoint. All preceding
payments and negative audits remain intact.

## What is now estimated

Write `b_N = joinedCoefficient u N` and retain the exact support

\[
\mathcal S_N=\operatorname{completePeriodLabels}
 (\operatorname{joinedLabels}(u,N),N,y).
\]

The original four signed coefficients have already been joined on each
label. The current ordinary-prime coefficient is exactly `-log p`; the
original head, unallocated correction and sieve/allocation masks are still
part of `b_N` on distinct-prime products.

The classical Selberg coefficient on this population is

\[
b_{\rm Sel}(p)=-\log p,
\qquad
b_{\rm Sel}(pq)=-\frac{2\log p\log q}{\log(pq)}.
\]

The new estimated subexpression is

\[
S_N=u^{N+1}\sum_{n\in\mathcal S_N}
 b_{\rm Sel}(n)K_N(3/2+iy,n).
\]

`norm_literalSelberg_le` bounds `S_(N+1)` by an explicit budget:

\[
\begin{aligned}
\|S_{N+1}\|\le{}&
 |a_{N+1}+1|
 +\frac{2C}{N+1}\sum_{k=0}^N|a_k+1|\\
 &+\left(\frac{4u}{3}\right)^{N+1}\frac{uM_{\square}}2
 +r_{\rm edge}^{N+1}C_{\rm edge},
\end{aligned}
\]

where

\[
a_k=u^{k+1}\sum_p(\log p)K_k(3/2+iy,p),
\quad |a_k|\le C,\quad C\ge1,
\]

and `M_square` is the convergent existing prime-square logarithmic Euler
majorant. The last two rates are strictly below one in the current radius
regime. Constants may depend on the selected zero; no starting order or
height-uniform bound is evaluated.

For a simple exposed zero, the existing complete ordinary-prime phase theorem
gives `a_k -> -1`. Cesaro convergence therefore pays the first two terms,
**including orders zero and one**. `tendsto_literalSelberg_simple` proves
`S_N -> 0` on the literal support, and `selbergBudget_tendsto_simple` proves
that the displayed explicit budget vanishes.

## Why the literal support transfer is valid

`finiteSelberg_eq` first proves the exact finite identity for a prime prefix
`A`, with every complementary factorial order and the repeated-prime
diagonal retained:

\[
\begin{aligned}
&\sum_{p\in A}b_{\rm Sel}(p)K_{N+1}(s,p)
 +\sum_{p<q\in A}b_{\rm Sel}(pq)K_{N+1}(s,pq)\\
&\quad=-F_A(N+1,s)
 -\frac{\sum_{k=0}^NF_A(k,s)F_A(N-k,s)-D_A(N,s)}{N+1}.
\end{aligned}
\]

Here `F_A` is the logged finite prime moment and
`D_A = sum_(p in A) (log p)^2 K_N(s,p^2)`. Its quotient is exactly one half
of the logged square moment at order `N+1`; no diagonal is silently deleted.

`exists_literalSelberg_completion_bound` then reuses the checked uniform
radial-edge estimate on the difference between that finite prefix and the
**same original** complete-period support. Every ordinary-prime or distinct-pair
label strictly inside the contracted radial window is already in `joinedLabels`.
All missing labels therefore lie on paid radial/partial-period edges.
On this population `|b_Sel(n)| <= log n`, so the existing divisor-log majorant
applies. A single fixed geometric constant pays this support difference.
Ordinary-prime summability and the square majorant justify passing the
exhaustive prefix to the limit.

No hard-share mask is transported by separate complete-leg convergence.
Only the auxiliary Selberg subexpression is completed; every owner/share
restriction remains in the **literal signed defect**. This does not revive
the earlier invalid masked phase transfer or bare cofactor completion.

## What remains, exactly

Define the same-support difference

\[
D_N=u^{N+1}\sum_{n\in\mathcal S_N}
 [b_N(n)-b_{\rm Sel}(n)]K_N(3/2+iy,n).
\]

`literalPairDefect_eq_nonprime` proves that every ordinary-prime summand is
zero. Only genuine squarefree distinct-prime products survive, retaining
**all** original coefficient masks and the full phase.

`lowCountPeriods_eq` gives the exact ledger

\[
\operatorname{lowCountPeriods}_j=\Re S_{N_j}+\Re D_{N_j}.
\]

`exists_native_pairDefect_payment_simple` spends the displayed Selberg cost
in the original native ledger:

\[
\Re(\operatorname{nativeScaledCore}_j)
 \ge-\Re D_{N_j}-E_j,\qquad E_j\to0.
\]

The new `E_j` combines the previous independent payments with the centered
Selberg convolution budget once. The cancellation part of this payment
**uses exposure and simplicity**; it is not a hypothesis-free arithmetic
floor. The exact remaining target is a genuinely independent, cofinal

\[
\boxed{\Re D_{N_j}\le399/5000+o(1).}
\]

The earlier proved absolute defect allowance still diverges. There is no
positive-period sum, defect norm allowance or countwise credit in the new
ledger. Multiple zeros still require the separate existing ceiling campaign.

## Numerical calibration: keep the moving radial saddle

The optional `scripts/probe_riesz_native_selberg_profile.py` is a
**pure selected simple-zero channel model**, not an actual-prime enumeration,
prime-density transport, interval certificate or arithmetic bound. It
retains the finite binomial allocation, actual floor-length error enclosure,
head/correction conditions and complete-period endpoints. It integrates

\[
u^{N+1}e^{-uT}\frac{T^N}{N!}
\]

rather than freezing `T=2N`. The relevant asymptotic saddle is `T=N/u`, so
`L_N/T -> -2u log u`. Freezing `T=2N` instead gives `-log u` and reverses the
comparison with the target at `u=10001/20000`:

| Model | Limiting signed value |
| --- | ---: |
| Forbidden frozen `2N` slice | 0.07974183525 |
| Moving radial saddle / already-proved source | 0.07987179703 |
| Independent target | 0.07980000000 |

This is a probe calibration, not a correction to any Lean theorem. The
existing Lean source constant was already correctly normalized.

The native model displays delayed imbalance:

| Native order | Model joined channel |
| --- | ---: |
| 90,112 | 0.07961576218 |
| 196,608 | 0.07974750997 |
| 425,984 | 0.07981103255 |
| 917,504 | 0.07984201740 |
| 4,194,304 | 0.07986460335 |

The 64/96 quadrature comparison differs by less than `1e-14` on the checked
large orders; the height-100 control differs by less than `3e-15`. These are
floating-point regressions, not rigorous error bounds. Old intermediate
reports with the frozen source header are excluded from final evidence.

In the limiting coefficient-only profile, for the smaller share `q` and
`lambda=-2u log u`, the defect divided by total log is

\[
\begin{cases}
q(2(1-q)-1/\lambda),&q\le13/32,\\
2q(1-q)-(1/\lambda-1),&q>13/32.
\end{cases}
\]

It changes sign at approximately `q=0.27862054` and at the allocation
transition `13/32`. The model's low/middle/high signed integrals are about
`+0.08605`, `-0.02566`, `+0.01948`. Their net is the **existing** source
`0.07987179703`, not a new estimate or separately spendable credits.

The next arithmetic task is cancellation in this literal weighted pair
profile across its actual share and total-log periods. Nothing in this
slice supplies the missing independent `399/5000` bound.
