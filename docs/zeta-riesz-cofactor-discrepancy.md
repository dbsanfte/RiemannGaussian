# A power estimate for the signed cofactor counting error

[The Lean proof](../RiemannGaussian/ZetaRieszCofactorDiscrepancy.lean)
uses the repository's proved squarefree counting error. Ordinary primes
are retained as an exact signed subtraction, not replaced by a density.
The [audit](riesz-cofactor-discrepancy-audit.json) records validation.

For the existing sharp divisor prefix, put

```math
M_D(n)=\sum_{d\mid n,\ d\le D}\mu(d),\qquad
c_D=\sum_{d\le D}\mu(d)\,\operatorname{density}(\operatorname{primeFactors}(d)).
```

Here `density` is the canonical limit of the actual finite square sieve.
The constant `countingConstant` is a positive finite defining series,
independent of both cutoffs; it has not been numerically evaluated.
`sharp_count_error` and `sharp_count_error_short` prove

```math
\left|\sum_{n\le X}\mathbf1_{\mathrm{squarefree}}(n)M_D(n)-c_DX\right|
 \le C X^{3/4}D^{3/8}
 \le C X^{15/16}\quad(D^2\le X,\ D,X>0).
```

This is an elementary squarefree counting power saving. It is not a
prime-number-theorem approximation, and it does not assert decay of `c_D`.

The subsequent [signed-main theorem](zeta-riesz-signed-density-main.md)
now bounds the original comparison main explicitly after retaining cutoff
cancellation. Its remaining source factor grows as `(2u)^N`; it does not
pay this module's full literal variation/long-cutoff error or close either
cofinal endgame bound.

## Exact prime subtraction and product phase

For any real weight `w`, `composite_model` retains the signed expression

```math
\mathcal M_D(w)=c_D\sum_{n=1}^Xw(n)-w(1)
                    -\sum_{D<p\le X}w(p).
```

The difference between this expression and the weighted sharp prefix over
squarefree composite cofactors is exactly the centered squarefree counting
error. No unit or ordinary-prime cofactor is silently discarded.

`shell_composite_error` proves a concrete estimate when
`0<M<X<=2M`, `D>0`, `D^2<=M`, and `M>=exp(N/2)`. Set

```math
w(n)=\mathbf1_{M<n\le X}\frac{a(n)}n
                         \cos\bigl(y(c+\log n)\bigr),\qquad |a(n)|\le A.
```

Then

```math
\left|\sum_{\substack{1<n\le X\\n\ \mathrm{squarefree\ composite}}}
                 w(n)M_D(n)-\mathcal M_D(w)\right|
 \le C e^{-N/32}
 \left((3+|y|)A+\sum_{k=M+1}^{X-1}|a(k)-a(k+1)|\right).
```

Both exterior jumps are paid. The product phase stays inside the signed
main expression. Extra allocation and mask variation remain in `a`; they
are not asserted bounded by a constant. The general `weighted_error` also
retains every arbitrary mask jump explicitly.

`profile_error_exponential` recombines every cutoff using the original
signed profile increments before taking the error norm. Its main term is
`sum_D (f(D)-f(D+1))*M_D(w)`, not the sum of absolute main terms.
The scalar theorem `source_rate_bound` proves, for `0<=u<=10001/20000`,

```math
(2u)^N e^{-N/32}\le e^{-3N/100}.
```

Thus this counting error has ample exponential margin **if the displayed
amplitude/profile variation is controlled**. This does not pay the original
whole-core mask variation, all divisor ranges, or the signed main expression.

## Numerical check and next target

The optional [probe](../scripts/probe_riesz_cofactor_main.py) enumerates
actual squarefree integers and ordinary primes in three order-16 columns.
These columns lie inside a nonempty original physical annulus, unlike the
earlier order-6/8/10 enlarged-population tests. They retain the exact owner
allocation and product phase. They omit nonowner allocation and do not
verify all earlier nested core masks. The probe is outside CI.

At height 54 its signed main terms are approximately `2.70e-11`, `-3.31e-12`
and `-2.08e-12`, with counting discrepancies of order `1e-14` or smaller.
These are **individual columns**, not a joint whole-carrier bound, a
certificate, or an asymptotic result. They show why estimating only the
counting error leaves the observed signed signal largely untouched.

A subsequent [joint probe](../scripts/probe_riesz_joint_main.py) sums **all**
marked-prime columns in this selected owner sector before taking its real
part. Its [recorded results](riesz-joint-main-probe.json) at height 54 are:

| Order | Marked primes | Signed main | Sum of absolute column mains |
| ---: | ---: | ---: | ---: |
| 14 | 15,218 | -9.36612e-7 | 1.01121e-6 |
| 16 | 480,399 | -2.49291e-6 | 8.26543e-6 |
| 18 | 7,507,215 | 7.98299e-6 | 1.67126e-5 |

The corresponding signed counting discrepancies are about `1.55e-10`,
`-3.02e-11` and `1.07e-10`. The main expression has changed sign and its
absolute size has not decreased across these orders. This is **not evidence
of the required asymptotic saving**. The small-order moving lengths allow
only divisor cutoffs 1, 2 and 3; they do not test the exponentially growing
cutoffs of the endgame. All earlier mask limitations still apply.

The user-directed next slice must bound the **signed main expression**,
retaining its density/prime cancellation and the correlated original
weights. No further error-only estimate counts as completing that target.
The whole cofinal `-79/1000` floor, `3/2` ceiling and RH remain open.

The subsequent [literal variation audit](zeta-riesz-signed-density-main.md#audit-of-the-literal-mask-variation) quantifies why the canonical zero
extension cannot be treated as a smooth amplitude here: on support
`n>=exp(N/2)`, the displayed `exp(-N/32)` weighted-variation allowance is
at least `exp(15N/32)/3` times the absolute column mass. This is a lower
bound for the allowance, not the actual signed discrepancy. A changed
extension needs its own exact comparison ledger and variation estimate.

## Checked extension audit

The actual `ownerRows B` have squarefree composite cofactors only.
`literal_compositeModel` now proves that, for their canonical zero-extended
`maskedWeight`, the unit and prime terms in the displayed model are zero.
The model is then simply `c_D * sum w`. A nonzero virtual prime subtraction
requires a different extension to ineligible cofactors. Such an extension
can be valid, but agreement on the composite support and the resulting
counting error must both be controlled.

The effect of changing an extension is quantified exactly. If `q` is prime
and `D<q<=X`, changing `w(q)` to `w(q)+a` leaves the composite correlation
unchanged, while `compositeModel_prime_extension` gives

```math
\mathcal M_D(w+a\mathbf1_{\{q\}})-\mathcal M_D(w)=(c_D-1)a.
```

`comparison_error_prime_extension` proves that the comparison error changes
by the opposite amount, with exact magnitude `|c_D-1|*|a|`. A cancellation
created by an unpriced extension cannot count as a gain in the actual sum.
These theorems audit the interface; **they do not bound the signed main**.

The [boundary investigation](riesz-signed-main-boundary-investigation.md)
also shows why the small-order numerical signal cannot certify this missing
bound. Its extra `p>whole cofactor` restriction introduces a sector boundary
that is absent from the complete carrier. Future estimates must use a fixed,
explicit extension agreeing on every eligible composite, or work directly
with the original signed correlations.

## Signed profile factorisation

`literal_profile_factorization` now factors any common cutoff profile into
one signed density scalar times the signed canonical weight sum. The weight
is independent of the divisor cutoff. `literal_profile_error_exponential`
combines this with the existing `exp(-N/32)` comparison bound, retaining its
weighted variation, both endpoint conditions and every short/lower-cutoff
premise. It does not prove that those costs are small for the literal masks.
The [exposed-mode slice](zeta-exposed-moving-modes.md) separately gives a
geometric competing-mode bound. Connecting the masked weight sum to that
expansion with a polynomial coefficient budget remains open.
