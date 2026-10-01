# A global payment on the surviving hinge population

`ZetaRieszHingeAllocationPayment` proves a geometric allocation payment
inside the current central signed carrier. This removes the owner-allocation
factor on the genuine failed-gap hinge population with one independent error.
The unallocated signed hinge sum, whole `-79/1000` floor, ceiling and restricted
zero exclusion remain **open**.

The [Lean proof](../RiemannGaussian/ZetaRieszHingeAllocationPayment.lean) has
19 public theorems. The [proof audit](riesz-hinge-allocation-audit.json) records
their transitive axioms, source hashes and focused validation. The optional
[numerical regression](../scripts/probe_riesz_hinge_allocation.py) retains the
actual dyadic schedule and original core masks. It is outside builds and CI.

For an original squarefree label `n`, put `p = largestPrime n`, `a = n/p`.
On the current core, `1.97N < log n <= 2.03N`. A based cofactor `B = a/e`
on a genuine cofactor hinge satisfies `log B >= L`. Failure of the old
whole-window owner gap means

```math
2\log p+\log B\le\frac{203}{100}N.
```

The actual moving Riesz length eventually obeys `L >= 11N/8` throughout
the working radius range. Hence

```math
\log p\le\frac{131}{400}N,
\qquad \log q\le\log p<\frac16\log n
\quad(q\mid n\text{ prime}).
```

The theorem states the non-strict one-sixth bound. The arithmetic also gives
`omega(n) >= 7`: six primes bounded by `131N/400` would give total log at most
`1.965N`, outside the current central window. This is a property of the
**original label**, not its based quotient. It supplies no additional credit
from previously paid low-count populations.

`hingeLabels` is a finite subset of the existing physical core labels with
the displayed witness. It preserves the original radial/count/physical
conditions. A selected divisor mask may be any subset of the original
`a.divisorsAntidiagonal`, including the current complement of both affine
zero selectors. The selected label set and phase height may move with order.

The original allocation is a binomial sum over the unchanged `unpaidOrders`.
Their upper endpoint is `13N/32`. The cofactor binomial parameter is at least
`5/6`. Tilt by `1/2` and use

```math
\log\frac7{12}+\frac{13}{32}\log2\le-\frac18.
```

This proves the complete original owner share is at most `exp(-N/8)`.
No factorial orders are discarded, and no prime-phase approximation is used.
Because only one owner is selected, there is no prime-count multiplier.

For any selected original divisor set `D`, write its **signed** response as

```math
H_D(p,a)=\sum_{(d,b)\in D}\mu(b)
 \bigl[(\log p+\log b-L)_+-(\log b-L)_+\bigr].
```

The exact allocated-minus-unallocated coefficient is

```math
-\theta_{A\cap\{p\}}(n)\frac{\log n}{L}H_D(p,a).
```

Only this exponentially suppressed allocation correction is norm-paid.
The existing original-label partial-incidence majorant controls `H_D` for
that error. It is not used as a bound for the retained main response.

After the full summable arithmetic moment is included, one global bound is

```math
\left\|u^{N+1}\sum_{n\in S} w_n
 \bigl(c^{\rm owner}_{N,D}(n)-c^{\rm unallocated}_{N,D}(n)\bigr)
 K_N\!\left(\frac32+iy,n\right)\right\|
\le\frac{503}{500}\mathcal M\,r^N,
\qquad r<\frac9{10},
```

where `S` is any subset of `hingeLabels`, `||w_n|| <= 1`,
`M = zetaMoebiusLogMajorantMass (2049/2048)` is the existing fixed convergent
mass, and

```math
r=\frac{503}{1000}\frac{2048}{1023}e^{-1/8}.
```

The height, number of labels, divisor selections and original count ceiling
do not enter the bound. Numerically `r` is about `0.88866`; Lean proves the
rational upper bound. The constant `M` has not been evaluated, so the numeric
rates reported **per unit of M** are not effective floor certificates.

`retained_hinge_allocation_bound` applies the payment to the current literal
antidiagonal after both affine zero deletions.
`central_hinge_allocation_bound` removes this allocation only on the selected
hinge labels inside the whole central main.
`polynomial_remaining_hinge_allocation_bounds` gives the resulting two-sided
inequality directly for `polynomialCentralRemaining`. Large-owner, owner-gap
and polynomial-cutoff credits are unchanged and subtracted once. There is no
new scalar carrier and no estimate of either full hinge separately.

The remaining phase weight on selected labels is exactly

```math
\frac{\log n}{L}K_N\!\left(\frac32+iy,n\right).
```

Thus the signed prime moments no longer have the owner binomial allocation
on this population. This is useful for the next joint constant/log-moment
estimate; it is not that estimate. The cofactor-dependent prime holes and
both actual Riesz hinges remain. The previous
[hinge-pair cancellation](zeta-riesz-hinge-pair.md) remains available, including
its counterexample to dropping the other hinge or extending a narrow masked
prime-shift pairing without its exterior boundary.

The regression tests the original binomial sum at the worst allowed cofactor
share and revisits the original rough close-owner labels at `(N,K)=(640,16)`
and `(1536,32)`. The former does not satisfy the sufficient length lower bound;
its directly checked one-sixth share still permits the pointwise binomial
estimate. The latter satisfies all geometric prerequisites. Source amplitude
underflow is never used as cancellation evidence. These are diagnostics,
not a bound on the remaining signed population or a certified floor margin.

The focused warning-as-error module build, ordinary-root-plus-module namespace
lint, and all 19 public transitive axiom checks pass. Only `propext`,
`Classical.choice` and `Quot.sound` occur. Wider publication checks are deferred;
the slice is local and unpublished, and the README/public endpoint is unchanged.
