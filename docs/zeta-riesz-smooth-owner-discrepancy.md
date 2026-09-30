# Smooth owner comparison — joint main still open

This local supporting result does **not** meet the current milestone of an
independent bound for the combined real contribution of `J_j+C_j`.
It pays a counting comparison on complete cofactor shells; the signed main
and the other original core sectors remain unbounded.

[Lean source](../RiemannGaussian/ZetaRieszSmoothOwnerDiscrepancy.lean).
The module is not a new public proof endpoint. No zero exclusion is claimed.
Its [local audit](riesz-smooth-owner-discrepancy-audit.json) records a strict
module build, the full root build, declaration lint with the module imported,
and eight terminal axiom checks using only the three standard axioms.

## What is proved

Keep the exact owner factorial weight

```math
a_{N,p}(n)=\left(1-\sum_{k\in\mathrm{unpaidOrders}(N)}
 \operatorname{Bin}_{N+1,k}\!\left(\frac{\log n}{\log p+\log n}\right)\right)
 \frac{e^{-(\log p+\log n)/2}(\log p+\log n)^{N+1}}{N!}.
```

For `N>=32`, its variation on a shell `M<n<=X<=2M` is at most
`3*(N+1)*2^(N+1)`. Squarefreeness stays in the counting measure: the
smooth extension agrees with the original weight on composite squarefree
cofactors but is **not** set to zero on primes or nonsquarefree integers.
The prime-extension correction is therefore retained explicitly.

Let `p` be an eligible prime with `X<p` and `log p<=L`, and put

```math
b_p=L-\log p,\qquad
w_p(n)=\mathbf1_{M<n\le X}\frac{a_{N,p}(n)}n
              \cos\!\bigl(y(\log p+\log n)\bigr).
```

`owner_atom_eq` and `literal_owner_shell_eq` identify the actual owner
atoms with `w_p(n)*R_{b_p}(n)/(L*p)` on this support. This uses saturation
of the **composite** cofactor at `L`; it does not complete a prime sum.

For `0<=u<=10001/20000`, `M>=exp(N/2)`, and an integer cutoff `R>0`
satisfying `R^2<=M`, `floor(exp(b_p))<=R`, and `b_p<=log(R+1)`, define
the already existing signed comparison main

```math
\mathcal M_{N,p}=
\frac{\operatorname{densityRiesz}(b_p)\sum_{n=1}^{X}w_p(n)
      -b_p\sum_{\substack{q\le X\\q\ \mathrm{prime}}}w_p(q)}{Lp}.
```

If `B_{N,p}` denotes the literal owner shell sum, then
`normalized_literal_owner_error` proves

```math
\left|u^{N+1}(B_{N,p}-\mathcal M_{N,p})\right|
 \le \frac{2u\,C\,(6+|y|)(N+1)}p e^{-3N/100}.
```

Here `C=countingConstant` is the existing positive finite squarefree
counting constant. Its numerical value is not evaluated. The cutoff
profile is summed with its Möbius signs before estimating this error.
The ordinary-prime subtraction and the full product phase remain signed.

`normalized_joint_owner_error` sums all selected owner-prime columns first,
with their own shell endpoints and divisor cutoffs. Its error is bounded by

```math
2u\,C\,(6+|y|)(N+1)e^{-3N/100}\sum_{p\in P}\frac1p
 \le 2u\,C\,(6+|y|)(N+1)(1+\log Q)e^{-3N/100}
 \quad(P\subseteq\{p\le Q:p\text{ prime}\}).
```

Thus even an exponential upper prime cutoff does not exhaust this error's
geometric saving. There is no termwise absolute-value replacement of the
signed main in this theorem.

## What is not proved

The bound controls `B-main`, **not** `B` or `main` separately. The selected
resonance can remain in the main. Neither its phase cancellation nor a
one-sided estimate for it follows from this comparison.

The condition `p>whole cofactor` describes only a sector of the actual core.
The other geometries and the inherited prime-count/mask restrictions have
not been removed by this result. It is invalid to replace the whole
`J_j+C_j` by these full shells without an exact, independently paid bridge.
The zero-extension variation obstruction remains valid for that different
extension; the new proof addresses a smooth extension on the stated shells.

The cofinal floor `-79/1000-o(1)`, the cofinal ceiling `3/2+o(1)`, and the
restricted exposed-zero contradiction are all still open. Further work
must bound the remaining **combined signed main**, rather than count this
comparison-error payment as satisfying the user's requested slice.
