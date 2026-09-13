# The original linear source on the integer lattice

Lean now transports the original signed Chebyshev carrier to a complete
prime-versus-integer sum. Its sampling error is independently geometrically
small, and the same hypothetical zero's negative multiplicity survives.
The independent signed lower bound remains open. No new zero-free region,
RH proof or historical novelty is claimed.

All declarations below have prefix `RiemannGaussian.PrimeLatticeCarrier.`
and are compiled in
[ZetaPrimeLatticeCarrier](../RiemannGaussian/ZetaPrimeLatticeCarrier.lean),
in the **Euler & prime structure** family.

## The linear arithmetic target

Keep the existing factorial filter and the original expanding band:

```math
K_{p,N}(s,x)=x^{-s}\sum_kp_k\frac{(\log x)^{N+k}}{(N+k)!},
\qquad s=3/2+i\gamma,
```

```math
A_N=\exp(N\log(2)/4),\qquad B_N=2^{32N}.
```

Let `lambda(n)=log(n)` for ordinary primes and zero otherwise. The new
literal finite carrier is

```math
L_{p,N}(\gamma)=\sum_{\lfloor A_N\rfloor<n\le B_N}
 (\lambda(n)-1)K_{p,N}(3/2+i\gamma,n).
```

Every composite has coefficient minus one. Every prime has coefficient
`log(n)-1`; proper prime powers remain in the composite part. Nothing is
selected by the sign of a phase. `centered_eq_prime_sub_lattice` identifies
this with the unchanged ordinary-prime band minus the entire integer
background on exactly the same endpoints.

For the actual integer discrepancy `d_n=n-theta(n)`,
`centered_eq_error_increments` also proves

```math
L_{p,N}(\gamma)
=-\sum_{\lfloor A_N\rfloor<n\le B_N}
 K_{p,N}(3/2+i\gamma,n)(d_n-d_{n-1}).
```

This is linear in the error increments. The separate
[prime-discrepancy work](zeta-prime-discrepancy-work.md) multiplies those
increments by a preceding discrepancy and is quadratic; its diagonal
decay does not automatically bound this carrier.

## Exact sampling before estimating

Define the upper sawtooth

```math
v(x)=\lfloor x\rfloor+1-x,\qquad 0<v(x)\le1\quad(x\ge0).
```

At an integer, this convention gives one. Its endpoint values are retained.
For every positive ordered interval, every complex `s` and every polynomial,
`lattice_sub_integral` proves

```math
\sum_{\lfloor a\rfloor<n\le\lfloor b\rfloor}K_{p,N}(s,n)
-\int_a^bK_{p,N}(s,x)\,dx
=K_{p,N}(s,b)v(b)-K_{p,N}(s,a)v(a)
-\int_a^bK'_{p,N}(s,x)v(x)\,dx.
```

The proof uses exact Abel summation. Genuine integrability of the
discontinuous sawtooth pairing is proved by `integrableOn_deriv_mul_saw`.
No endpoint rounding or unit-cell term is omitted.

## An independent geometric error bound

Put

```math
P(p)=\sum_k|p_k|(4/5)^k,\qquad
C(p,y)=\bigl(2+4(5/4+|3/2+i y|)\bigr)P(p).
```

The exact lowering identity, with the whole complex multiplier retained,
is proved in `deriv_kernel_eq_shift`. At `Re(s)=3/2`,
`norm_deriv_kernel_le` gives for `N>=1`, `x>=1`,

```math
|K'_{p,N}(s,x)|\le(5/4+|s|)(4/5)^N P(p)x^{-5/4}.
```

The integrable spatial envelope has total mass four on `[1,infinity)`.
The two boundary kernels each have allowance `(4/5)^N*P(p)`. Thus
`norm_lattice_sub_integral_le` proves

```math
\left|\sum_{\lfloor a\rfloor<n\le\lfloor b\rfloor}K_{p,N}(3/2+i y,n)
-\int_a^bK_{p,N}(3/2+i y,x)\,dx\right|
\le C(p,y)(4/5)^N
```

for `N>=1` and every `1<=a<=b`. The constant is independent of both
endpoints. `tendsto_lattice_sub_integral` therefore covers arbitrary moving
intervals with a fixed polynomial and ordinate. No zero or pole-annihilation
hypothesis is used. The constant depends on the full coefficient budget and
the ordinate; it is not asserted uniform over unbounded heights or growing
filter budgets.

## The original source is preserved

Write `J_{p,N}` for the existing signed integral of `K'*(x-theta(x))`, and
`B_{p,N}` for its two original Abel boundary terms. The exact comparison
`centered_sub_carrier` is

```math
L_{p,N}-J_{p,N}
=B_{p,N}-\left(\sum K_{p,N}-\int K_{p,N}\right).
```

For every fixed polynomial, `norm_centered_sub_carrier_le` proves

```math
|L_{p,N}-J_{p,N}|
\le 2^{-N}(\log4+1)E(p)+C(p,\gamma)(4/5)^N,
```

where `E(p)=zetaPrimeBandEndpointConstant p` is the existing explicit
coefficient budget. This comparison requires no root condition on `p`.
`tendsto_scaled_comparison` proves it still vanishes after multiplying by
`u^(N+1)`, for every `0<=u<=1`.

Now let `rho=beta+i*gamma` be a hypothetical nontrivial zero with `beta>1/2`,
put `u=3/2-beta`, and take its original normalized zero-mode filter.
`tendsto_actual_source` and `tendsto_actual_source_re` prove

```math
u^{N+1}L_{p,N}(\gamma)\longrightarrow-m_\rho,
\qquad
u^{N+1}\Re L_{p,N}(\gamma)\longrightarrow-m_\rho.
```

These retain the original analytic multiplicity. The source theorem uses
the hypothetical zero; the sampling and comparison estimates above are
independent of it. No zero is asserted to exist.

The sufficient independent target is still only

```math
\exists\varepsilon>0\ \forall N_0\ \exists N\ge N_0:
u^{N+1}\Re L_{p,N}(\gamma)\ge-m_\rho+\varepsilon.
```

All-order norm decay is stronger than necessary. This slice removes the
sampling cost and exposes the signed arithmetic on the actual integer
lattice; it does not prove that floor. Further pair or operator estimates
must retain this same source and all prime/composite cross terms. The
quadratic work from the preceding slice remains a companion identity,
not an independent estimate for this linear sum.
