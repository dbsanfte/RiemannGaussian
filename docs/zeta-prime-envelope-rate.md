# General subexponential error envelopes fail at source scale

[ZetaPrimeEnvelopeRate](../RiemannGaussian/ZetaPrimeEnvelopeRate.lean)
checks a proposed route from zero-free regions to the independent prime-tail
bound. Its conclusion is a **method obstruction**, not a lower bound for the
actual signed arithmetic error. The proved zero-free region is unchanged
and RH remains open.

## All fixed filters and all continuous sublinear exponents

Put `u=3/2-beta`, so a hypothetical right-half zero has `1/2<u<1`.
For a fixed complex polynomial `p`, retain the original factorial amplitude

```math
F_{p,N}(t)=\sum_k p_k\frac{t^{N+k}}{(N+k)!}.
```

Let `g(t)=exp(-r(t))`, where `r` is any continuous real function with
`r(t)/t -> 0`. No coefficient family or particular sublinear rate is
selected. Consider the local absolute allowance

```math
A_N(p,g,u)=u^{N+1}\int_{N/u}^{N/u+1}
  g(t)e^{-t/2}|F_{p,N}(t)|\,dt.
```

`windowAllowance_tendsto_atTop` proves divergence for every continuous
`g` which is eventually at least `exp(-epsilon*t)` for every positive
`epsilon`, whenever `p(1/u)=1`. The exponent formulation follows in
`sublinear_exponent_allowance_tendsto`. The later
`windowAllowance_sublinear_tendsto_of_eval_ne_zero` only requires
`p(1/u) != 0`; scaling the polynomial transports the allowance exactly.

The proof retains the complete fixed filter until its uniform localization
near `t=N/u`. Stirling's inequality then gives, for every `epsilon>0`
whose exponential is eventually below `g`,

```math
A_N(p,g,u)\ge
\frac{u e^{-\epsilon-1/2}}{12N}
\exp\!\left(\left[1-\frac{1/2+\epsilon}{u}\right]N\right)
\qquad\text{eventually},
```

for normalized `p`. Choose `0<epsilon<u-1/2` to obtain positive exponential
growth. This bounds a genuine finite integral; it does not use a totalized
improper integral or a conjecture about prime distribution.

`window_inside_original_band` proves that this witness interval belongs
to the original prime band. Consequently `bandAllowance_sublinear_tendsto`
proves divergence of the entire positive allowance, and
`actual_bandAllowance_sublinear_tendsto` instantiates the actual pole-jet
filter with its normalization proved.

## Keeping the complete derivative does not remove this obstruction

The signed Chebyshev integral uses a derivative, so checking a separately
bounded kernel term alone would leave an information-flow question.
Keep its exact derivative filter instead:

```math
Q_{p,s}(X)=(1-sX)p(X),\qquad
F_{Q_{p,s},N}=F_{p,N}-sF_{p,N+1}.
```

`derivativeFilter_polynomial` and `derivativeFilter_kernel` prove this
identity for the literal complex prime kernel. At `s=3/2+i*gamma` and
`x=exp(t)`, `derivative_norm_log_coordinate` proves exactly

```math
e^{2t}|K'_{p,N+1}(s,e^t)|
 =e^{-t/2}|F_{p,N}(t)-sF_{p,N+1}(t)|.
```

The two factors `exp(t)` are the proposed Chebyshev error envelope's
factor `x` and the change-of-variable Jacobian. Neither derivative term,
nor its imaginary contribution, has been separated before the norm.

For the actual normalized filter,
`Q(1/u)=1-s/u=-rho/u != 0`. The finite source window is also inside the
**successor** prime band. Thus the terminal theorem
`actual_full_derivative_allowance_tendsto` proves

```math
u^{N+2}\int_{\log B^-_{N+1}}^{\log B^+_{N+1}}
 e^{-r(t)-t/2}|F_{p,N}(t)-sF_{p,N+1}(t)|\,dt\longrightarrow+\infty,
```

where `B^-_M=exp(M*log(2)/4)` and `B^+_M=2^(32*M)` are the original
finite arithmetic boundaries. The moment index, band, full pole-jet
filter and source normalization all match. This obstruction remains after
preserving the entire complex derivative.

`original_derivative_envelope_eq_log` proves the complete change of
variables on every positive compact interval. The original envelope is
proved integrable, and `derivativeBandAllowance_eq_original` identifies
the two allowances exactly. Thus
`actual_original_derivative_allowance_tendsto` states the divergence
directly in the arithmetic coordinate:

```math
u^{N+2}\int_{B^-_{N+1}}^{B^+_{N+1}}
 x e^{-r(\log x)}|K'_{p,N+1}(s,x)|\,dx\longrightarrow+\infty.
```

There is no remaining informal substitution in this allowance audit.

## What this changes in the research plan

A pointwise estimate of the form
`abs(theta(x)-x) <= x*exp(-r(log x))`, with sublinear `r`, cannot close the
current fixed-filter contradiction by direct absolute integration: its
resulting allowance grows. The new Gaussian zero-free curve still supplies
actual zero exclusion and larger squarefree analytic discs. Further use of
those discs must provide additional signed or correlated arithmetic control,
not just a subexponential full-density error envelope.

The result does **not** assert that the actual Chebyshev error saturates
such an envelope. It does not rule out cancellation between logarithmic
times, an independent one-sided cofinal bound, or order-dependent filters
whose complete source and analytic errors are separately justified.

There is no conflict with the repository's general Suzuki--Landau
compensator theorem: its sufficient signed-work bound has a different
normalization. The present result does not supply that open arithmetic
bound or disprove it.

The next arithmetic input must reach the signed carrier itself. An exact
factorization alone is insufficient; its accompanying estimate must retain
and exploit information beyond a full-density absolute envelope. See the
[literature and interface audit](prime-tail-literature-audit-2026-09-11.md).

## Verification

The module is root-imported and checked with warnings as errors. Terminal
axiom audits and whole-project lint enforce the standard-only logical
axioms. Generated status remains a theorem inventory; this method
obstruction adds no zero-free milestone or RH completion claim. Work is
kept local under the user's commit hold.
