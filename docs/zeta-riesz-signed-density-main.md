# Bounding the signed main expression

[The Lean proof](../RiemannGaussian/ZetaRieszSignedDensityMain.lean) bounds
the existing `ZetaRieszCofactorDiscrepancy.compositeModel`, with the literal
zero-extended owned weights. It uses no zero hypothesis, prime-density
approximation, virtual prime weight, or assumed mean-value constant.

The bound is explicit and uniform over the original masks. It still grows
at source scale for fixed `u>1/2`; neither cofinal endgame inequality follows.
The [validation record](riesz-signed-density-main-audit.json) distinguishes
this main-term estimate from the still-unpaid comparison error.

## Cancellation in the original cutoff coefficient

Write `delta` for the repository's canonical unmarked squarefree density.
`density_marks` proves its exact marked-prime factorization:

```math
\operatorname{density}(\operatorname{primeFactors}(n))
 =\delta\prod_{p\mid n}\frac1{p+1},\qquad 0\le\delta\le1.
```

Put `b(n)=product_(p|n) 1/(p+1)` and `q(n)=b(n)/n`, for `n>=1`.
The signed identity `density_convolution` and the normalized mass identity
`density_correction_mass` give

```math
\mu(n)b(n)=\sum_{ab=n}\frac{\mu(a)}a q(b),\qquad
q(b)\ge0,\qquad \delta\sum_{b\ge1}q(b)=1.
```

The convolution is proved on every prime power, not just squarefree
integers. Preliminary summability uses the square-times-squarefree decomposition.
The exact Euler product then cancels the density normalization;
`normalized_correction_prefix_bound` gives `delta*sum_(b<=X) q(b)<=1`.
Applying the repository's
classical signed reciprocal Möbius bounds gives

```math
|c_D|\le2,\qquad
|\eta(t)|\le7,\qquad
\eta(t)=\sum_{n\le e^t}\mu(n)
 \operatorname{density}(\operatorname{primeFactors}(n))(t-\log n).
```

These are `densityPrefix_bound` and `densityRiesz_bound`. Crucially, the
Möbius signs are summed before taking the norm. The bound does not replace
their contribution by the sum of absolute divisor terms.

For the exact original hinge `h_p(d)`, `hinge_density_eq` then gives

```math
\sum_{d\le R}\mu(d)\operatorname{density}(\operatorname{primeFactors}(d))h_p(d)
 =\eta(L)-\eta(L-\log p),\qquad
|\eta(L)-\eta(L-\log p)|\le14,
\quad R\ge\lfloor e^L\rfloor.
```

The full-support condition on `R` matters. The uniform sharp-prefix bound
`|c_D|<=2` applies to every `D`, but the two-hinge bound is for the recombined
profile covering its entire support.

## The whole literal comparison main

For any finite squarefree label set `B` with at least three prime factors
per label, retain its exact largest-prime owner rows, `boundedShare`, full
cosine phase and factorial weight. The unit and prime-cofactor weights
are exactly zero, as proved previously. Define the existing comparison
main by its original formula

```math
\mathcal M=
\sum_{p\in\operatorname{ownerPrimes}(B)}
\sum_{D=1}^R (h_p(D)-h_p(D+1))\,\operatorname{compositeModel}(X,D,w_p),
\quad X=\max\operatorname{cofactors}(B).
```

`literal_profile_main_bound` first retains all cofactor phase cancellation:

```math
|\mathcal M|\le14\sum_p\left|\sum_{n\le X}w_p(n)\right|.
```

`whole_signed_main_bound` then evaluates an unconditional envelope for the
entire remaining weight. Unique ownership counts each integer only once;
the factorial radial mass is summed before charging a saddle maximum.
For `scale=u^(N+1)` and the exact core support, `core_signed_main_bound`
proves

```math
\boxed{\displaystyle
|\mathcal M_N|\le
28e^2\frac{N+1}{L_N}(2u)^{N+1}.}
```

Every original core mask and count cutoff is retained on the left. The
right has no unevaluated population, energy or arithmetic constant. This
is a bound on the existing signed comparison main, **not** an identity
between that main and `coreResponse`.

## What this saves and what remains

The signed cutoff coefficient is now bounded independently of the cutoff,
instead of charging its growing absolute divisor sum. Both the sharp
main and its full hinge profile have checked bounds. This is a concrete
main-term cancellation estimate, not another counting-error estimate.

The result supplies no negative source exponent. At the largest requested
radius, the remaining base is exactly `2u=10001/10000>1`. Its growing
envelope does not prove that the actual signed main grows, but it cannot
give the required cofinal floor `-79/1000-o(1)` or ceiling `3/2+o(1)`.
The full comparison error, including literal mask variation and the long
cutoffs, also remains unpaid. The short-cutoff error theorem cannot be
applied to the entire hinge support without proving its hypotheses.

The next useful gain must control the remaining signed phase-weighted
columns jointly, or combine their main and comparison error before taking
norms. The exact column sum in `literal_profile_main_eq` is retained for
that purpose. No RH or zero-free claim follows from this slice.

The next [exposed-mode estimate](zeta-exposed-moving-modes.md) uses a strict
spectral gap instead of further polynomial improvements to this envelope.
It bounds the competing finite modes geometrically while retaining the
selected source. The literal masked transfer remains an obligation.

## Audit of the literal mask variation

[ZetaRieszLiteralVariationAudit](../RiemannGaussian/ZetaRieszLiteralVariationAudit.lean)
now quantifies a loss in the existing absolute Abel error allowance. This is
a negative audit of that allowance, not a new main-term saving or a lower
bound for the actual signed error.

Every canonical column weight `w(n)` is exactly zero when `4` divides `n`,
because its cofactor must be squarefree. Three adjacent differences therefore
dominate each value, regardless of its phase. For `X=max(cofactors B)`,
`literal_variation_lower` proves, including the last exterior jump,

```math
\sum_{n=1}^X n|w(n)-w(n+1)|\;\ge\;
\frac13\sum_{n=1}^X n|w(n)|.
```

On a column supported at `n>=exp(N/2)`,
`literal_short_allowance_lower` consequently proves

```math
e^{-N/32}\sum_{n=1}^X n|w(n)-w(n+1)|\;\ge\;
\frac{e^{15N/32}}3\sum_{n=1}^X|w(n)|.
```

The support premise is explicit; it is not asserted automatically for every
finite-order column. The inequality holds for the original weights, with
every allocation and phase retained. It applies to any eligible squarefree
label set with at least three prime factors, without a zero hypothesis.

Thus the advertised `exp(-N/32)` prefactor in the short-cutoff error estimate
does not give a small **relative** allowance for the canonical zero extension.
Its absolute variation carries a much larger factor. This does not prove
that the actual error grows, or that the allowance diverges for every moving
column; its absolute mass could also change. It rules out treating the
literal squarefree mask as a smooth amplitude in that argument. A different
extension needs its own exact main/error ledger and paid variation. The
existing signed cutoff correlations avoid this absolute-variation loss, but
their sufficient joint bound remains open.
