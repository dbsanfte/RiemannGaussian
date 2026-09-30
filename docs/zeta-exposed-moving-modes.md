# Geometric control outside the selected resonance

[ZetaExposedMovingModes](../RiemannGaussian/ZetaExposedMovingModes.lean)
proves a geometric estimate for the finite competing zero modes. It does
not estimate the selected resonance or identify a masked arithmetic column
with a complete prime series. The [audit](exposed-moving-modes-audit.json)
records those distinctions.

For a finite support `S`, selected coordinate `z0=-u`, and `0<u<R`, assume
every competing coordinate has norm at least `R` and
`norm(a N z) <= C*(N+1)^d`. Then `complement_bound` proves

```math
\left\|\sum_{z\in S\setminus\{-u\}}a_{N,z}
        \bigl(u(-z^{-1})\bigr)^{N+1}\right\|
\le |S\setminus\{-u\}|\,C(N+1)^d(u/R)^{N+1}.
```

`tendsto_complement` proves convergence to zero. The coefficients can move
with `N`; no norm is taken over the selected mode. `selected_split` retains
its coefficient exactly. `exists_canonical_complement_bound` supplies a
single strict gap from the existing exposed-zero theorem and transfers it
to the actual canonical local divisor. Simplicity is not required.

## Application to the existing complete prime filter

For any polynomial `P_N`, `primeFilter_selected_split` gives exactly

```math
u^{N+1}\operatorname{primeFilter}(P_N,N)
=-m_\rho P_N(1/u)+E_N+
u^{N+1}(\operatorname{pole}_{P_N}
 -\operatorname{residual}_{P_N}+\operatorname{reflected}_{P_N}).
```

Here `E_N` is the negative competing direct-mode sum.
`primeFilterComplement_bound` and `primeFilter_resonance_bound` bound it
by the displayed geometric rate, with the polynomial evaluation budget
as an explicit hypothesis. `tendsto_primeFilterComplement` applies to a
whole moving family `P_N`. Every actual divisor multiplicity is retained.
The old pole, residual and reflected terms keep their original signs.
Their existing fixed-filter estimates remain available; this theorem does
not silently extend those estimates to arbitrary moving filters.
The filter here uses the repository's complete von Mangoldt moments.
An ordinary-prime or finite-carrier application must also retain its
proper-prime-power and finite-completion corrections.

## Signed profile and cheap completion audit

`ZetaRieszCofactorDiscrepancy.literal_profile_factorization` proves, for
each fixed owner prime, the canonical rows and their exact weight `w`,

```math
\sum_{D=1}^R(f(D)-f(D+1))\operatorname{compositeModel}(X,D,w)
=\left[\sum_{D=1}^R(f(D)-f(D+1))c_D\right]
  \left[\sum_{n=1}^X w(n)\right].
```

The first bracket remains one signed arithmetic scalar. The second retains
the actual allocation, phase and masks. The weight is independent of `D`.
If the profile depends on the owner prime, that signed scalar keeps this
dependence; it cannot be pulled outside the sum over owners for free.
`literal_profile_error_exponential` joins this identity to the existing
comparison estimate, with error allowance

```math
C_{\rm count}e^{-N/32}
 \left(\sum_{k=1}^X k|w(k)-w(k+1)|\right)
 \left(\sum_{D=1}^R|f(D)-f(D+1)|\right).
```

Its support conditions `R^2<=k`, `exp(N/2)<=k`, and both exterior endpoint
conditions are explicit. This is not an unconditional exponentially small
error for the literal weights: the earlier
[mask-variation audit](zeta-riesz-signed-density-main.md#audit-of-the-literal-mask-variation)
still applies. The full hinge support also includes unhandled long cutoffs.

In `ZetaRieszJoinedHeadCancellation`, `markedWeight_count_le_one` and
`markedWeight_count_le_two` prove exact vanishing at low total prime count.
`ordinary_prime_correction_eq_zero` proves that a prime cofactor added to
one marked prime contributes exactly zero, including arbitrary complex
phases and extra masks. `cofactor_head_completion` therefore permits adding
the unit and ordinary-prime head to a finite cofactor sum while retaining
the joined marked weight. It does not pay the omitted composite cofactors.
In particular, a singleton middle prime after **two** primes have already
been marked makes a three-prime label and is not covered by this vanishing.

## Remaining arithmetic obligation

The subsequent [ordered-cofactor payment](zeta-riesz-exposed-mode-coupling.md)
now gives `poly(N)*(9999/10000)^N` for a concrete actual component:
genuine modes at distance at least `501/1000`, on `|xi|<=1/2000`, with the
entire ordered cofactor and factorial rectangle retained. Its exact
signed ledger preserves the selected mode, closer competitors and exterior
frequencies. This pays a sector, not the full masked complement.

The complete-filter estimate is a real geometric saving, not another
polynomial improvement to the growing `(2u)^N` envelope. To use it on the
literal carrier one must still prove the exact masked transfer with a
polynomial competing-mode budget and pay its comparison errors. Exposure
is at the selected evaluation centre; a Fourier-shifted centre needs its
own gap estimate. Neither separate complete-leg convergence nor a bare
cofactor completion supplies that transfer.

Even after this bridge, the selected resonance needs an independent signed
bound. The cofinal floor `-79/1000-o(1)`, ceiling `3/2+o(1)`, and RH remain
open. No new zero-free region follows from this slice.
