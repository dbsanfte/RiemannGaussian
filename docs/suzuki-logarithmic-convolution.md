# Exact logarithmic convolution in the retained arithmetic moment

`SuzukiLogarithmicConvolution.lean` formalizes a logarithmic Dirichlet
convolution identity and transfers it to the actual Suzuki quantities.
All sums here are finite; no continuation or convergence assumption is
used. **This is an arithmetic identity, not a new global lower bound.**

Write `*` for Dirichlet convolution and `D f(n)=f(n)*log(n)` for
pointwise logarithmic weighting. Lean first proves

```text
D(f*g) = (D f)*g + f*(D g).
```

Applying this to `Lambda*1=log`, and then convolving with the actual
Mobius function, gives

```text
Lambda(n)*log(n) + (Lambda*Lambda)(n)
  = sum_(d*m=n) mu(d)*(log(m))^2.
```

The derivation uses the existing exact divisor identities. No claim of
mathematical novelty is made for this logarithmic convolution formula.

The center must be inserted in the same identity. For every real `r`,

```text
Lambda(n)*(log(n)-r)
  = sum_(d*m=n) mu(d)*log(m)*(log(m)-r) - (Lambda*Lambda)(n).
```

The center multiplies the inner logarithm `log(m)` on the Mobius side.
Replacing that logarithm by `log(n)` would change the convolution.

The theorem holds at each integer, so every finite real or complex test
preserves it. `sum_complex_weighted_vonMangoldt_center_eq_moebius_sub_pair`
retains the entire complex weight before a norm or real part is taken.

## The original Suzuki quantities

The finite linear form is exactly

```text
L_N(r) = sum_(n<=N) Lambda(n)*(log(n)-r)/sqrt(n)
       = sum_(n<=N) [sum_(d*m=n) mu(d)*log(m)*(log(m)-r)
                     - (Lambda*Lambda)(n)]/sqrt(n).
```

Lean substitutes this at the original corrected mass center
`r_N=2*log((M_N-c)/2)` and retains the complete background:

```text
B_N = C + 4*exp(r_N/2) + c*r_N + L_N(r_N).
```

It also proves the same identity directly on every complete centered
prime-power block `W(start,count)`, with its unchanged starting mass
center. The previous exact identity `Delta B = W - blockEntropy` remains
available with its full entropy cost.

## Cutoffs and the unresolved estimate

Here `(Lambda*Lambda)(n)` contains every ordered pair with product `n`;
summing over `n<=N` retains the complete product cutoff. The separate
[triangular-work formula](suzuki-product-cutoff-obstruction.md) uses a
different denominator and a larger product region. Its nonnegligible
product complement remains necessary when using that formula. The new
identity does not identify those two different pair sums.

The quantitative problem is still to bound the combined signed expression,
including the entropy and Archimedean terms. Coefficientwise positivity of
the pair function does not supply a lower bound after its subtraction,
and taking absolute values of the Mobius coefficients would discard the
new identity's cancellation.

A subsequent [Lean source audit](suzuki-convolution-source.md) proves that
the separate convolution has leading coefficient `m*(m-1)` at a zero of
multiplicity `m`. It vanishes at a simple zero, while the full difference
with the pair response retains `-m` for fixed centers. The audit includes
all convergent complex weights and the explicit effect of moving centers.
Smallness of the separate convolution is therefore not sufficient evidence
of a bound on the original signed quantity.

Principal declarations:

- `arithmeticFunction_logWeight_mul`
- `vonMangoldt_logWeight_add_self_convolution`
- `sum_moebius_log_mul_sub_center`
- `sum_weighted_vonMangoldt_center_eq_moebius_sub_pair`
- `sum_complex_weighted_vonMangoldt_center_eq_moebius_sub_pair`
- `suzukiLegendreLinearForm_eq_moebius_sub_pair`
- `suzukiMassBlockCenteredWork_eq_moebius_sub_pair`
- `suzukiMassLegendrePotential_eq_moebius_sub_pair`

The module is imported from the root library. Direct warnings-as-errors
checks, the full build, declaration lint, and terminal axiom audits passed
locally. Work remains uncommitted. No new zero exclusion or unconditional
RH proof is claimed.
