# The complete complex Euler matrix and prime insertion

This theorem chain gives an exact divisor diagonalization and an exact
cancellation in the original large-prime arithmetic response. It does not
yet give the independent signed upper bound needed for the RH contradiction.

## The full matrix

For a finite excluded-prime set `S`, let `T` contain the squarefree integers
`1 <= d <= D` avoiding every prime of `S`. Write

```text
nu_s(d) = product_(p divides d) p^(-s)/(1+p^(-s)),
F_S(s)  = product_(p in S) (1+p^(-s))^(-1) * zeta(s)/zeta(2s),
G_w,v(s) = sum_(d,e in T) w(d) v(e) nu_s(lcm(d,e)),
Y_w(q,s) = sum_(d in T, q divides d) w(d) nu_s(d).
```

In `Re(s) > 0`, `form_eq_divisor_coordinates` proves, for every pair of
complex weight families,

```text
G_w,v(s) = sum_(1 <= q <= D) q^s Y_w(q,s) Y_v(q,s).
```

In particular, the original real Möbius weights give **complex squares**
`q^s Y_mu(q,s)^2`. They are not squared absolute values and need not be
positive. The identity retains phases in both the diagonal weight and
the complete sum over multiples. It follows from the exact shared-prime
identity `nu_s(lcm(d,e)) = nu_s(d) nu_s(e) sum_(q divides gcd(d,e)) q^s`.
This is a complex specialization of the classical Selberg divisor
diagonalization; no historical novelty is claimed for that identity.

`LSeriesHasSum_cutoff_diagonal` connects this matrix to the literal
squarefree arithmetic coefficient with the two original finite divisor
weights. `coefficient_moebius_self` recovers the original Möbius mask squared.
The corresponding moment and filter theorems preserve every factorial
logarithmic moment and every complex polynomial filter.

## Cancellation in the actual large-prime response

Put `G = G_mu,mu` and define

```text
A_D,S(s) = sum_(p prime, p <= D, p not in S) log(p) nu_s(p).
```

`smallInsertion_eq` proves that inserting each such prime into the full
matrix and summing its logarithmic weight gives exactly

```text
smallInsertion(s) = G(s) A_D,S(s) - G'(s).
```

Its proof tracks whether the inserted prime is already present in each
lcm. That incidence is exactly the complementary local factor occurring
in the derivative of `nu_s`. The formula holds for arbitrary complex
weight families; no entry or channel is bounded separately.

For `D >= 1`, let `P_D,S(s)` denote the genuine ordinary-prime tail
`sum_(p prime, p > D, p not in S) log(p) p^(-s)` in `Re(s) > 1`.
The formal definition also covers `D = 0`, using the literal mask.
`LSeriesHasSum_squareCoefficient` identifies the full prime-deleted
logarithmic square response as `-(F_S G)' - P_D,S`.
`LSeriesHasSum_actualSmall` identifies the actual small-prime correction
as `F_S (G A_D,S - G')`. Subtracting gives

```text
H_large(s) = (-F_S'(s) - F_S(s) A_D,S(s)) G(s) - P_D,S(s).
```

`LSeriesHasSum_largeResponse` proves this identity for the **original**
large-prime coefficients. Thus the explicit first derivative `G'` cancels
before an estimate is taken. Higher Taylor derivatives of the remaining
product still differentiate its factors; the theorem does not delete
those derivatives.

`hasSum_large_filter` carries the cancellation to every original filtered
arithmetic sum. `normalized_large_source_eq` specializes it to the current
RH source, with the actual selected zero, moving excluded-prime set, jet
polynomial, common divisor/prime cutoff, and normalization unchanged.

## Domains and remaining obligation

The local matrix and insertion identities hold in `Re(s) > 0`. The
arithmetic L-series identities above assert genuine convergence in
`Re(s) > 1`, including the actual moment center `3/2 + i*y`. They do not
assert that the raw ordinary-prime series converges to the left of that
half-plane, and no singular or divergent series has been silently
reinterpreted as an analytic continuation.

The required cofinal strict upper bound below the surviving unit source
remains open. The new formula gives an exact factorization in which to
study it: the full complex matrix, the scalar prime contribution, and the
ordinary-prime tail remain coupled. A bound on individual marked Euler
responses does not yet control this growing expression. No new zero-free
region or proof of RH follows from these identities alone.

## Local verification

Both modules are imported by the root library. Direct warning-as-error
elaboration and the focused and full builds pass. Whole-project and
focused declaration lint, the compiled-environment status audit, and the
source placeholder and whitespace scans pass. Fifteen terminal axiom
checks use only `propext`, `Classical.choice`, and `Quot.sound`.
