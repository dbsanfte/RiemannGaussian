# Unscaled squarefree decay under the actual prime sieve

The theorem `tendsto_squarefreeEuler_actual_quadratic_sieve` proves
decay of the complete squarefree arithmetic response under the exact
quadratic prime sieve used in the current RH source. It holds for every
moving natural divisibility mark and every fixed complex polynomial.
The response is **unscaled**: no hypothetical-zero normalization is used
to make it small.

This closes a limitation of the earlier sublinear-cardinality theorem,
which did not cover the actual sieve. It does not close the independent
upper bound on the prime-deleted, Möbius-weighted large-prime response.

## The arithmetic quantity

The original coefficient is

```text
c(S,P,n) = 1 if n is squarefree, P divides n, and no prime in S divides n;
           0 otherwise.
```

For a polynomial `p` and a fixed height `|y| > 1`, its response is

```text
B(p,S,P,N,y) = sum_n c(S,P,n) K_p,N(3/2+i*y,n),

K_p,N(s,n) = n^(-s) sum_k p_k log(n)^(N+k)/(N+k)!.
```

Ordinary primes are included. The sum converges absolutely at its stated
center. Invalid or incompatible marks give zero coefficients pointwise;
the estimate covers those marks as well.

## Uniform theorem and explicit allowance

Let `R_N` be any natural cutoff tending to infinity and satisfying,
eventually,

```text
sqrt(R_N) <= N/40.
```

`exists_squarefreeEuler_quadratic_sieve_bound` proves a constant `C > 0`
and an eventual bound, simultaneously for **every** prime subset
`S` of `[1,R_N]`, **every** natural mark `P`, and **every** polynomial `p`:

```text
norm(B(p,S,P,N,y))
  <= C exp(-N / (20 log(R_N+2))) sum_k norm(p_k).
```

There is no restriction on the size or growth of the mark.
`tendsto_squarefreeEuler_quadratic_sieve_allowance` proves that the
displayed exponential tends to zero. The general limit theorem
`tendsto_squarefreeEuler_quadratic_sieve` therefore permits both the prime
subset and the divisibility mark to change arbitrarily with the moment.

## Where the saving comes from

The earlier bound replaced the excluded primes by all integers, costing
an exponential in `sqrt(R)`. The new bound first uses the actual prime
density. Abel summation and Mathlib's classical Chebyshev theorem give

```text
sum_(p <= R) log(p)/sqrt(p) <= 3 sqrt(R),
sum_(p <= R) 1/sqrt(p) <= 8 sqrt(R)/log(R+2)  eventually.
```

The second estimate is also proved uniformly for every prime subset of
the cutoff. No prime number theorem or unproved cancellation estimate is
assumed.

The circle radius is then chosen by a fixed formula:

```text
r_R = 1 + 1/log(R+2).
```

It eventually lies inside the previously proved analytic disc for the
exact quotient `zeta(s)/zeta(2s)`. Its lower real edge is
`1/2 - 1/log(R+2)`. For each excluded prime, the extra local weight is
at most `exp(1) < 3`. All squarefree divisibility marks have a common
finite allowance, uniformly as that edge moves.

`exists_squarefreeEulerBudget_moving_radius_bound` consequently proves
an Euler allowance at most

```text
A exp(30 sqrt(R)/log(R+2)).
```

For large `R`, the Cauchy gain has logarithm at least
`(4/5) N/log(R+2)`. The cutoff condition makes the sieve loss at most
`(3/4) N/log(R+2)`. Their difference is the explicit positive saving
`N/(20 log(R+2))`. The polynomial envelope remains visible throughout.

## Application to the current source

The existing source uses

```text
u = 3/2 - Re(rho),
q = u^(-1/4),
R_N = floor(N log(q)/8)^2,
S_N = every prime <= R_N.
```

`sqrt_zetaRightHalfPrimePatternCutoff_le` checks the exact rounded cutoff
against `N/40` at every order. It uses `q <= 6/5` and
`log(q) <= q-1 <= 1/5`. The existing theorem supplies `R_N -> infinity`
under the hypothetical right-half zero. Thus
`tendsto_squarefreeEuler_actual_quadratic_sieve` applies with no missing
sieve-growth premise and every moving mark `P_N`.

The general theorem has no zero hypothesis. The specialization uses one
only to select the repository's already-defined source schedule and height.

## Physical logarithmic weights

`SquarefreeEulerLog.response` retains the genuine arithmetic logarithm:

```text
B_log(p,S,P,N,y) = sum_n c(S,P,n) log(n) K_p,N(3/2+i*y,n).
```

For every polynomial, define its raised coefficients by
`raised(p,N)_k = (N+k+1) p_k`. The exact theorem
`SquarefreeEulerLog.log_mul_kernel` gives

```text
log(n) K_p,N(s,n) = K_raised(p,N),N+1(s,n).
```

The identity keeps the full complex coefficients before any estimate.
`SquarefreeEulerLog.exists_quadratic_sieve_bound` consequently proves,
with the same uniformity over every prime subset, mark and polynomial,

```text
norm(B_log(p,S,P,N,y))
  <= C (N+1) exp(-N / (20 log(R_N+2))) sum_k (k+1) norm(p_k).
```

`SquarefreeEulerLog.tendsto_quadratic_sieve_log_allowance` proves that
the complete factor `(N+1) exp(-N/(20 log(R_N+2)))` tends to zero.
It uses `log(N+2)^2/N -> 0` to absorb the linear factor into half the
exponential saving. Thus `SquarefreeEulerLog.tendsto_quadratic_sieve`
and `SquarefreeEulerLog.tendsto_actual_quadratic_sieve` prove unscaled
logarithmic decay, including the exact source sieve and every moving mark.

## Remaining RH obligation

The full survivor also contains a growing sum of divisor-pair marks,
selection of its large-prime logarithms, and ordinary-prime deletion.
The full physical logarithm is now controlled for every complete mark.
Uniform decay of each marked response still cannot be interchanged with
the growing divisor sum without paying for it, nor does it survive
ordinary-prime deletion automatically. The preceding exact matrix and
prime-insertion identities retain these operations and their phases.

The subsequent [complete-family theorem](zeta-squarefree-euler-family-decay.md)
now pays both coefficient masses and proves normalized full logarithmic
decay through the squared divisor cutoff. Its exact connection to the
original source leaves the ordinary-prime tail as the remaining signed
arithmetic obligation.

The cofinal strict signed upper bound below the surviving unit source is
still unproved. No stronger zero-free region, historical novelty claim,
or completed RH contradiction follows from this slice.

## Local verification

All three modules are imported by the root library. Direct warning-as-error
elaboration, focused and full builds, whole-project declaration lint,
focused verbose lint, and the compiled-environment status audit pass.
Terminal axiom checks use only `propext`, `Classical.choice`, and
`Quot.sound`. The placeholder and whitespace scans pass. The generated
dashboard changes only its inventory counts.
