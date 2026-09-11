# Squarefree Euler cancellation with moving marks

The theorem chain controls the **complete** squarefree arithmetic
series, including its ordinary-prime terms. It does not prove the independent
upper bound on the prime-deleted, Möbius-weighted survivor needed for RH.

## Exact arithmetic carrier

For a finite prime set `S` and a squarefree integer `P` whose primes avoid `S`,
the existing coefficient is

```text
c(S,P,n) = 1 if n is squarefree, P divides n, and every prime in S avoids n;
           0 otherwise.
```

`LSeriesHasSum_markedSquarefreeEuler` proves absolute convergence and the
exact identity, for `Re(s) > 1`,

```text
sum_n c(S,P,n) n^(-s)
  = [P^(-s) product_(a in S union primeFactors(P)) (1+a^(-s))^(-1)]
      zeta(s)/zeta(2s).
```

`squarefreeEuler_coefficient_eq_dilation` also keeps its coefficient-level
meaning: the cofactor `n/P` must avoid both `S` and the primes of `P`.
`hasSum_markedSquarefreeEuler_moment` and
`hasSum_markedSquarefreeEuler_filter` carry the identity to the original
factorial logarithmic moments and complex polynomial filters. Analytic
continuation is applied to their summed function; the raw Dirichlet series
is not claimed to converge left of the Euler half-plane.

## Radius beyond one

Write the previously proved zero-free width as

```text
Delta(t) = 792 / (7625 log(|t|+2) - 2000).
```

At every fixed `|y| > 1`, define

```text
r(y) = 1 + min((|y|-1)/2, Delta(2|y|+3)/4).
```

`squarefreeEulerRadius_bounds` proves `1 < r(y) < min(|y|,17/16)`.
`squarefreeEuler_disc_safe` proves that the closed disc about `3/2+i*y`
with this radius avoids the numerator's pole and every zero or pole of
the doubled zeta denominator. Thus the exact quotient is analytic on a
neighbourhood of the disc. The finite marked multiplier is also analytic
there, since its local denominators are nonzero in `Re(s) > 0`.

The classical identity `sum mu(n)^2 n^(-s) = zeta(s)/zeta(2s)` is not a
novelty claim. The new project result combines its literal arithmetic
filters with the repository's checked zero-free region and the uniform
moving-mark estimates below.

## Uniformity and growing sieves

`exists_markedSquarefreeEuler_filter_bound` retains an explicit finite
allowance at `sigma = 3/2-r(y)`:

```text
A_sigma(S,P) = P^(-sigma)
  product_(a in S union primeFactors(P)) (1-a^(-sigma))^(-1).
```

For **every** positive `sigma`,
`exists_squarefreeEulerBudget_card_bound` proves constants `C > 0` and
`K > 1`, independent of `S` and `P`, such that

```text
A_sigma(S,P) <= C K^(card S).
```

The reason the mark cost is uniform is exact: each marked prime contributes
`a^(-sigma)/(1-a^(-sigma))`. All sufficiently large primes have factor at
most one; only finitely many smaller primes can enlarge the product, and
squarefreeness allows each at most once.

`exists_squarefreeEuler_uniform_mark_filter_bound` consequently gives

```text
norm(response(p,S,P,N,3/2+i*y))
  <= C_y K_y^(card S) r(y)^(-N)
       sum_(k in support p) norm(p_k) r(y)^(-k).
```

It covers every natural mark, including incompatible or nonsquarefree
marks, whose literal coefficients vanish. The constants are independent
of the polynomial, moment, mark, and excluded-prime set.

`exists_squarefreeEuler_sublinear_sieve_bound` proves geometric decay for
**every** prime-set schedule with `card(S_N)/N -> 0`, uniformly over all
marks at each sufficiently large moment. The polynomial envelope remains
explicit. `tendsto_squarefreeEuler_sublinear_sieve` specializes this to
every fixed polynomial and **arbitrary moving marks** `P_N`, with no mark
growth restriction and no zero hypothesis. These are bounds on the actual
unscaled arithmetic sums.

## Remaining RH obligation

The current obstruction has additional prime-log weights, a growing sum
of Möbius divisor-pair marks, and ordinary primes removed. The new uniform
bound on each complete marked response does not by itself control that
whole sum. The current sieve contains every prime up to a cutoff of order
`N^2`; the sublinear-cardinality theorem does not supply its bound. The
subsequent [quadratic-sieve theorem](zeta-squarefree-quadratic-sieve-decay.md)
now proves unscaled decay for that exact sieve, uniformly over moving marks,
using Chebyshev prime density and a moving Cauchy radius. The
full signed prime-deleted source must still be bounded independently
below its unit source along cofinally many moments. No stronger zero-free
region or RH contradiction is claimed by this slice.

## Local verification

All three modules are imported by the root library. The warning-as-error
full build passes, as do whole-project declaration lint, focused verbose
lint, the compiled-environment status audit, and the placeholder scan.
Thirteen terminal axiom checks use only `propext`, `Classical.choice`, and
`Quot.sound`.
