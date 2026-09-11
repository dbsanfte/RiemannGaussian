# Growing logarithmic divisor families and the remaining prime tail

The local continuation transports the uniform marked quadratic-sieve
estimate through a complete growing divisor matrix and its physical
logarithm. It then connects that independent decay to the original
prime-deleted large-prime response. The remaining signed arithmetic
obligation is an explicit ordinary-prime tail. RH remains open.

## The complete logarithmic response

For finite sets `S,T` and arbitrary complex divisor families `w,v`, put

```text
c(S,n) = 1 if n is squarefree and no prime in S divides n; 0 otherwise,
W_T(n) = sum_(d in T, d divides n) w(d),
V_T(n) = sum_(e in T, e divides n) v(e),

J_N(p,S,T,w,v) = sum_n c(S,n) W_T(n) V_T(n) log(n) K_p,N(3/2+i*y,n).
```

These are complex products, not squared norms. Taking the two families
equal to the real Möbius function recovers the actual squared mask.
Ordinary primes are included.

`SquarefreeEulerQuadratic.hasSum_logResponse` and
`logResponse_eq_lcm_sum` retain the exact convergent expansion

```text
J_N = sum_(d,e in T) w(d) v(e) B_log(p,S,lcm(d,e),N,y).
```

There is no restriction on the locations or sizes of the marks.
Incompatible or nonsquarefree marks vanish in the original coefficient.
`logResponse_eq_cutoff_diagonal` separately preserves the full complex
Selberg representation and its exact raised polynomial. Thus the estimate
does not replace the signed identities.

## Paying for every pair

For the same growing cutoff `R_N` with `sqrt(R_N) <= N/40` eventually,
`exists_logResponse_quadratic_sieve_bound` proves, simultaneously for
every prime subset `S` of that cutoff and every `T,w,v,p`,

```text
norm(J_N) <= C (N+1) exp(-N/(20 log(R_N+2))) E(p) M(w,T) M(v,T),

E(p)   = sum_k (k+1) norm(p_k),
M(w,T) = sum_(d in T) norm(w(d)).
```

Both complete coefficient masses appear. There is no exchange of a
growing sum with a limit without paying its cost.
`tendsto_logResponse_of_mass_budget` proves decay for arbitrary moving
finite families whenever the chosen normalization keeps the product of
these two masses bounded. This permits arbitrary changing mark locations;
it is not a search for one coefficient family.

For the current source let

```text
u = 3/2 - Re(rho),       q = u^(-1/4),
D0_N = floor(q^N),      D_N <= D0_N^2.
```

`source_pair_count_bound` proves exactly

```text
u^(N+1) D_N^2 <= u.
```

The key identity is `u q^4 = 1`; integer rounding and the whole pair
count are included. Every pair of weights bounded by one therefore
satisfies the mass budget. The remaining factor
`(N+1) exp(-N/(20 log(R_N+2)))` tends to zero by the preceding logarithmic
allowance theorem.

`tendsto_normalizedLogResponse_square_cutoff` proves independent decay
for all those moving complex families, under the actual full quadratic
prime sieve. `tendsto_normalized_moebius_logResponse` specializes it to
the literal Möbius square, with no missing coefficient-family premise.

This is a direct transport of the new uniform marked estimate through
the complete logarithmic sum. It is not claimed to improve the geometric
rate or the cutoff power in the earlier lcm estimates for their different,
source-subtracted correlations.

## Exact connection to the original survivor

Let `L_N` denote the original normalized large-prime composite response
at the common divisor/prime cutoff `D_N`, and let `S_N` be the original
quadratic prime sieve. Define the normalized ordinary-prime correction

```text
P_N = u^(N+1) sum_(a prime, a>D_N, a not in S_N)
                    log(a) K_p,N(3/2+i*Im(rho),a),
```

using the original polynomial `p = zetaRightHalfPoleJetFilter rho hrho`.
`primeCorrectionCoefficient_eq_prime_tail` and
`primeLogResponse_eq_prime_sum` prove this literal formula: no squarefree
weight, divisor matrix, or Möbius mask remains in `P_N`.
`summable_primeLogResponse` proves genuine convergence for every fixed
moment in `Re(s)>1`.

`normalized_large_add_prime_eq` proves the exact identity

```text
L_N + P_N = normalized complete logarithmic matrix
              - normalized small-prime insertion.
```

The first term now decays by the complete-family theorem. The second
decays by the previously proved `RoughPrimeLogLcm.tendsto_square_cutoff`.
Consequently `tendsto_large_add_primeCorrection` proves independently

```text
L_N + P_N -> 0
```

for every positive moving cutoff through `D0_N^2`. This decay proof does
not use the multiplicity-source limit as an estimate.

The already proved source theorem gives `L_N -> m_rho`, so the separate
theorem `tendsto_normalizedPrimeLogResponse` identifies

```text
P_N -> -m_rho.
```

That last statement is a consequence under the hypothetical right-half
zero. It supplies no independent arithmetic estimate on the prime tail.

## The remaining RH obligation

An independent bound on the ordinary-prime sum is still needed. Since
the multiplicity is at least one, a fixed `epsilon > 0` and a cofinal
lower bound `Re(P_N) >= -1+epsilon` would already contradict its required
limit. Full norm decay is stronger than necessary. Merely being greater
than `-1` at each finite moment, with no fixed positive margin, would not
rule out convergence to `-1`.

The complex polynomial, oscillatory prime phase, growing cutoff and
sieve remain in this last sum. Positivity of the real coefficient
`log(a)` does not establish the required sign after multiplication by
the complex kernel. No improved zero-free region or completed RH
contradiction is claimed.

The subsequent [prime-tail literature audit](prime-tail-literature-audit-2026-09-11.md)
records a Lean-checked continuous comparison in which positivity and
conjugate pairing coexist with a negative unit complete-moment response.
It compares sixteen primary sources with the actual carrier and identifies
the additional factorization and additive-correlation hypotheses that a
new estimate would need. This is a diagnostic and research assessment;
the independent prime-tail bound remains open.

## Local verification

Both modules are imported by the root library. Warning-as-error direct
elaboration, focused and full builds, whole-project declaration lint,
focused verbose lint, and the compiled-environment status audit pass.
Explicit axiom checks use only `propext`, `Classical.choice`, and
`Quot.sound`; placeholder and whitespace scans pass. Generated-status
changes are confined to inventory counts. These are local validation results; remote CI is checked separately on the exact commit.
