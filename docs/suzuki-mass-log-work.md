# Finite arithmetic work with a summable replacement error

`SuzukiMassLogWork.lean` removes the implicit canonical centers from the
signed-work target while retaining the full nonlinear mass logarithm.
The actual replacement error is now bounded and summable. **The required
independent cumulative lower bound remains open; no zero exclusion or
unconditional RH proof is claimed.**

At cell `j`, the old prefix ends at `j+2` and the next integer is `n=j+3`.
Write

```text
a_j = Lambda(n)/sqrt(n)
M_j = sum_{2 <= d < n} Lambda(d)/sqrt(d)
c = (Re digamma(1/4) - log(pi))/2
q_j = (M_j-c)/(2*sqrt(n)).
```

Lean proves `M_j-c > 0` from the original slope-matching equation. Define
the finite arithmetic work

```text
L_j = a_j * (log(n) - 2*log((M_j-c)/2))
    = -2*a_j*log(q_j).
```

For the unchanged canonical center `r_j`, the original work remains
`I_j = a_j*(log(n)-r_j)`. The exact identity is

```text
I_j = L_j + E_j
E_j = 2*a_j*log(1 + T(r_j)/(2*exp(r_j/2)))
0 <= E_j <= 2*exp(6)/(j+1)^2.
```

Here `T` is the convergent positive Lerch slope tail already retained in
the [bilinear estimate](suzuki-bilinear-work.md). The new proof bounds
`T(r) <= (8/15)*exp(-5*r/2)` for `r >= log(2)` and then uses the existing
canonical-center localization. No zeta-zero hypothesis is used.

The error estimate is uniform over arbitrary finite bands:

```text
0 <= sum_{j=s}^{s+k-1} I_j - sum_{j=s}^{s+k-1} L_j
  <= 4*exp(6)*(1/(s+1) - 1/(s+k+1))
  <= 4*exp(6)/(s+1).
```

Thus the complete cumulative difference converges to the genuine finite
sum of the positive errors. Lean also retains the exact canonical-gap
accounting, with the original summable transport costs `C_j`:

```text
G_(s+k) - G_s - sum L_j = sum E_j - sum C_j.
```

Its lower bound is minus the common transport-cost tail, and its upper
bound is `4*exp(6)/(s+1)`. Both approach zero independently of band length.
This is proved by
`suzukiFirstTailCanonicalGap_block_massLog_error_uniformly_small`.

The simpler bilinear work `J_j` is still available. Its exact relationship
to the retained expression is

```text
L_j = J_j + 2*a_j*(q_j - 1 - log(q_j)).
```

The added finite arithmetic reserve is nonnegative. Its summability is
still unproved, so dropping it could make the target unnecessarily strong.
The mass-log expression retains it and only separates the now controlled
Lerch error. The previous complete convexity reserve is exactly this
arithmetic reserve plus `E_j`.

`suzuki_signed_work_eventually_bounded_below_iff_massLog` proves that an
eventual finite floor for cumulative `L_j` is equivalent to such a floor
for the original cumulative `I_j`. Consequently
`riemannHypothesis_of_suzuki_massLog_work_eventually_bounded_below` connects
this wholly finite arithmetic target to the existing RH chain. Its
arithmetic premise has not been discharged.

The module is imported from the root library. Validation is local, with
warnings treated as errors and module lint and transitive axiom audits.
The work remains uncommitted under the user's instruction.
