# Fixed-order factorial-cutoff test

The `1664/4096 -> 1665/4096` perturbation passes the exact algebraic checks,
but supplies **no independent floor saving**. Its narrow transition retains
the same coherent selected source. Stop this automatic-cutoff-cancellation
route; the independent arithmetic floor and RH remain open.

The baseline is `48f975c2154fe65919f66218dab86a42ec78aa99`. Its GitHub CI passed.
The new work stays local, outside ordinary-root registration and public
frontier metadata. All previous proofs and negative audits are preserved.

## Exact fixed-order identity

[`ZetaRieszFactorialCutoff`](../RiemannGaussian/ZetaRieszFactorialCutoff.lean)
defines `evaluation a u N K`, the existing completed `harmonicEvaluation`
with arbitrary factorial-prefix endpoint. At `K=13*N/32` they are exactly
equal. No physical prime support or phase is completed or replaced.

For `2*(K+1)<=N`, `evaluation_sub_succ` proves

$$
H_{N,K}-H_{N,K+1}
=\frac{N+1}{K+1}\,a_K
\left(\frac{a_{N-K-1}}{N-K}-\frac{a_{N-K}}{uL_N}\right).
$$

Two central endpoints and one successor-prefix endpoint are removed.
`evaluation_sub_eq_sum` telescopes this identity over the exact consecutive
orders; it keeps the complete complex products signed throughout.

All array orders, including zero, remain in the evaluator. The same joint
`22*C/N` array-difference price holds when `N<=4*K` and `2*K<=N`. The existing
proper-prime-power price therefore also applies to the candidate endpoint;
this is not a new physical-mask completion.

## Source formula and the narrow transition

For any constant array `a_k=c`, `K/(N+1)->theta`, `0<theta<1/2`, the exact
harmonic endpoints and the original integer-floor length give

$$
H_{N,K}\longrightarrow c^2 S_\theta(u),\qquad
S_\theta(u)=1+\log\frac{1-\theta}{\theta}
-\frac{\log(1/\theta)}{-2u\log u}.
$$

This formula is proved independently in Lean by
`evaluation_const_tendsto`. Under the original exposed-zero hypotheses,
`tendsto_ordinary_source` and `tendsto_mangoldt_source` transfer it to the
already-completed genuine arrays with `c=-m`. Actual multiplicity is retained.
The full ordinary-prime source-error mass remains height-dependent; the proof
does not certify an actual small entry order from the numerical controls.

Write `theta0=13/32`, `theta1=1665/4096`. Lean verifies

$$
S_{\theta_1}(u)<\frac{399}{5000},\qquad
S_{\theta_0}(u)-S_{\theta_1}(u)>\frac1{7000}
$$

throughout `1/2<=u<=10001/20000`. The first statement is a scalar source
comparison, not an independent upper bound for the original literal carrier.

The optional 360-bit balls, replayed independently at 420 bits, give these
rounded scalar controls for `m=1`:

| u | Original source S0 | Candidate source S1 | Transition S0-S1 |
|---|---:|---:|---:|
| 0.5 | 0.079929339846 | 0.079784033860 | 0.000145305986 |
| 0.500025 | 0.079900571421 | 0.079755284622 | 0.000145286799 |
| 0.50005 | 0.079871797035 | 0.079726529427 | 0.000145267608 |

These are source-model controls, not sampled actual primes or zeros. On the
original native dyadic schedule, `4096` divides `N` from `j=6` onward, and the
number of transition steps is exactly `N/4096`. Both facts are checked.

## Why the centered moment does not cancel

With `j=N-K-1` and `a_k->-m`, the exact complex recurrence defect satisfies

$$
(N+1)\left(\frac{a_j}{j+1}-\frac{a_{j+1}}{uL_N}\right)
\longrightarrow
-m\left(\frac1{1-\theta}-\frac1{-2u\log u}\right).
$$

At `theta1`, its real coefficient is less than `-6*m/25` uniformly on the
requested strip. It is approximately `-0.24214*m` to `-0.24221*m`, rather
than zero. The factorial complementary order is approximately `0.5935*N`,
whereas the centering length `u*L_N` is approximately `0.6931*N`. The mismatch
survives the limit. Multiplying by `a_K->-m` makes the one-step transition
positive and coherent.

[`ZetaRieszCutoffTransitionAudit`](../RiemannGaussian/ZetaRieszCutoffTransitionAudit.lean)
proves, for both the actual ordinary-prime and von Mangoldt arrays,

$$
H_{N,K_0}-H_{N,K_1}
\longrightarrow
m^2\bigl(S_{\theta_0}(u)-S_{\theta_1}(u)\bigr).
$$

Its ordinary-prime difference from the finite constant-source evaluation is
at most `44*(m+D)*D/N`, where `D` is the existing source-error mass. Only that
error vanishes. The selected transition does not.

`eventually_transition_source_lower` gives the conditional signed lower
bound `m^2/7000` on the transition. `false_of_transition_cofinal_upper` makes
explicit that a cofinal upper bound strictly below its exact selected limit
would itself be a new contradiction-strength arithmetic theorem. No such
independent upper bound is supplied here. This audit does not prove that an
independent arithmetic theorem is impossible.

## Original carrier ledger

`prefix_candidate_ledger` and `norm_prefix_candidate_ledger_le` retain exactly

$$
\text{prefixPairDefect}_N
=H_{N,K_1}+(H_{N,K_0}-H_{N,K_1})
+\text{previously paid error}_N.
$$

The error is the same `wholeCompletionBudget + squareBudget` already proved
geometrically small. There is no new literal support completion. In particular,

$$
S_{\theta_1}(u)+(S_{\theta_0}(u)-S_{\theta_1}(u))
=1-c_{\rm ret}(u)
$$

exactly. The candidate's smaller source has merely moved into the transition.
Using the candidate limit alone would require an independent saving of about
49.4% of the transition at `u=0.50005`, rising to about 89.0% as `u->0.5`.
Narrowing the factorial interval has not supplied that saving.

## Local validation

Both leaves passed warning-as-error builds, all 14 namespace linters, and
transitive standard-axiom checks of every declaration, including generated
helpers and equations. The optional probe/replay passed 165 finite ball
comparisons, retaining the exact integer-floor length at
`N=4096,16384,65536,262144` and multiplicities one and two.

```sh
lake build RiemannGaussian.ZetaRieszFactorialCutoff \
  RiemannGaussian.ZetaRieszCutoffTransitionAudit --wfail
lake env lean -DwarningAsError=true scripts/CheckRieszFactorialCutoff.lean
../.venv/bin/python scripts/probe_riesz_factorial_cutoff.py
../.venv/bin/python scripts/replay_riesz_factorial_cutoff.py
```

The probes are optional and are not ordinary-CI inputs or Lean assumptions.
No new floor, ceiling, restricted zero exclusion or RH claim is made.
