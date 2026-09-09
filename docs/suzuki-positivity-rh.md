# The repaired Suzuki-to-RH chain

The canonical-gap branch previously ended at positivity of the literal
`riemannXiSuzukiPsiNonnegative` on `t >= log 2`. Its implication to Mathlib's
`RiemannHypothesis` is now proved in Lean. **The independent arithmetic
inequality remains open; no unconditional RH proof or new zero bound is
claimed.**

The analytic connection follows the positive-Laplace argument used in
[Suzuki's Theorem 1.2](https://arxiv.org/html/2206.03682v3), with genuine
convergence and the repo's exact arithmetic signal checked explicitly:

1. `suzukiPointwiseArchimedean_lt_four_mul_exp_half` keeps the first moving
   Lerch summand. It cancels the reflected exponential and proves that the
   complete Archimedean term is below `4*exp(t/2)` for `t >= 0`.
2. `suzukiChebyshevLogAverageLaplaceSignal_pos_of_psi_nonnegative` turns
   the literal Suzuki tail-positivity premise into positivity of the actual
   logarithmic-average Laplace signal. The prime-free initial interval is
   discharged separately, using the exact finite formula.
3. `Iio_subset_interior_integrableExpSet_of_analytic_mgf` proves the
   positive-measure Landau continuation lemma. Recentring a power series
   preserves its positive moment coefficients; Tonelli then gives genuine
   integrability beyond any proposed finite abscissa.
4. `Iio_zero_subset_interior_integrableExpSet_suzukiPositiveLaplaceMeasure`
   applies that lemma to the actual arithmetic measure. The completed
   response is analytic along the positive real axis because the existing
   eta-mass theorem excludes real xi zeros. No off-axis zero is excluded
   at this step.
5. `nontrivialZero_re_le_half_of_suzuki_signal_nonnegative` clears the xi
   denominator, extends the identity throughout the positive half-plane,
   and contradicts the exact positive multiplicity residue of a hypothetical
   right-half zero. Reflection finishes
   `riemannHypothesis_of_suzuki_psi_nonnegative_tail`.

`SuzukiTransportRH.lean` attaches the current arithmetic interfaces to this
chain. In the notation of the
[cell-cost estimate](suzuki-transport-cell-cost.md), Lean now proves

```text
for every j >= 1:
  sum_{n<j} C_n <= G_0 + sum_{n<j} I_n
                         implies RiemannHypothesis.
```

The terminal theorem is
`riemannHypothesis_of_suzukiFirstTail_signed_work_bound`. The exact entropy
criterion has its own terminal theorem. The finite-head/tail variant retains
the proved common cost tail, and the contrapositive proves that any actual
right-half zero would force a strict signed-work failure at a finite prefix.

These connections remove analytic omissions; they do not establish the
signed-work margin. Cost summability and a small tail alone do not pay for
negative signed work. The previously refuted all-cutoff quadratic majorant
is not used as an arithmetic premise.

Validation is local, with warnings treated as errors, module declaration
lint, and terminal transitive axiom audits. The slice remains uncommitted
under the user's instruction.
