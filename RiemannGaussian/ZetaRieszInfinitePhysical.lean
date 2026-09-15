/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPhysicalAnnulus

/-!
# Independent bounds for the infinite physical upper tail

Every changing infinite mask of the actual coefficient above X_N squared
is genuinely summable. On 0<u<exp(-2/3), its original normalized response
has the same strictly subunit geometric bound as the finite physical tail.
Uniform finite bounds are proved before the infinite sum is taken.
The signed contribution inside the annulus is not bounded here.
-/

namespace RiemannGaussian.ZetaRieszInfinitePhysical
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszLowerDegreeBounds ZetaRieszPhysicalProductBounds

/-- A bound valid eventually for every moving choice is eventually
uniform over all choices, when the allowance is independent of that choice. -/
theorem eventually_forall_of_all_selections {α : Type*} [Inhabited α] (Q : ℕ → α → Prop)
    (h : ∀ f : ℕ → α, ∀ᶠ N : ℕ in atTop, Q N (f N)) :
    ∀ᶠ N : ℕ in atTop, ∀ a : α, Q N a := by
  let f : ℕ → α := fun N => if hh : ∃ a, ¬ Q N a then Classical.choose hh else default
  filter_upwards [h f] with N hN
  intro a
  by_contra ha
  have hex : ∃ a, ¬ Q N a := ⟨a, ha⟩
  exact (Classical.choose_spec hex) (by simpa only [f, dif_pos hex] using hN)

/-- An arbitrary moving infinite mask of the actual physical upper tail.
The complete coefficient and integer labels remain unchanged on the mask. -/
def upperCoefficient (Q : ℕ → ℕ → Prop) (u : ℝ) (N n : ℕ) : ℂ :=
  if Q N n ∧ ((ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) ^ 2 ≤ n then
    SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n else 0

/-- The actual infinitely selected upper coefficient retains the original
summable divisor majorant, with no convergence premise supplied externally. -/
theorem norm_upperCoefficient_le (Q : ℕ → ℕ → Prop) (u : ℝ) (N n : ℕ) :
    ‖upperCoefficient Q u N n‖ ≤ zetaMoebiusLogMajorant n := by
  unfold upperCoefficient
  split_ifs
  · exact SquarefreeVaughanLogSource.norm_coefficient_le (SquarefreeVaughanLogSource.length_pos u N) n
  · simpa only [norm_zero] using zetaMoebiusLogMajorant_nonneg n

/-- The full polynomial response on every moving infinite upper mask is
genuinely summable at each original moment order. -/
theorem summable_upperCoefficient (Q : ℕ → ℕ → Prop) (u y : ℝ) (N : ℕ) (P : Polynomial ℂ) :
    Summable (fun n : ℕ => upperCoefficient Q u N n *
      zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) :=
  (hasSum_zetaDominatedFilter _ (norm_upperCoefficient_le Q u N) P N (by norm_num)).summable

/-- The finite physical product bound extends to the actual convergent
infinite tail, uniformly over every moving mask. This pays genuine infinite
completion errors without silently exchanging two limits. -/
theorem eventually_norm_infinite_upper_le (Q : ℕ → ℕ → Prop) (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 0 < u) (huh : u < Real.exp (-(2 / 3 : ℝ))) :
    ∀ᶠ N : ℕ in atTop,
      ‖(u : ℂ) ^ (N + 1) * zetaArithmeticFilter (upperCoefficient Q u N) P N
        (3 / 2 + Complex.I * y)‖ ≤
      degreeRate 2 (2 / 3) (3 / 8) (257 / 256) ^ N *
        (u * ZetaArithmeticLogWindow.tiltConstant P (3 / 8) (257 / 256)) := by
  have hfinite : ∀ᶠ N : ℕ in atTop, ∀ S : Finset ℕ,
      ‖(u : ℂ) ^ (N + 1) * ∑ n ∈ S, upperCoefficient Q u N n *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n‖ ≤
      degreeRate 2 (2 / 3) (3 / 8) (257 / 256) ^ N *
        (u * ZetaArithmeticLogWindow.tiltConstant P (3 / 8) (257 / 256)) := by
    apply eventually_forall_of_all_selections
    intro S
    have h := eventually_norm_physical_product_sum_le
      (fun N => (S N).filter (fun n => Q N n ∧
        ((ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) ^ 2 ≤ n)) P y hu
      (by norm_num : (0 : ℝ) ≤ 2 / 3) huh (by norm_num : (0 : ℝ) < 3 / 8)
      (by norm_num : (1 : ℝ) < 257 / 256) (by norm_num) 2
      (fun _ _ hn => physical_product_log_budget (Finset.mem_filter.mp hn).2.2)
    filter_upwards [h] with N hN
    simpa only [upperCoefficient, Finset.sum_filter, ite_mul, zero_mul] using hN
  filter_upwards [hfinite] with N hN
  have ht := ((summable_upperCoefficient Q u y N P).hasSum.mul_left ((u : ℂ) ^ (N + 1))).norm
  apply le_of_tendsto' ht
  intro S
  simpa only [Finset.mul_sum] using hN S

/-- Every moving infinite selection from n>=X_N^2 has independently
vanishing normalized response on 0<u<exp(-2/3). -/
theorem tendsto_infinite_upper (Q : ℕ → ℕ → Prop) (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 0 < u) (huh : u < Real.exp (-(2 / 3 : ℝ))) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) *
      zetaArithmeticFilter (upperCoefficient Q u N) P N (3 / 2 + Complex.I * y)) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (eventually_norm_infinite_upper_le Q P y hu huh)
  have hr0 : 0 ≤ degreeRate 2 (2 / 3) (3 / 8) (257 / 256) := by unfold degreeRate; positivity
  simpa only [zero_mul] using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 two_degree_rate_lt_one).mul_const
    (u * ZetaArithmeticLogWindow.tiltConstant P (3 / 8) (257 / 256))

end
end RiemannGaussian.ZetaRieszInfinitePhysical
