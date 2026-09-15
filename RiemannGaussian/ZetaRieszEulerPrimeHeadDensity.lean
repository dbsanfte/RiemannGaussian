/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszEulerWindowDeletion
import RiemannGaussian.ZetaPrimeDensityEulerBudget

/-!
# Prime density pays quadratic Euler heads at every original order

The actual Chebyshev prime-density estimate bounds every head through N^2 by an arbitrarily small exponential allowance. This preserves the full original correction filter, physical normalization and frequency integrability, and removes the need for a stride of orders. The complete signed residual still needs its independent joint floor.
-/

namespace RiemannGaussian.ZetaRieszEulerPrimeHeadDensity
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators
open ZetaRieszEulerMultiplier ZetaRieszEulerHead ZetaRieszEulerGrowingHead
open ZetaRieszEulerWindowDeletion ZetaRieszEulerMoments

/-- The exact all-family coefficient product has an exponential bound
in its weighted prime mass, before replacing primes by integer density. -/
theorem head_product_le_exp_mass (S : Finset ℕ) (sigma : ℝ) :
    (∏ p ∈ S, (1 + 2 * Real.exp (-sigma * Real.log p))) ≤
      Real.exp (2 * ∑ p ∈ S, Real.exp (-sigma * Real.log p)) := by
  calc
    _ ≤ ∏ p ∈ S, Real.exp (2 * Real.exp (-sigma * Real.log p)) := by
      apply Finset.prod_le_prod (fun _ _ => by positivity)
      intro p _hp
      have h := Real.add_one_le_exp (2 * Real.exp (-sigma * Real.log p))
      linarith
    _ = _ := by rw [← Real.exp_sum, ← Finset.mul_sum]

/-- The whole half-plane weight is bounded by inverse-square-root
prime mass, with actual primality supplying the nonzero prime hypothesis. -/
theorem head_mass_le_prime_sqrt (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {sigma : ℝ} (hsigma : 1 / 2 ≤ sigma) :
    (∑ p ∈ S, Real.exp (-sigma * Real.log p)) ≤ ∑ p ∈ S, 1 / Real.sqrt p := by
  apply Finset.sum_le_sum
  intro p hp
  simpa only [norm_zetaPrimeFeature, zetaPrimeExpWeight, Complex.ofReal_re] using
    norm_zetaPrimeFeature_le_inv_sqrt (s := (sigma : ℂ)) hsigma (hS p hp).pos

/-- Chebyshev prime density controls every head family together with a
logarithmic saving, uniformly on the full correction half-plane. -/
theorem eventually_head_product_le_prime_density :
    ∀ᶠ b : ℕ in atTop, ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ p ≤ b) →
      ∀ sigma : ℝ, 1 / 2 ≤ sigma →
        (∏ p ∈ S, (1 + 2 * Real.exp (-sigma * Real.log p))) ≤
          Real.exp (16 * Real.sqrt b / Real.log (b + 2)) := by
  filter_upwards [eventually_sum_prime_inv_sqrt_le] with b hb S hS sigma hsigma
  apply (head_product_le_exp_mass S sigma).trans
  apply Real.exp_le_exp.mpr
  have hm := (head_mass_le_prime_sqrt S (fun p hp => (hS p hp).1) hsigma).trans (hb S hS)
  calc
    _ ≤ 2 * (8 * Real.sqrt b / Real.log (b + 2)) := mul_le_mul_of_nonneg_left hm (by norm_num)
    _ = _ := by ring

/-- Heads through the square of the original order have arbitrarily
small exponential cost. The bound is uniform over every prime subset and
over the complete correction half-plane; no stride is needed for this cost. -/
theorem eventually_quadratic_head_product_le {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop, ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ p ≤ n ^ 2) →
      ∀ sigma : ℝ, 1 / 2 ≤ sigma →
        (∏ p ∈ S, (1 + 2 * Real.exp (-sigma * Real.log p))) ≤ Real.exp (eps * n) := by
  have hn : Tendsto (fun n : ℕ => n ^ 2) atTop atTop := by
    apply tendsto_atTop_mono _ tendsto_id
    intro n
    simpa [pow_two] using Nat.le_mul_self n
  have hl := Real.tendsto_log_atTop.comp
    ((tendsto_natCast_atTop_atTop (R := ℝ)).comp hn |>.atTop_add
      (tendsto_const_nhds (x := (2 : ℝ))))
  have hi : Tendsto (fun n : ℕ => 16 * (Real.log (((n ^ 2 : ℕ) : ℝ) + 2))⁻¹)
      atTop (nhds (0 : ℝ)) := by
    simpa only [Function.comp_def, Pi.inv_apply, mul_zero] using hl.inv_tendsto_atTop.const_mul (16 : ℝ)
  filter_upwards [hn.eventually eventually_head_product_le_prime_density,
    hi.eventually (gt_mem_nhds heps)] with n hn he S hS sigma hsigma
  apply (hn S hS sigma hsigma).trans
  apply Real.exp_le_exp.mpr
  have hsqrt : Real.sqrt ((n ^ 2 : ℕ) : ℝ) = (n : ℝ) := by
    rw [Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg n)]
  rw [hsqrt]
  calc
    _ = (16 * (Real.log (((n ^ 2 : ℕ) : ℝ) + 2))⁻¹) * n := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right he.le (Nat.cast_nonneg n)

/-- Every quadratic prime head has an explicit subexponential budget
for the entire original correction filter, including its total log frequency. -/
theorem eventually_quadratic_head_budget_le {eps sigma a : ℝ} (heps : 0 < eps)
    (hsigma : 1 / 2 < sigma) (ha : 0 < a) :
    ∀ᶠ n : ℕ in atTop, ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ p ≤ n ^ 2) → ∀ K : ℕ,
      headResponseBudget S sigma a K ≤ Real.exp (eps * n) *
        (shiftBudget sigma a 1 K * (1 + (((n ^ 2 : ℕ) : ℝ) + 1) ^ 2)) := by
  filter_upwards [eventually_quadratic_head_product_le heps] with n hn S hS K
  apply (headResponseBudget_le_product S hsigma ha K).trans
  apply mul_le_mul (hn S hS sigma hsigma.le)
  · apply (shiftBudget_le_linear hsigma ha (headFrequency_nonneg S) K).trans
    apply mul_le_mul_of_nonneg_left _ (shiftBudget_nonneg hsigma ha 1 K)
    apply add_le_add le_rfl
    exact headFrequency_le_window S (n ^ 2)
      (fun p hp => Finset.mem_range.mpr (Nat.lt_succ_of_le (hS p hp).2))
  · exact shiftBudget_nonneg hsigma ha _ K
  · exact (Real.exp_pos _).le

/-- Every positive strict geometric saving absorbs a sufficiently
small independent exponential head cost. -/
theorem exists_small_exponential_factor {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ∃ eps : ℝ, 0 < eps ∧ r * Real.exp eps < 1 := by
  have hl : Real.log r < 0 := Real.log_neg hr hr1
  refine ⟨-Real.log r / 2, by linarith, ?_⟩
  conv_lhs => lhs; rw [← Real.exp_log hr]
  rw [← Real.exp_add]
  exact Real.exp_lt_one_iff.mpr (by linarith)

/-- The complete quadratic-window frequency cost and original order
factor have a uniform fifth-degree polynomial majorant. -/
theorem quadratic_window_polynomial_le (n : ℕ) :
    (1 + (((n ^ 2 : ℕ) : ℝ) + 1) ^ 2) * ((n : ℝ) + 1) ≤ 2 * ((n : ℝ) + 1) ^ 5 := by
  rw [Nat.cast_pow]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith [pow_nonneg hn 2, pow_nonneg hn 3, pow_nonneg hn 4, pow_nonneg hn 5]

/-- A shifted fixed polynomial still decays against every positive
strict geometric factor, with no subsequence of orders required. -/
theorem tendsto_successor_pow_mul_geometric (k : ℕ) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ k * r ^ n) atTop (nhds 0) := by
  have ht := ((tendsto_pow_const_mul_const_pow_of_lt_one k hr.le hr1).comp
    (tendsto_add_atTop_nat 1)).div_const r
  simpa [Function.comp_def, pow_succ, mul_div_assoc, hr.ne'] using ht

/-- Every quadratic prime-head family preserves original-order
correction decay, with eventual large-prime support and arbitrary physical
lengths above a positive base. Prime density removes the earlier stride. -/
theorem tendsto_quadratic_headFilteredResponse (S Q : ℕ → Finset ℕ)
    (hS : ∀ n p, p ∈ S n → p.Prime ∧ p ≤ n ^ 2)
    (h16 : ∀ᶠ n : ℕ in atTop, ∀ p ∈ Q n, 16 ≤ p)
    (P : Polynomial ℂ) (L : ℕ → ℝ) {a : ℝ} (ha : 0 < a) (hL : ∀ n, a ≤ L n)
    {s : ℂ} {R u : ℝ} (hu : 0 < u) (huR : u < R) (hhalf : 1 / 2 < s.re - R) :
    Tendsto (fun n : ℕ => (u : ℂ) ^ (n + 1) *
      headFilteredResponse (S n) (Q n) P n s (L n)) atTop (nhds 0) := by
  have hR : 0 < R := hu.trans huR
  let r : ℝ := u / R
  have hr : 0 < r := div_pos hu hR
  have hr1 : r < 1 := (div_lt_one hR).mpr huR
  obtain ⟨eps, heps, hsmall⟩ := exists_small_exponential_factor hr hr1
  let C : ℝ := shiftBudget (s.re - R) a 1 0 * filterRadiusCost P R
  have hC : 0 ≤ C := mul_nonneg (shiftBudget_nonneg hhalf ha 1 0)
    (by unfold filterRadiusCost; positivity)
  have hb : ∀ᶠ n : ℕ in atTop, ‖(u : ℂ) ^ (n + 1) *
      headFilteredResponse (S n) (Q n) P n s (L n)‖ ≤
      (2 * C * r) * (((n : ℝ) + 1) ^ 5 * (r * Real.exp eps) ^ n) := by
    filter_upwards [eventually_quadratic_head_budget_le heps hhalf ha, h16] with n hn h16n
    apply (norm_scaled_headFilteredResponse_le (S n) (Q n) h16n P n hR hu.le hhalf
      0 (fun _ _ => Nat.zero_le _) ha (hL n)).trans
    calc
      _ ≤ (Real.exp (eps * n) *
          (shiftBudget (s.re - R) a 1 0 * (1 + (((n ^ 2 : ℕ) : ℝ) + 1) ^ 2)) *
            filterRadiusCost P R) * (((n : ℝ) + 1) * r ^ (n + 1)) := by
        apply mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hn (S n) (hS n) 0)
            (by unfold filterRadiusCost; positivity))
        positivity
      _ = (C * Real.exp (eps * n)) *
          ((1 + (((n ^ 2 : ℕ) : ℝ) + 1) ^ 2) * ((n : ℝ) + 1)) * r ^ (n + 1) := by
        dsimp [C]
        ring
      _ ≤ (C * Real.exp (eps * n)) * (2 * ((n : ℝ) + 1) ^ 5) * r ^ (n + 1) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (quadratic_window_polynomial_le n) (by positivity))
          (pow_nonneg hr.le _)
      _ = _ := by
        rw [show eps * (n : ℝ) = (n : ℝ) * eps by ring, Real.exp_nat_mul, pow_succ, mul_pow]
        ring
  apply squeeze_zero_norm' hb
  simpa only [mul_zero] using
    (tendsto_successor_pow_mul_geometric 5 (mul_pos hr (Real.exp_pos eps)) hsmall).const_mul (2 * C * r)

end
end RiemannGaussian.ZetaRieszEulerPrimeHeadDensity
