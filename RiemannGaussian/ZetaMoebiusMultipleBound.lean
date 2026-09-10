/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaMoebiusMultipleResponse

/-!
# A factor-independent bound for complete multiple sectors

The actual least-common-multiple feature controls its logarithmic
displacement on `Re s ≥ 1/2`. Retaining this scale until after the
logarithmic bound removes every dependence on the chosen factor.
-/

open Complex
open scoped Classical ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- The natural-index Dirichlet feature pays for its own logarithm,
uniformly in the entire closed right half of the critical strip. -/
theorem norm_zetaPrimeFeature_mul_log_le_two {s : ℂ} (hs : 1 / 2 ≤ s.re) (n : ℕ) :
    ‖zetaPrimeFeature s n‖ * Real.log n ≤ 2 := by
  let x := Real.log n
  have hx : 0 ≤ x := Real.log_natCast_nonneg n
  have he : x / 2 ≤ Real.exp (x / 2) := by linarith [Real.add_one_le_exp (x / 2)]
  have he' := mul_le_mul_of_nonneg_right he (Real.exp_pos (-x / 2)).le
  have hex : Real.exp (x / 2) * Real.exp (-x / 2) = 1 := by
    rw [← Real.exp_add, show x / 2 + -x / 2 = 0 by ring, Real.exp_zero]
  rw [hex] at he'
  rw [norm_zetaPrimeFeature, zetaPrimeExpWeight]
  calc
    _ ≤ Real.exp (-x / 2) * x := by
      apply mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr _) hx
      dsimp [x]
      nlinarith
    _ ≤ 2 := by nlinarith

/-- The offset is nonnegative and no greater than the full physical
logarithm of the intersection index. -/
theorem zetaMultipleLogOffset_bounds {d P : ℕ} (hd : 0 < d) (hP : 0 < P) :
    0 ≤ zetaMultipleLogOffset d P ∧
      zetaMultipleLogOffset d P ≤ Real.log (Nat.lcm d P) := by
  have hle := Nat.le_of_dvd (Nat.lcm_pos hd hP) (Nat.dvd_lcm_left d P)
  have hlog := Real.log_le_log (x := (d : ℝ)) (y := (Nat.lcm d P : ℝ))
    (by exact_mod_cast hd) (by exact_mod_cast hle)
  have hdlog := Real.log_natCast_nonneg d
  unfold zetaMultipleLogOffset
  constructor <;> linarith

/-- Both finite least-common-multiple multipliers are entire. -/
theorem differentiable_zetaMoebiusMultipleMultipliers (D P : ℕ) :
    Differentiable ℂ (zetaMoebiusMultipleDerivativeMultiplier D P) ∧
      Differentiable ℂ (zetaMoebiusMultipleValueMultiplier D P) := by
  constructor
  · unfold zetaMoebiusMultipleDerivativeMultiplier zetaPrimeFeature
    fun_prop
  · unfold zetaMoebiusMultipleValueMultiplier zetaPrimeFeature
    fun_prop

/-- Retaining the physical Dirichlet scale makes both bounds independent
of the factor, including all of its prime valuations and size. -/
theorem norm_zetaMoebiusMultipleMultipliers_le (D : ℕ) {P : ℕ} (hP : 0 < P)
    {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖zetaMoebiusMultipleDerivativeMultiplier D P s‖ ≤ D ∧
      ‖zetaMoebiusMultipleValueMultiplier D P s‖ ≤ 2 * D := by
  have hm (d : ℕ) : ‖(μ d : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
  constructor
  · rw [zetaMoebiusMultipleDerivativeMultiplier, norm_neg]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _d ∈ Finset.Icc 1 D, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro d _
        rw [norm_mul]
        exact (mul_le_mul (hm d) (norm_zetaPrimeFeature_le_one (by linarith) _) (norm_nonneg _)
          (by norm_num)).trans_eq (by norm_num)
      _ = D := by simp
  · rw [zetaMoebiusMultipleValueMultiplier, norm_neg]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _d ∈ Finset.Icc 1 D, (2 : ℝ) := by
        apply Finset.sum_le_sum
        intro d hd
        obtain ⟨h0, hL⟩ := zetaMultipleLogOffset_bounds (Finset.mem_Icc.mp hd).1 hP
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg h0]
        calc
          _ ≤ 1 * ‖zetaPrimeFeature s (Nat.lcm d P)‖ * Real.log (Nat.lcm d P) := by gcongr; exact hm d
          _ ≤ 2 := by simpa only [one_mul] using norm_zetaPrimeFeature_mul_log_le_two hs (Nat.lcm d P)
      _ = 2 * D := by simp; ring

/-- Filtered moments of the complete multiple-sector response. -/
def zetaMoebiusMultipleFilter (p : Polynomial ℂ) (D P N : ℕ) (s : ℂ) : ℂ :=
  zetaMomentSequenceFilter p (fun k ↦ signedTaylorMoment k (zetaMoebiusMultipleResponse D P) s) N

/-- A single ordinate-dependent constant bounds every factor, cutoff,
order, and polynomial filter. The bound does not grow with the factor. -/
theorem exists_zetaMoebiusMultipleFilter_bound (y : ℝ) (hy : 1 < |y|) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Polynomial ℂ) (D P N : ℕ), 0 < P →
      ‖zetaMoebiusMultipleFilter p D P N (3 / 2 + I * y)‖ ≤
        C * D * ∑ k ∈ p.support, ‖p.coeff k‖ := by
  obtain ⟨C, hC, hb⟩ := exists_zetaEntireMultiplier_filter_bound y hy
  refine ⟨3 * C, by positivity, ?_⟩
  intro p D P N hP
  obtain ⟨hf, hg⟩ := differentiable_zetaMoebiusMultipleMultipliers D P
  have h := hb _ _ hf hg D (2 * D) (by positivity) (by positivity)
    (fun s hs ↦ (norm_zetaMoebiusMultipleMultipliers_le D hP hs).1)
    (fun s hs ↦ (norm_zetaMoebiusMultipleMultipliers_le D hP hs).2) p N
  exact h.trans_eq (by ring)

end
end RiemannGaussian
