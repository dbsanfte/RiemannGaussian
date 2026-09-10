/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaMoebiusMultipleDecay
import RiemannGaussian.ChebyshevMoebiusCancellation

/-!
# Retaining the divisor scale in the complete multiple-sector response

The least-common-multiple feature splits into the original divisor feature
and its full complex logarithmic displacement. Paying for the displacement
leaves the divisor's inverse square-root weight intact. Summing those weights
improves the complete multiplier and arithmetic-family costs from a linear
cutoff to a square-root cutoff, uniformly in every selected factor.
-/

open Complex Filter Topology
open scoped Classical ArithmeticFunction.Moebius

namespace RiemannGaussian
noncomputable section

/-- The physical intersection feature factors exactly, with both
complex phases and the full logarithmic displacement retained. -/
theorem zetaPrimeFeature_lcm_eq_offset (d P : ℕ) (s : ℂ) :
    zetaPrimeFeature s (Nat.lcm d P) = zetaPrimeFeature s d *
      Complex.exp (-s * (zetaMultipleLogOffset d P : ℂ)) := by
  unfold zetaPrimeFeature zetaMultipleLogOffset
  rw [← Complex.exp_add, Complex.ofReal_sub]
  congr 1
  ring

/-- On the closed right half-strip, a positive divisor retains its
inverse square-root weight. -/
theorem norm_zetaPrimeFeature_le_inv_sqrt {s : ℂ} (hs : 1 / 2 ≤ s.re)
    {d : ℕ} (hd : 0 < d) : ‖zetaPrimeFeature s d‖ ≤ 1 / Real.sqrt d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have he : Real.exp (Real.log (d : ℝ) / 2) = Real.sqrt d := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hdR]
    congr 1
    ring
  rw [norm_zetaPrimeFeature, zetaPrimeExpWeight]
  calc
    _ ≤ Real.exp (-(Real.log d / 2)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [Real.log_natCast_nonneg d]
    _ = _ := by rw [Real.exp_neg, he, one_div]

private theorem offset_exp_log_le_two {s x : ℝ} (hs : 1 / 2 ≤ s) (hx : 0 ≤ x) :
    Real.exp (-s * x) * x ≤ 2 := by
  have he : x / 2 ≤ Real.exp (x / 2) := by linarith [Real.add_one_le_exp (x / 2)]
  have hm := mul_le_mul_of_nonneg_right he (Real.exp_pos (-x / 2)).le
  have hp : Real.exp (x / 2) * Real.exp (-x / 2) = 1 := by
    rw [← Real.exp_add, show x / 2 + -x / 2 = 0 by ring, Real.exp_zero]
  rw [hp] at hm
  calc
    _ ≤ Real.exp (-x / 2) * x :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith)) hx
    _ ≤ 2 := by nlinarith

/-- Paying for the intersection's logarithmic displacement leaves the
original divisor weight intact. This is uniform in the factor and its valuations. -/
theorem norm_zetaPrimeFeature_lcm_mul_offset_le {s : ℂ} (hs : 1 / 2 ≤ s.re)
    {d P : ℕ} (hd : 0 < d) (hP : 0 < P) :
    ‖zetaPrimeFeature s (Nat.lcm d P)‖ * zetaMultipleLogOffset d P ≤
      2 / Real.sqrt d := by
  have hx := (zetaMultipleLogOffset_bounds hd hP).1
  have he : ‖Complex.exp (-s * (zetaMultipleLogOffset d P : ℂ))‖ =
      Real.exp (-s.re * zetaMultipleLogOffset d P) := by
    rw [Complex.norm_exp]
    congr 1
    simp
  rw [zetaPrimeFeature_lcm_eq_offset, norm_mul, he, mul_assoc]
  calc
    _ ≤ ‖zetaPrimeFeature s d‖ * 2 :=
      mul_le_mul_of_nonneg_left (offset_exp_log_le_two hs hx) (norm_nonneg _)
    _ ≤ (1 / Real.sqrt d) * 2 :=
      mul_le_mul_of_nonneg_right (norm_zetaPrimeFeature_le_inv_sqrt hs hd) (by norm_num)
    _ = _ := by ring

/-- The two entire multipliers of the actual multiple sector have
square-root cutoff cost. No cancellation hypothesis on Möbius is used. -/
theorem norm_zetaMoebiusMultipleMultipliers_le_sqrt (D : ℕ) {P : ℕ} (hP : 0 < P)
    {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖zetaMoebiusMultipleDerivativeMultiplier D P s‖ ≤ 2 * Real.sqrt D ∧
      ‖zetaMoebiusMultipleValueMultiplier D P s‖ ≤ 4 * Real.sqrt D := by
  have hm (d : ℕ) : ‖(μ d : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
  constructor
  · rw [zetaMoebiusMultipleDerivativeMultiplier, norm_neg]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ d ∈ Finset.Icc 1 D, 1 / Real.sqrt d := by
        apply Finset.sum_le_sum
        intro d hd
        have hd0 := (Finset.mem_Icc.mp hd).1
        have hle : Real.sqrt d ≤ Real.sqrt (Nat.lcm d P) :=
          Real.sqrt_le_sqrt (by
            exact_mod_cast (Nat.le_of_dvd (Nat.lcm_pos hd0 hP) (Nat.dvd_lcm_left d P)))
        rw [norm_mul]
        calc
          _ ≤ 1 * (1 / Real.sqrt (Nat.lcm d P)) :=
            mul_le_mul (hm d) (norm_zetaPrimeFeature_le_inv_sqrt hs (Nat.lcm_pos hd0 hP))
              (norm_nonneg _) (by norm_num)
          _ ≤ 1 / Real.sqrt d := by
            rw [one_mul]
            exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by exact_mod_cast hd0)) hle
      _ ≤ _ := sum_inv_sqrt_Icc_le D
  · rw [zetaMoebiusMultipleValueMultiplier, norm_neg]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ d ∈ Finset.Icc 1 D, 2 / Real.sqrt d := by
        apply Finset.sum_le_sum
        intro d hd
        have hd0 := (Finset.mem_Icc.mp hd).1
        have hx := (zetaMultipleLogOffset_bounds hd0 hP).1
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hx]
        calc
          _ ≤ 1 * ‖zetaPrimeFeature s (Nat.lcm d P)‖ * zetaMultipleLogOffset d P := by
            gcongr
            exact hm d
          _ ≤ 2 / Real.sqrt d := by
            simpa only [one_mul] using norm_zetaPrimeFeature_lcm_mul_offset_le hs hd0 hP
      _ = 2 * ∑ d ∈ Finset.Icc 1 D, 1 / Real.sqrt d := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        ring
      _ ≤ _ := by nlinarith [sum_inv_sqrt_Icc_le D]

/-- Every polynomial filter of the actual sector inherits the
square-root cutoff saving, uniformly over all moment orders and positive factors. -/
theorem exists_zetaMoebiusMultipleFilter_sqrt_bound (y : ℝ) (hy : 1 < |y|) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Polynomial ℂ) (D P N : ℕ), 0 < P →
      ‖zetaMoebiusMultipleFilter p D P N (3 / 2 + I * y)‖ ≤
        C * Real.sqrt D * ∑ k ∈ p.support, ‖p.coeff k‖ := by
  obtain ⟨C, hC, hb⟩ := exists_zetaEntireMultiplier_filter_bound y hy
  refine ⟨6 * C, by positivity, ?_⟩
  intro p D P N hP
  obtain ⟨hf, hg⟩ := differentiable_zetaMoebiusMultipleMultipliers D P
  have h := hb _ _ hf hg (2 * Real.sqrt D) (4 * Real.sqrt D) (by positivity) (by positivity)
    (fun s hs ↦ (norm_zetaMoebiusMultipleMultipliers_le_sqrt D hP hs).1)
    (fun s hs ↦ (norm_zetaMoebiusMultipleMultipliers_le_sqrt D hP hs).2) p N
  exact h.trans_eq (by ring)

/-- Every actual finite complex factor family has a square-root cutoff
cost times its total coefficient mass. All overlapping sectors remain signed
inside the arithmetic expression; genuine summability is supplied upstream. -/
theorem exists_zetaMoebiusMultipleFamily_sqrt_bound (y : ℝ) (hy : 1 < |y|) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Polynomial ℂ) (D N : ℕ) (S : Finset ℕ) (w : ℕ → ℂ),
      (∀ P ∈ S, 0 < P ∧ P ≠ 1 ∧ ¬IsPrimePow P) →
      ‖∑ P ∈ S, w P * ∑' n, zetaMoebiusMultipleCoefficient D P n *
        zetaPrimeFilterKernel p N (3 / 2 + I * y) n‖ ≤
        C * Real.sqrt D * (∑ k ∈ p.support, ‖p.coeff k‖) * ∑ P ∈ S, ‖w P‖ := by
  obtain ⟨C, hC, hb⟩ := exists_zetaMoebiusMultipleFilter_sqrt_bound y hy
  refine ⟨C, hC, ?_⟩
  intro p D N S w hS
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ P ∈ S, ‖w P‖ * (C * Real.sqrt D * ∑ k ∈ p.support, ‖p.coeff k‖) := by
      apply Finset.sum_le_sum
      intro P hP
      obtain ⟨hP0, hP1, hmix⟩ := hS P hP
      rw [(hasSum_zetaMoebiusMultipleFilter p D N hP0 hP1 hmix (by norm_num)).tsum_eq, norm_mul]
      exact mul_le_mul_of_nonneg_left (hb p D P N hP0) (norm_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

end
end RiemannGaussian
