import RiemannGaussian.EtaCurrentArithmeticEnvelope
import Mathlib.Analysis.SumIntegralComparisons

/-!
# Finite power sums for the actual current's horizontal displacement

Both completed endpoint powers are bounded by the slower exponent
`|2 Re rho - 1| - 1`. An integral comparison gives its explicit finite
sum. The zero-displacement case is kept separate to avoid division by
zero and to preserve the exact critical-line cancellation upstream.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- Twice the actual zero's horizontal distance from the critical line. -/
def pairedEtaCurrentHorizontalDisplacement (rho : NontrivialZetaZero) : ℝ := |2 * rho.1.re - 1|

/-- The actual horizontal displacement is nonnegative and strictly less than one. -/
theorem pairedEtaCurrentHorizontalDisplacement_bounds (rho : NontrivialZetaZero) :
    0 ≤ pairedEtaCurrentHorizontalDisplacement rho ∧ pairedEtaCurrentHorizontalDisplacement rho < 1 := by
  constructor
  · exact abs_nonneg _
  · exact abs_lt.mpr ⟨by linarith [NontrivialZetaZero.zero_lt_re rho], by linarith [NontrivialZetaZero.re_lt_one rho]⟩

/-- Reflection preserves the actual horizontal displacement. -/
theorem pairedEtaCurrentHorizontalDisplacement_conjugatePartner (rho : NontrivialZetaZero) :
    pairedEtaCurrentHorizontalDisplacement (NontrivialZetaZero.conjugatePartner rho) =
      pairedEtaCurrentHorizontalDisplacement rho := by
  unfold pairedEtaCurrentHorizontalDisplacement
  simp only [NontrivialZetaZero.conjugatePartner_coe, Complex.sub_re, Complex.one_re, Complex.conj_re]
  rw [show 2 * (1 - rho.1.re) - 1 = -(2 * rho.1.re - 1) by ring, abs_neg]

/-- Away from the critical line, the displacement denominator is strictly positive. -/
theorem pairedEtaCurrentHorizontalDisplacement_pos (rho : NontrivialZetaZero) (hrho : rho.1.re ≠ 1 / 2) :
    0 < pairedEtaCurrentHorizontalDisplacement rho := by
  apply abs_pos.mpr
  intro h
  apply hrho
  linarith

/-- Each actual squared endpoint decay is bounded by the slower
horizontal displacement power at the same arithmetic cutoff. -/
theorem pairedEtaCurrentMomentDecay_sq_le_displacement_rpow (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCurrentMomentDecay rho N ^ 2 ≤
      (N + 1 : ℝ) ^ (pairedEtaCurrentHorizontalDisplacement rho - 1) := by
  have hx : 0 < (N + 1 : ℝ) := by positivity
  have hq : 0 < ((2 * (N + 1) + 1 : ℕ) : ℝ) := by positivity
  have hs := NontrivialZetaZero.zero_lt_re rho
  calc
    _ = (((2 * (N + 1) + 1 : ℕ) : ℝ) ^ (-2 * rho.1.re)) := by
      unfold pairedEtaCurrentMomentDecay
      rw [show -2 * rho.1.re = (-rho.1.re) * 2 by ring, Real.rpow_mul hq.le, Real.rpow_two]
    _ ≤ (N + 1 : ℝ) ^ (-2 * rho.1.re) :=
      Real.rpow_le_rpow_of_nonpos hx
        (by exact_mod_cast (show N + 1 ≤ 2 * (N + 1) + 1 by omega)) (by linarith)
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
      (by unfold pairedEtaCurrentHorizontalDisplacement; linarith [neg_le_abs (2 * rho.1.re - 1)])

/-- The two actual completed endpoint channels share one explicit
displacement-power majorant, with their completion constants retained. -/
theorem pairedEtaCurrentDoubleDecayEnvelope_le_displacement_rpow (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCurrentDoubleDecayEnvelope rho N ≤
      (pairedEtaCurrentMomentConstant (NontrivialZetaZero.conjugatePartner rho) ^ 2 + pairedEtaCurrentMomentConstant rho ^ 2) *
        (N + 1 : ℝ) ^ (pairedEtaCurrentHorizontalDisplacement rho - 1) := by
  have hp := pairedEtaCurrentMomentDecay_sq_le_displacement_rpow (NontrivialZetaZero.conjugatePartner rho) N
  rw [pairedEtaCurrentHorizontalDisplacement_conjugatePartner] at hp
  exact (add_le_add (mul_le_mul_of_nonneg_left hp (sq_nonneg _))
    (mul_le_mul_of_nonneg_left (pairedEtaCurrentMomentDecay_sq_le_displacement_rpow rho N) (sq_nonneg _))).trans_eq
      (by ring)

/-- An explicit finite power-sum bound throughout the strict integrable
range `-1 < r ≤ 0`, including the initial arithmetic term. -/
theorem sum_range_nat_add_one_rpow_le {r : ℝ} (hr : -1 < r) (hr0 : r ≤ 0) (K : ℕ) :
    (∑ N ∈ Finset.range K, (N + 1 : ℝ) ^ r) ≤ (K + 1 : ℝ) ^ (r + 1) / (r + 1) := by
  have hant : AntitoneOn (fun x : ℝ ↦ x ^ r) (Icc 1 (1 + (K : ℝ))) := by
    intro a ha b hb hab
    exact Real.rpow_le_rpow_of_nonpos (by linarith [ha.1]) hab hr0
  have hi := hant.sum_le_integral
  have hsum : (∑ N ∈ Finset.range K, (N + 1 : ℝ) ^ r) ≤
      (∑ N ∈ Finset.range K, (1 + ((N + 1 : ℕ) : ℝ)) ^ r) + 1 := by
    have h := Finset.sum_range_succ' (fun N : ℕ ↦ (N + 1 : ℝ) ^ r) K
    rw [Finset.sum_range_succ] at h
    simp only [Nat.cast_zero, zero_add, Real.one_rpow, Nat.cast_add, Nat.cast_one] at h
    have he : (∑ N ∈ Finset.range K, ((N : ℝ) + 1 + 1) ^ r) =
        ∑ N ∈ Finset.range K, (1 + ((N : ℝ) + 1)) ^ r := by
      apply Finset.sum_congr rfl
      intro N _
      rw [add_comm 1 ((N : ℝ) + 1)]
    rw [he] at h
    have hn : 0 ≤ (K + 1 : ℝ) ^ r := Real.rpow_nonneg (by positivity) _
    simp only [Nat.cast_add, Nat.cast_one]
    linarith
  calc
    _ ≤ (∫ x : ℝ in (1 : ℝ)..1 + (K : ℝ), x ^ r) + 1 :=
      hsum.trans (add_le_add hi le_rfl)
    _ = ((K + 1 : ℝ) ^ (r + 1) - 1) / (r + 1) + 1 := by
      rw [integral_rpow (Or.inl hr), Real.one_rpow, add_comm 1 (K : ℝ)]
    _ ≤ _ := by
      have hr1 : 0 < r + 1 := by linarith
      apply (le_div_iff₀ hr1).2
      rw [add_mul, div_mul_cancel₀ _ hr1.ne']
      linarith

end

end RiemannGaussian
