import Development.AutomorphicArithmetic.DedekindLFunctions.LandauZeroFreeCriterion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

theorem mellin_ramp (n : ℕ) (hn : 1 ≤ n) (s : ℂ) (hs : 1 < s.re) :
    ∫ y in Ioi (1 : ℝ), ((max (y / n - 1) 0 : ℝ) : ℂ) * (y : ℂ) ^ (-s - 1) = (n : ℂ) ^ (-s) / (s * (s - 1)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs0 : s ≠ 0 := by
    intro h; rw [h] at hs; simp at hs; linarith
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have : s = 1 := by linear_combination h
    rw [this] at hs; simp at hs
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (s := Ioi (n : ℝ)) measurableSet_Ioi
    (Ioi_subset_Ioi hn1)]
  swap
  · intro y hy
    have hy' : y ≤ n := by simpa using hy.2
    have : y / n - 1 ≤ 0 := by
      rw [sub_nonpos, div_le_one hn0]; exact hy'
    simp [max_eq_right this]
  have hpt : ∀ y ∈ Ioi (n : ℝ), ((max (y / n - 1) 0 : ℝ) : ℂ) * (y : ℂ) ^ (-s - 1)
      = (n : ℂ)⁻¹ * (y : ℂ) ^ (-s) - (y : ℂ) ^ (-s - 1) := by
    intro y hy
    have hy : (n : ℝ) < y := hy
    have hypos : (0 : ℝ) < y := lt_trans hn0 hy
    have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hypos.ne'
    have hm : y / n - 1 ≥ 0 := by
      rw [ge_iff_le, sub_nonneg, le_div_iff₀ hn0]; linarith
    rw [max_eq_left hm, cpow_sub _ _ hyC, cpow_one]
    push_cast
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi hpt]
  have ha1 : (-s).re < -1 := by simp; linarith
  have ha2 : (-s - 1).re < -1 := by simp; linarith
  rw [integral_sub ((integrableOn_Ioi_cpow_of_lt ha1 hn0).const_mul _)
    (integrableOn_Ioi_cpow_of_lt ha2 hn0), integral_const_mul,
    integral_Ioi_cpow_of_lt ha1 hn0, integral_Ioi_cpow_of_lt ha2 hn0]
  have hcast : ((n : ℝ) : ℂ) = (n : ℂ) := by push_cast; rfl
  rw [hcast, cpow_add _ _ hnC, cpow_one, sub_add_cancel]
  have h1s : -s + 1 ≠ 0 := by
    intro h; apply hs1; linear_combination -h
  field_simp
  ring

end Deduction

end
