/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RosserSchoenfeldPrimePrimitive

/-!
# Monotone desmoothing of the literal prime sum

The original nonnegative von-Mangoldt events bracket each finite
logarithmic increment by actual Chebyshev values at its endpoints.
These bounds retain every prime-power event, including moving boundaries.
-/

namespace RiemannGaussian.RosserSchoenfeldDesmoothing
noncomputable section
open Real
open RosserSchoenfeldPrimePrimitive

private theorem psi_eq_sum (t : ℝ) :
    Chebyshev.psi (exp t) = ∑ n ∈ Finset.Icc 1 ⌊exp t⌋₊, ArithmeticFunction.vonMangoldt n := by
  unfold Chebyshev.psi
  congr 1

private theorem term_increment_le {a b : ℝ} (hab : a ≤ b) (n : ℕ) :
    term n b-term n a ≤ (b-a)*ArithmeticFunction.vonMangoldt n := by
  have hm : max (b-log n) 0-max (a-log n) 0 ≤ b-a := by
    by_cases ha : log n ≤ a
    · rw [max_eq_left (sub_nonneg.mpr ha), max_eq_left (sub_nonneg.mpr (ha.trans hab))]
      linarith
    · rw [max_eq_right (sub_nonpos.mpr (le_of_not_ge ha)), sub_zero]
      exact max_le (by linarith) (sub_nonneg.mpr hab)
  have hh := mul_le_mul_of_nonneg_left hm (ArithmeticFunction.vonMangoldt_nonneg (n := n))
  unfold term
  nlinarith only [hh]

/-- The upper endpoint's actual Chebyshev sum controls the complete increment. -/
theorem prime_increment_upper {a b : ℝ} (hab : a ≤ b) :
    value b-value a ≤ (b-a)*Chebyshev.psi (exp b) := by
  rw [value_eq_fixed_sum hab, value, ← Finset.sum_sub_distrib, psi_eq_sum, Finset.mul_sum]
  exact Finset.sum_le_sum (fun n _ => term_increment_le hab n)

/-- The lower endpoint's actual Chebyshev sum is paid by the complete increment. -/
theorem prime_increment_lower {a b : ℝ} (hab : a ≤ b) :
    (b-a)*Chebyshev.psi (exp a) ≤ value b-value a := by
  have hsubset : Finset.Icc 1 ⌊exp a⌋₊ ⊆ Finset.Icc 1 ⌊exp b⌋₊ :=
    Finset.Icc_subset_Icc le_rfl (Nat.floor_mono (exp_le_exp.mpr hab))
  have hs : (∑ n ∈ Finset.Icc 1 ⌊exp a⌋₊, term n b) ≤ value b := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun n _ _ => term_nonneg n b)
  have he : (b-a)*Chebyshev.psi (exp a) =
      (∑ n ∈ Finset.Icc 1 ⌊exp a⌋₊, term n b)-value a := by
    rw [psi_eq_sum, Finset.mul_sum, value, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    obtain ⟨hn1, hn⟩ := Finset.mem_Icc.mp hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hl : log n ≤ a := (log_le_iff_le_exp hn0).mpr ((Nat.le_floor_iff (exp_pos a).le).mp hn)
    simp only [term, max_eq_left (sub_nonneg.mpr hl),
      max_eq_left (sub_nonneg.mpr (hl.trans hab))]
    ring
  linarith

end
end RiemannGaussian.RosserSchoenfeldDesmoothing
