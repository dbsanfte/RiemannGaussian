/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.FiniteFourierResonance

/-!
# Absolute difference budgets for finite Fourier interactions

An absolute mass bound on one vector and a summable difference bound on
the other control every region with a fixed symbol gap. The cyclic second
difference keeps its exact interior formula and all three exceptional
indices before its boundary estimate is taken.
-/

open Complex
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- A symbol gap and two absolute masses give a bound independent of
the size of the cyclic group. The complete difference order is explicit. -/
theorem norm_finiteFourierPart_le_sum_norm_difference {q : ℕ} [NeZero q]
    (a f : ZMod q → ℂ) (S : Finset (ZMod q)) (r : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hS : ∀ k ∈ S, δ ≤ ‖cyclicDifferenceSymbol k‖) :
    ‖finiteFourierPart a f S‖ ≤ δ⁻¹ ^ r * (∑ j, ‖a j‖) *
      ∑ j, ‖(cyclicDifference^[r] f) j‖ := by
  have ha : 0 ≤ ∑ j, ‖a j‖ := Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)
  have hf : 0 ≤ ∑ j, ‖(cyclicDifference^[r] f) j‖ :=
    Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  apply (norm_finiteFourierPart_sq_le_physical_difference a f S r hδ hS).trans
  calc
    _ ≤ (δ⁻¹ ^ r) ^ 2 * (∑ j, ‖a j‖) ^ 2 * (∑ j, ‖(cyclicDifference^[r] f) j‖) ^ 2 := by
      gcongr
      · exact Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ ↦ norm_nonneg _)
      · exact Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ ↦ norm_nonneg _)
    _ = _ := by ring

/-- The signed cyclic second difference before any norm estimate. -/
theorem cyclicDifference_twice {q : ℕ} (f : ZMod q → ℂ) (j : ZMod q) :
    (cyclicDifference^[2] f) j = f (j + 2) - 2 * f (j + 1) + f j := by
  change (f (j + 1 + 1) - f (j + 1)) - (f (j + 1) - f j) = _
  rw [show j + 1 + 1 = j + 2 by ring]
  ring

/-- The complete absolute second-difference mass retains its initial
sample and both terminal cyclic terms exactly. -/
theorem sum_norm_cyclicDifference_twice_eq (M : ℕ) (hM : 2 ≤ M)
    (f : ZMod (M + 1) → ℂ) (h0 : f 0 = 0) (h1 : f 1 = 0) :
    (∑ j, ‖(cyclicDifference^[2] f) j‖) =
      (∑ n ∈ Finset.Ico 1 (M - 1),
        ‖f ((n + 2 : ℕ) : ZMod (M + 1)) - 2 * f ((n + 1 : ℕ) : ZMod (M + 1)) + f n‖) +
        ‖f 2‖ + ‖f (M - 1 : ℕ) - 2 * f M‖ + ‖f M‖ := by
  let g : ℕ → ℝ := fun n ↦
    ‖f ((n + 2 : ℕ) : ZMod (M + 1)) - 2 * f ((n + 1 : ℕ) : ZMod (M + 1)) + f n‖
  have he (j : ZMod (M + 1)) : ‖(cyclicDifference^[2] f) j‖ = g j.val := by
    rw [cyclicDifference_twice]
    simp [g, Nat.cast_add]
  simp_rw [he]
  change (∑ j : Fin (M + 1), g j.val) = _
  rw [Fin.sum_univ_eq_sum_range g]
  have hs := Finset.sum_range_succ g (M - 1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ M),
    Finset.sum_range_eq_add_Ico g (by omega : 0 < M - 1)] at hs
  rw [Finset.sum_range_succ, hs]
  have hg0 : g 0 = ‖f 2‖ := by simp [g, h0, h1]
  have hgM : g M = ‖f M‖ := by
    have he1 : ((M + 1 : ℕ) : ZMod (M + 1)) = 0 := by simp
    have he2 : ((M + 2 : ℕ) : ZMod (M + 1)) = 1 := by
      rw [show M + 2 = (M + 1) + 1 by omega, Nat.cast_add, he1]
      simp
    simp only [g, he1, he2, h0, h1, mul_zero, sub_zero, zero_add]
  have hgM1 : g (M - 1) = ‖f (M - 1 : ℕ) - 2 * f M‖ := by
    have he1 : M - 1 + 1 = M := by omega
    have he2 : M - 1 + 2 = M + 1 := by omega
    simp only [g, he1, he2, ZMod.natCast_self, h0, zero_sub]
    congr 1
    ring
  rw [hg0, hgM, hgM1]
  ring

/-- Only three exceptional indices are paid for in this bound; the
number of interior samples never multiplies the boundary allowance. -/
theorem sum_norm_cyclicDifference_twice_le (M : ℕ) (hM : 2 ≤ M)
    (f : ZMod (M + 1) → ℂ) (h0 : f 0 = 0) (h1 : f 1 = 0) :
    (∑ j, ‖(cyclicDifference^[2] f) j‖) ≤
      (∑ n ∈ Finset.Ico 1 (M - 1),
        ‖f ((n + 2 : ℕ) : ZMod (M + 1)) - 2 * f ((n + 1 : ℕ) : ZMod (M + 1)) + f n‖) +
        ‖f 2‖ + ‖f (M - 1 : ℕ)‖ + 3 * ‖f M‖ := by
  rw [sum_norm_cyclicDifference_twice_eq M hM f h0 h1]
  have h := norm_sub_le (f (M - 1 : ℕ)) (2 * f M)
  norm_num only [norm_mul, norm_ofNat] at h
  linarith

end
end RiemannGaussian
