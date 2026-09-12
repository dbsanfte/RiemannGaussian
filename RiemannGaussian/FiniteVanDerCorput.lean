/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.FiniteShiftCorrelation

/-!
# Weighted van der Corput differencing with signed correlations

The Toeplitz matrix of complete translates has an exact triangular-lag
expansion. This proves the finite van der Corput inequality with factor
`N+H-1` and arbitrary complex amplitudes. The sharper signed real form
precedes the usual absolute-correlation bound, and the complete complex
correlations remain available. This is the finite differencing ingredient
of the exponential-sum route to larger zero-free regions, not a derivative
test or an estimate for the unresolved arithmetic correlations.

For the classical unweighted inequality see Yang, *Explicit bounds on
zeta(s) in the critical strip and a zero-free region*, JMAA 2024,
Lemma 2.3, https://arxiv.org/html/2301.03165v2.
-/

namespace RiemannGaussian.FiniteVanDerCorput
noncomputable section
open Complex Filter Topology FiniteShiftCorrelation
open scoped Classical

private theorem sum_reverse_lags (g : ℤ → ℝ) (H : ℕ) :
    (∑ k ∈ Finset.range H, g ((H : ℤ) - k)) =
      ∑ k ∈ Finset.range H, g ((k : ℤ) + 1) := by
  calc
    _ = ∑ k ∈ Finset.range H, g (((H - 1 - k : ℕ) : ℤ) + 1) := by
      apply Finset.sum_congr rfl
      intro k hk
      congr 1
      have hk' := Finset.mem_range.mp hk
      omega
    _ = _ := Finset.sum_range_reflect (fun k : ℕ ↦ g ((k : ℤ) + 1)) H

/-- Every real even Toeplitz form has its exact triangular-lag expansion.
The final lag has coefficient zero; no endpoint is approximated. -/
theorem toeplitz_sum_eq (g : ℤ → ℝ) (hg : ∀ h : ℤ, g (-h) = g h) (H : ℕ) :
    (∑ h ∈ Finset.range H, ∑ k ∈ Finset.range H, g ((h : ℤ) - k)) =
      (H : ℝ) * g 0 +
        2 * ∑ h ∈ Finset.range H, ((H : ℝ) - h - 1) * g ((h : ℤ) + 1) := by
  induction H with
  | zero => simp
  | succ H ih =>
    have hs : (∑ h ∈ Finset.range H, g ((h : ℤ) - H)) =
        ∑ h ∈ Finset.range H, g ((H : ℤ) - h) := by
      apply Finset.sum_congr rfl
      intro h _
      rw [show (h : ℤ) - H = -((H : ℤ) - h) by ring, hg]
    have hD : (∑ h ∈ Finset.range (H + 1), ∑ k ∈ Finset.range (H + 1),
        g ((h : ℤ) - k)) =
          (∑ h ∈ Finset.range H, ∑ k ∈ Finset.range H, g ((h : ℤ) - k)) +
            2 * (∑ h ∈ Finset.range H, g ((h : ℤ) + 1)) + g 0 := by
      simp only [Finset.sum_range_succ, Finset.sum_add_distrib, sub_self]
      rw [hs, sum_reverse_lags]
      ring
    have hW : (∑ h ∈ Finset.range (H + 1),
        (((H + 1 : ℕ) : ℝ) - h - 1) * g ((h : ℤ) + 1)) =
          (∑ h ∈ Finset.range H, ((H : ℝ) - h - 1) * g ((h : ℤ) + 1)) +
            ∑ h ∈ Finset.range H, g ((h : ℤ) + 1) := by
      rw [Finset.sum_range_succ]
      simp only [Nat.cast_add, Nat.cast_one]
      rw [show (H : ℝ) + 1 - H - 1 = 0 by ring, zero_mul, add_zero,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun h _ ↦ by ring)
    rw [hD, ih, hW]
    push_cast
    ring

/-- The complete shifted energy equals the signed triangular form of
the original finite sequence, including the full diagonal mass. -/
theorem shifted_energy_eq {f : ℤ → ℂ} (hf : Function.HasFiniteSupport f) (H : ℕ) :
    (∑' n : ℤ, ‖shiftedSum f H n‖ ^ 2) =
      (H : ℝ) * (∑' n : ℤ, ‖f n‖ ^ 2) +
        2 * ∑ h ∈ Finset.range H, ((H : ℝ) - h - 1) * (correlation f ((h : ℤ) + 1)).re := by
  rw [shiftedSum_energy hf,
    toeplitz_sum_eq (fun h ↦ (correlation f h).re) (correlation_neg_re f), correlation_zero hf]

/-- The full signed form is nonnegative because it is the energy of
the original translated family. Individual correlations need not be positive. -/
theorem triangular_form_nonneg {f : ℤ → ℂ} (hf : Function.HasFiniteSupport f) (H : ℕ) :
    0 ≤ (H : ℝ) * (∑' n : ℤ, ‖f n‖ ^ 2) +
      2 * ∑ h ∈ Finset.range H, ((H : ℝ) - h - 1) * (correlation f ((h : ℤ) + 1)).re := by
  rw [← shifted_energy_eq hf]
  exact tsum_nonneg (fun _ ↦ sq_nonneg _)

/-- Weighted van der Corput with the exact block factor and the signed
real part of every complete overlap correlation. -/
theorem signed_bound {f : ℤ → ℂ} {a : ℤ} {N H : ℕ} (hH : 0 < H)
    (hf : ∀ n ∉ Finset.Ico a (a + N), f n = 0) :
    (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.Ico a (a + N), f n‖ ^ 2 ≤
      ((N : ℝ) + H - 1) * ((H : ℝ) * (∑ n ∈ Finset.Ico a (a + N), ‖f n‖ ^ 2) +
        2 * ∑ h ∈ Finset.range H, ((H : ℝ) - h - 1) * (correlation f ((h : ℤ) + 1)).re) := by
  have hfinite : Function.HasFiniteSupport f :=
    (Finset.Ico a (a + N)).finite_toSet.subset (by
      intro n hn
      by_contra h
      exact hn (hf n h))
  have h := norm_sum_sq_le_correlation_matrix hH hf
  rw [toeplitz_sum_eq (fun h ↦ (correlation f h).re) (correlation_neg_re f),
    correlation_zero hfinite,
    tsum_eq_sum (fun n hn ↦ by rw [hf n hn, norm_zero, zero_pow (by decide)])] at h
  exact h

/-- The usual absolute-correlation estimate follows downstream from the
stronger signed bound, for every complex amplitude sequence and shift count. -/
theorem absolute_bound {f : ℤ → ℂ} {a : ℤ} {N H : ℕ} (hH : 0 < H)
    (hf : ∀ n ∉ Finset.Ico a (a + N), f n = 0) :
    (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.Ico a (a + N), f n‖ ^ 2 ≤
      ((N : ℝ) + H - 1) * ((H : ℝ) * (∑ n ∈ Finset.Ico a (a + N), ‖f n‖ ^ 2) +
        2 * ∑ h ∈ Finset.range H, ((H : ℝ) - h - 1) * ‖correlation f ((h : ℤ) + 1)‖) := by
  apply (signed_bound hH hf).trans
  have hHr : (1 : ℝ) ≤ H := by exact_mod_cast Nat.succ_le_iff.mpr hH
  apply mul_le_mul_of_nonneg_left _
    (by linarith [Nat.cast_nonneg (α := ℝ) N] : 0 ≤ (N : ℝ) + H - 1)
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply Finset.sum_le_sum
  intro h hh
  have hh' : (h : ℝ) + 1 ≤ H := by
    exact_mod_cast Nat.succ_le_iff.mpr (Finset.mem_range.mp hh)
  exact mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (by linarith)

end
end RiemannGaussian.FiniteVanDerCorput
