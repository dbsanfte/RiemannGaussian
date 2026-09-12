/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaEulerContinuation
import Mathlib.Analysis.SumIntegralComparisons

/-!
# The actual direct zeta truncation and its retained complex remainder

Every ordinary Dirichlet prefix reconstructs zeta with its full complex
pole endpoint and an absolutely convergent Euler remainder. The elementary
tail bound has no eta-factor loss. It is not yet the sharp oscillatory
remainder bound used in Yang's Lemma 3.2; the exact remainder stays available
for that next step.
-/

namespace RiemannGaussian.ZetaEulerTruncation
noncomputable section
open Complex Filter MeasureTheory Set Topology ZetaEulerCell ZetaEulerContinuation

/-- The full original complex Euler remainder beyond an integer
Dirichlet cutoff, with every unit cell retained. -/
def remainder (N : ℕ) (s : ℂ) : ℂ := ∑' n, cell s (n + N)

/-- The original finite Euler cells telescope to the exact Dirichlet
prefix minus its complete power integral. -/
theorem sum_cell {s : ℂ} (hs : s ≠ 1) (N : ℕ) :
    (∑ n ∈ Finset.range N, cell s n) =
      partialSum N s + ((N + 1 : ℂ) ^ (1 - s) - 1) / (s - 1) := by
  have h := sum_regularizedCell N s
  simp only [regularizedCell_eq, ← Finset.mul_sum] at h
  apply mul_left_cancel₀ (sub_ne_zero.mpr (Ne.symm hs) : 1 - s ≠ 0)
  rw [h]
  field_simp
  ring

/-- Every shifted complex Euler tail converges absolutely for positive
real part, before any estimate forgets its oscillation. -/
theorem summable_remainder {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    Summable (fun n ↦ cell s (n + N)) :=
  (summable_cell hs).comp_injective (by intro a b h; exact Nat.add_right_cancel h)

/-- Actual zeta equals its ordinary Dirichlet prefix, its genuine
complex pole endpoint, and the complete signed Euler remainder. -/
theorem zeta_eq_partialSum_add_endpoint_add_remainder {s : ℂ}
    (hs : 0 < s.re) (hsne : s ≠ 1) (N : ℕ) :
    riemannZeta s = partialSum N s + (N + 1 : ℂ) ^ (1 - s) / (s - 1) + remainder N s := by
  have h := (summable_cell hs).sum_add_tsum_nat_add N
  rw [sum_cell hsne, tsum_cell_eq hs hsne] at h
  change partialSum N s + ((N + 1 : ℂ) ^ (1 - s) - 1) / (s - 1) + remainder N s =
    riemannZeta s - 1 / (s - 1) at h
  linear_combination -h

/-- The entire positive power tail is controlled by its actual
improper integral at the same cutoff. -/
theorem tsum_envelope_tail_le {p : ℝ} (hp : 0 < p) {N : ℕ} (hN : 1 ≤ N) :
    (∑' n : ℕ, (n + N + 1 : ℝ) ^ (-p - 1)) ≤ (N : ℝ) ^ (-p) / p := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have he : -p - 1 < -1 := by linarith
  have ha : AntitoneOn (fun x : ℝ ↦ x ^ (-p - 1)) (Ici (N : ℝ)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (hNp.trans_le hx) hxy (by linarith)
  have h := ha.tsum_comp_add_le_integral N (integrableOn_Ioi_rpow_of_lt he hNp)
    (fun x hx ↦ Real.rpow_nonneg (hNp.trans hx).le _)
  simp only [Nat.cast_add, Nat.cast_one] at h
  apply h.trans_eq
  rw [integral_Ioi_rpow_of_lt he hNp]
  rw [show -p - 1 + 1 = -p by ring]
  ring

/-- A first unconditional quantitative bound for the actual complex
Euler remainder, with no division by an eta factor. -/
theorem norm_remainder_le {s : ℂ} (hs : 0 < s.re) {N : ℕ} (hN : 1 ≤ N) :
    ‖remainder N s‖ ≤ ‖s‖ / s.re * (N : ℝ) ^ (-s.re) := by
  have hm := ((summable_envelope hs).comp_injective
    (show Function.Injective (fun n : ℕ ↦ n + N) by intro a b h; exact Nat.add_right_cancel h)).mul_left ‖s‖
  have hn := (summable_remainder hs N).norm
  have hb := hn.tsum_le_tsum (fun n ↦ norm_cell_le hs (n + N)) hm
  unfold remainder
  apply (norm_tsum_le_tsum_norm hn).trans (hb.trans _)
  simp only [Nat.cast_add, tsum_mul_left]
  have h := mul_le_mul_of_nonneg_left (tsum_envelope_tail_le hs hN) (norm_nonneg s)
  convert h using 1
  ring

/-- The literal Dirichlet truncation error separates its true pole
endpoint from the original full oscillatory remainder. -/
theorem norm_zeta_sub_partialSum_le {s : ℂ} (hs : 0 < s.re) (hsne : s ≠ 1)
    {N : ℕ} (hN : 1 ≤ N) :
    ‖riemannZeta s - partialSum N s‖ ≤
      (N + 1 : ℝ) ^ (1 - s.re) / ‖s - 1‖ + ‖s‖ / s.re * (N : ℝ) ^ (-s.re) := by
  rw [zeta_eq_partialSum_add_endpoint_add_remainder hs hsne N]
  have he : partialSum N s + (N + 1 : ℂ) ^ (1 - s) / (s - 1) + remainder N s - partialSum N s =
      (N + 1 : ℂ) ^ (1 - s) / (s - 1) + remainder N s := by ring
  rw [he]
  apply (norm_add_le _ _).trans
  have hp : ‖(N + 1 : ℂ) ^ (1 - s) / (s - 1)‖ =
      (N + 1 : ℝ) ^ (1 - s.re) / ‖s - 1‖ := by
    rw [norm_div]
    congr 1
    have h := Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : (0 : ℝ) < N + 1) (1 - s)
    simpa only [Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one,
      sub_re, one_re] using h
  rw [hp]
  exact add_le_add_right (norm_remainder_le hs hN) _

end
end RiemannGaussian.ZetaEulerTruncation
