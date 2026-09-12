/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.PhaseIncrementInverse
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Discrete Kuzmin--Landau cancellation with exact endpoints

Discrete summation by parts retains both complex endpoints and the full
inverse-increment variation. Between two adjacent resonances, the inverse
increment has constant real part and monotone imaginary part. Its total
variation therefore telescopes. This gives a length-independent bound
`2*pi/eta` for monotone or antitone increments in `[eta,2*pi-eta]`.

This is the classical Kuzmin bound, not Landau's sharper optimal constant.
See Arias de Reyna, https://arxiv.org/abs/2002.05982. No cancellation is
asserted for unrestricted arithmetic weights.
-/

namespace RiemannGaussian.FiniteKuzminLandau
noncomputable section
open PhaseIncrementInverse
open scoped Classical

/-- The signed summation-by-parts identity with both exact complex
endpoints and every interior coefficient difference retained. -/
theorem summation_by_parts (c z : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), c n * (z (n + 1) - z n)) =
      c N * z (N + 1) - c 0 * z 0 +
        ∑ n ∈ Finset.range N, (c n - c (n + 1)) * z (n + 1) := by
  induction N with
  | zero => simp [mul_sub]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring

private theorem norm_sub_vertical {z w : ℂ} (hre : z.re = w.re) :
    ‖z - w‖ = |z.im - w.im| := by
  have he : z - w = ((z.im - w.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hre]
  rw [he, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- A monotone path on one vertical line has total variation bounded
by twice a common endpoint norm bound, independently of its length. -/
theorem variation_le (c : ℕ → ℂ) (N : ℕ) {M : ℝ}
    (hre : ∀ n ≤ N, (c n).re = (c 0).re)
    (hnorm : ∀ n ≤ N, ‖c n‖ ≤ M)
    (hmono : MonotoneOn (fun n ↦ (c n).im) (Set.Icc 0 N) ∨
      AntitoneOn (fun n ↦ (c n).im) (Set.Icc 0 N)) :
    (∑ n ∈ Finset.range N, ‖c n - c (n + 1)‖) ≤ 2 * M := by
  have hn (n : ℕ) (hn : n < N) :
      ‖c n - c (n + 1)‖ = |(c n).im - (c (n + 1)).im| :=
    norm_sub_vertical ((hre n (by omega)).trans (hre (n + 1) (by omega)).symm)
  have hzero := abs_le.mp ((Complex.abs_im_le_norm (c 0)).trans (hnorm 0 (by omega)))
  have hlast := abs_le.mp ((Complex.abs_im_le_norm (c N)).trans (hnorm N le_rfl))
  rcases hmono with hmono | hanti
  · have he : (∑ n ∈ Finset.range N, ‖c n - c (n + 1)‖) = (c N).im - (c 0).im := by
      rw [← Finset.sum_range_sub (fun n ↦ (c n).im) N]
      apply Finset.sum_congr rfl
      intro n hmem
      have hn' := Finset.mem_range.mp hmem
      rw [hn n hn', abs_of_nonpos]
      · ring
      · exact sub_nonpos.mpr (hmono ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega))
    rw [he]
    linarith [hzero.1, hlast.2]
  · have he : (∑ n ∈ Finset.range N, ‖c n - c (n + 1)‖) = (c 0).im - (c N).im := by
      rw [← Finset.sum_range_sub' (fun n ↦ (c n).im) N]
      apply Finset.sum_congr rfl
      intro n hmem
      have hn' := Finset.mem_range.mp hmem
      rw [hn n hn', abs_of_nonneg]
      exact sub_nonneg.mpr (hanti ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega))
    rw [he]
    linarith [hzero.2, hlast.1]

/-- The exact phase increment of a sequence of real angles. -/
def increment (φ : ℕ → ℝ) (n : ℕ) : ℝ := φ (n + 1) - φ n

/-- Division by the genuine phase increment reconstructs the original
unit term from its signed adjacent difference. -/
theorem inverseStep_mul_difference {a b : ℝ}
    (hab : b - a ∈ Set.Ioo 0 (2 * Real.pi)) :
    inverseStep (b - a) * (rotation b - rotation a) = rotation a := by
  calc
    _ = inverseStep (b - a) * ((rotation (b - a) - 1) * rotation a) := by
      rw [sub_mul, one_mul, ← rotation_add, sub_add_cancel]
    _ = _ := by
      rw [← mul_assoc, inverseStep, inv_mul_cancel₀ (rotation_sub_one_ne_zero hab), one_mul]

/-- The original exponential sum equals its two endpoint terms and
the full signed inverse-increment variation. -/
theorem phase_sum_identity (φ : ℕ → ℝ) (N : ℕ)
    (hd : ∀ n ≤ N, increment φ n ∈ Set.Ioo 0 (2 * Real.pi)) :
    (∑ n ∈ Finset.range (N + 1), rotation (φ n)) =
      inverseStep (increment φ N) * rotation (φ (N + 1)) -
        inverseStep (increment φ 0) * rotation (φ 0) +
          ∑ n ∈ Finset.range N,
            (inverseStep (increment φ n) - inverseStep (increment φ (n + 1))) *
              rotation (φ (n + 1)) := by
  calc
    _ = ∑ n ∈ Finset.range (N + 1), inverseStep (increment φ n) *
        (rotation (φ (n + 1)) - rotation (φ n)) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact (inverseStep_mul_difference (hd n (by simpa using Finset.mem_range.mp hn))).symm
    _ = _ := summation_by_parts (fun n ↦ inverseStep (increment φ n)) (fun n ↦ rotation (φ n)) N

/-- Discrete Kuzmin--Landau: monotone or antitone phase increments a
fixed distance from both neighbouring resonances give a bound independent
of the number of original unit terms. -/
theorem bound (φ : ℕ → ℝ) (N : ℕ) {η : ℝ} (hη : 0 < η)
    (hd : ∀ n ≤ N, increment φ n ∈ Set.Icc η (2 * Real.pi - η))
    (hmono : MonotoneOn (increment φ) (Set.Icc 0 N) ∨
      AntitoneOn (increment φ) (Set.Icc 0 N)) :
    ‖∑ n ∈ Finset.range (N + 1), rotation (φ n)‖ ≤ 2 * Real.pi / η := by
  let c : ℕ → ℂ := fun n ↦ inverseStep (increment φ n)
  let M : ℝ := Real.pi / (2 * η)
  have hdom (n : ℕ) (hn : n ≤ N) : increment φ n ∈ Set.Ioo 0 (2 * Real.pi) :=
    ⟨by linarith [(hd n hn).1], by linarith [(hd n hn).2]⟩
  have hcnorm (n : ℕ) (hn : n ≤ N) : ‖c n‖ ≤ M := norm_inverseStep_le hη (hd n hn)
  have hcre (n : ℕ) (hn : n ≤ N) : (c n).re = (c 0).re := by
    rw [inverseStep_re (hdom n hn), inverseStep_re (hdom 0 (by omega))]
  have hcmono : MonotoneOn (fun n ↦ (c n).im) (Set.Icc 0 N) ∨
      AntitoneOn (fun n ↦ (c n).im) (Set.Icc 0 N) := by
    rcases hmono with hm | hm
    · left
      intro i hi j hj hij
      exact inverseStep_im_monotoneOn (hdom i hi.2) (hdom j hj.2) (hm hi hj hij)
    · right
      intro i hi j hj hij
      exact inverseStep_im_monotoneOn (hdom j hj.2) (hdom i hi.2) (hm hi hj hij)
  have hv := variation_le c N hcre hcnorm hcmono
  have hid := phase_sum_identity φ N hdom
  change (∑ n ∈ Finset.range (N + 1), rotation (φ n)) =
    c N * rotation (φ (N + 1)) - c 0 * rotation (φ 0) +
      ∑ n ∈ Finset.range N, (c n - c (n + 1)) * rotation (φ (n + 1)) at hid
  rw [hid]
  calc
    _ ≤ ‖c N * rotation (φ (N + 1)) - c 0 * rotation (φ 0)‖ +
        ‖∑ n ∈ Finset.range N, (c n - c (n + 1)) * rotation (φ (n + 1))‖ := norm_add_le _ _
    _ ≤ (‖c N * rotation (φ (N + 1))‖ + ‖c 0 * rotation (φ 0)‖) +
        ∑ n ∈ Finset.range N, ‖(c n - c (n + 1)) * rotation (φ (n + 1))‖ :=
      add_le_add (norm_sub_le _ _) (norm_sum_le _ _)
    _ = (‖c N‖ + ‖c 0‖) + ∑ n ∈ Finset.range N, ‖c n - c (n + 1)‖ := by
      simp only [norm_mul, norm_rotation, mul_one]
    _ ≤ (M + M) + 2 * M := add_le_add (add_le_add (hcnorm N le_rfl) (hcnorm 0 (by omega))) hv
    _ = _ := by dsimp [M]; ring

end
end RiemannGaussian.FiniteKuzminLandau
