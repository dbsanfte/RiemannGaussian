import RiemannGaussian.SymmetricTwoNodePick
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Schwarz--Pick contraction for the finite residual inner function

This file derives a denominator-free Schwarz--Pick inequality for
`lowerRootInnerValue` directly from the finite Pick-kernel positivity already
proved in `FiniteBlaschkePick`.  No general unformalized Schwarz--Pick theorem
is invoked.

The proof samples the residual-inner Pick kernel at two upper-half-plane
points, uses positivity of the resulting `2 × 2` matrix, and expands its
determinant.  Exact input- and output-distance identities then give the
cross-multiplied pseudo-hyperbolic contraction law without any nonvanishing
hypothesis on the output denominator.
-/

open Polynomial

namespace RiemannGaussian

noncomputable section

open scoped ComplexConjugate ComplexOrder

/-- The determinant of the two-point residual-inner Pick matrix bounds the
off-diagonal kernel norm by the product of the diagonal values. -/
theorem lowerRootInnerValue_pick_det
    (p : ℂ[X]) {z a : ℂ} (hz : 0 < z.im) (ha : 0 < a.im) :
    Complex.normSq
        (upperHalfPlanePickKernel (lowerRootInnerValue p) z a) ≤
      ((1 - Complex.normSq (lowerRootInnerValue p z)) / (2 * z.im)) *
        ((1 - Complex.normSq (lowerRootInnerValue p a)) / (2 * a.im)) := by
  let nodes : Fin 2 → ℂ := ![z, a]
  have hnodes : ∀ i, 0 < (nodes i).im := by
    intro i
    fin_cases i
    · exact hz
    · exact ha
  have hpsd := lowerRootInnerValue_pickMatrix_posSemidef p nodes hnodes
  have hdet := hpsd.det_nonneg
  rw [Matrix.det_fin_two] at hdet
  change 0 ≤
    upperHalfPlanePickKernel (lowerRootInnerValue p) z z *
        upperHalfPlanePickKernel (lowerRootInnerValue p) a a -
      upperHalfPlanePickKernel (lowerRootInnerValue p) z a *
        upperHalfPlanePickKernel (lowerRootInnerValue p) a z at hdet
  rw [upperHalfPlanePickKernel_self _ hz,
    upperHalfPlanePickKernel_self _ ha] at hdet
  have hsymm :
      upperHalfPlanePickKernel (lowerRootInnerValue p) a z =
        starRingEnd ℂ
          (upperHalfPlanePickKernel (lowerRootInnerValue p) z a) :=
    upperHalfPlanePickKernel_conj_transpose _ z a
  rw [hsymm] at hdet
  rw [show upperHalfPlanePickKernel (lowerRootInnerValue p) z a *
        starRingEnd ℂ
          (upperHalfPlanePickKernel (lowerRootInnerValue p) z a) =
      (Complex.normSq
        (upperHalfPlanePickKernel (lowerRootInnerValue p) z a) : ℂ) by
    rw [mul_comm, Complex.normSq_eq_conj_mul_self]] at hdet
  norm_cast at hdet
  exact sub_nonneg.mp hdet

/-- Cross-multiplied form of the two-point Pick determinant inequality. -/
theorem lowerRootInnerValue_pick_cross
    (p : ℂ[X]) {z a : ℂ} (hz : 0 < z.im) (ha : 0 < a.im) :
    4 * z.im * a.im *
        Complex.normSq
          (1 - lowerRootInnerValue p z *
            starRingEnd ℂ (lowerRootInnerValue p a)) ≤
      Complex.normSq (z - starRingEnd ℂ a) *
        ((1 - Complex.normSq (lowerRootInnerValue p z)) *
          (1 - Complex.normSq (lowerRootInnerValue p a))) := by
  have hraw := lowerRootInnerValue_pick_det p hz ha
  unfold upperHalfPlanePickKernel at hraw
  rw [Complex.normSq_div, Complex.normSq_mul, Complex.normSq_I,
    one_mul] at hraw
  let C := Complex.normSq
    (1 - lowerRootInnerValue p z *
      starRingEnd ℂ (lowerRootInnerValue p a))
  let D := Complex.normSq (z - starRingEnd ℂ a)
  let P := (1 - Complex.normSq (lowerRootInnerValue p z)) *
    (1 - Complex.normSq (lowerRootInnerValue p a))
  let H := (2 * z.im) * (2 * a.im)
  have hD : 0 < D := Complex.normSq_pos.mpr
    (sub_conj_ne_zero_of_im_pos hz ha)
  have hH : 0 < H := mul_pos (by positivity) (by positivity)
  have hraw' : C / D ≤ P / H := by
    calc
      C / D ≤
          (1 - Complex.normSq (lowerRootInnerValue p z)) / (2 * z.im) *
            ((1 - Complex.normSq (lowerRootInnerValue p a)) /
              (2 * a.im)) := by simpa [C, D] using hraw
      _ = P / H := by
        simp only [P, H]
        field_simp [hz.ne', ha.ne']
  have hcross := (div_le_div_iff₀ hD hH).mp hraw'
  dsimp only [C, D, P, H] at hcross ⊢
  nlinarith

/-- The squared reflected distance exceeds the ordinary squared distance by
the exact upper-half-plane height product. -/
theorem upperHalfPlane_normSq_sub_conj_sub_normSq_sub
    (z a : ℂ) :
    Complex.normSq (z - starRingEnd ℂ a) -
        Complex.normSq (z - a) =
      4 * z.im * a.im := by
  simp [Complex.normSq_apply]
  ring

/-- Exact disk identity relating the output pseudo-hyperbolic numerator and
denominator. -/
theorem normSq_one_sub_mul_conj_sub_normSq_sub
    (s u : ℂ) :
    Complex.normSq (1 - s * starRingEnd ℂ u) -
        Complex.normSq (s - u) =
      (1 - Complex.normSq s) * (1 - Complex.normSq u) := by
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

/-- Denominator-free Schwarz--Pick contraction for the finite residual inner
function on two arbitrary upper-half-plane points. -/
theorem lowerRootInnerValue_schwarzPick_cross
    (p : ℂ[X]) {z a : ℂ} (hz : 0 < z.im) (ha : 0 < a.im) :
    Complex.normSq
          (lowerRootInnerValue p z - lowerRootInnerValue p a) *
        Complex.normSq (z - starRingEnd ℂ a) ≤
      Complex.normSq
          (1 - lowerRootInnerValue p z *
            starRingEnd ℂ (lowerRootInnerValue p a)) *
        Complex.normSq (z - a) := by
  have hpick := lowerRootInnerValue_pick_cross p hz ha
  have hinput := upperHalfPlane_normSq_sub_conj_sub_normSq_sub z a
  have houtput := normSq_one_sub_mul_conj_sub_normSq_sub
    (lowerRootInnerValue p z) (lowerRootInnerValue p a)
  let A := Complex.normSq (z - starRingEnd ℂ a)
  let B := Complex.normSq (z - a)
  let C := Complex.normSq
    (1 - lowerRootInnerValue p z *
      starRingEnd ℂ (lowerRootInnerValue p a))
  let D := Complex.normSq
    (lowerRootInnerValue p z - lowerRootInnerValue p a)
  let H := 4 * z.im * a.im
  let P := (1 - Complex.normSq (lowerRootInnerValue p z)) *
    (1 - Complex.normSq (lowerRootInnerValue p a))
  have hpick' : H * C ≤ A * P := by
    simpa [A, C, H, P] using hpick
  have hinput' : A - B = H := by simpa [A, B, H] using hinput
  have houtput' : C - D = P := by simpa [C, D, P] using houtput
  have hB : B = A - H := by linarith
  have hD : D = C - P := by linarith
  change D * A ≤ C * B
  calc
    D * A = C * A - A * P := by rw [hD]; ring
    _ ≤ C * A - H * C := sub_le_sub_left hpick' (C * A)
    _ = C * B := by rw [hB]; ring

end

end RiemannGaussian
