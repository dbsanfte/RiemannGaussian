/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SecondDerivativeTest
import RiemannGaussian.LogarithmicShiftPhase

/-!
# The complete second-derivative test for the actual logarithmic phase

For positive height, `-t*log(x)` has second derivative `t/x^2`.
On a positive dyadic block it lies between `t/(4*X^2)` and `t/X^2`.
The resulting finite sum bound covers all crossings of resonances by
the first derivative. The square-root form exposes the usual scale
`N*sqrt(t)/X + X/sqrt(t)`, with a coarse explicit constant.
-/

namespace RiemannGaussian.LogarithmicSecondDerivativeTest
noncomputable section
open PhaseIncrementInverse LogarithmicShiftPhase

/-- The original logarithmic phase has the exact positive second
derivative `t/x^2` on its genuine positive domain. -/
theorem hasDerivAt_first (t : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ ↦ -t / y) (t / x ^ 2) x := by
  convert! (hasDerivAt_const x (-t)).div (hasDerivAt_id x) hx.ne' using 1
  simp only [zero_mul, mul_one, zero_sub, neg_neg, id_eq]

/-- Both curvature bounds hold on the entire original dyadic interval. -/
theorem curvature_bounds {t x X : ℝ} (ht : 0 ≤ t) (hX : 0 < X)
    (hl : X ≤ x) (hu : x ≤ 2 * X) :
    t / (4 * X ^ 2) ≤ t / x ^ 2 ∧ t / x ^ 2 ≤ t / X ^ 2 := by
  have hx : 0 < x := hX.trans_le hl
  have hlo : X ^ 2 ≤ x ^ 2 := sq_le_sq₀ hX.le hx.le |>.mpr hl
  have hhi : x ^ 2 ≤ 4 * X ^ 2 := by nlinarith
  exact ⟨div_le_div_of_nonneg_left ht (sq_pos_of_pos hx) hhi,
    div_le_div_of_nonneg_left ht (sq_pos_of_pos hX) hlo⟩

/-- The whole original logarithmic exponential sum satisfies the
second-derivative bound, with no first-derivative resonance restriction. -/
theorem bound {t X a η : ℝ} (ht : 0 < t) (hX : 0 < X)
    (ha : X ≤ a) (N : ℕ) (hb : a + N ≤ 2 * X) (hη : 0 < η) (hηπ : η ≤ Real.pi) :
    ‖∑ n ∈ Finset.range N, rotation (phase t (a + n))‖ ≤
      (t / X ^ 2 * N / (2 * Real.pi) + 2) *
        (2 * η / (t / (4 * X ^ 2)) + 1 + 2 * Real.pi / η) := by
  have hdom {x : ℝ} (hx : x ∈ Set.Icc a (a + N)) :
      0 < x ∧ X ≤ x ∧ x ≤ 2 * X := ⟨hX.trans_le (ha.trans hx.1), ha.trans hx.1, hx.2.trans hb⟩
  exact SecondDerivativeTest.bound (phase t) (fun x ↦ -t / x) (fun x ↦ t / x ^ 2)
    a N hη hηπ (by positivity) (by positivity)
    (fun _ hx ↦ hasDerivAt_phase t (hdom hx).1)
    (fun _ hx ↦ hasDerivAt_first t (hdom hx).1)
    (fun _ hx ↦ curvature_bounds ht.le hX (hdom hx).2.1 (hdom hx).2.2)

/-- A square-root curvature choice gives an explicit classical bound
for every logarithmic block in its nontrivial curvature range. -/
theorem square_root_bound {t X a : ℝ} (ht : 0 < t) (hX : 0 < X)
    (ha : X ≤ a) (N : ℕ) (hb : a + N ≤ 2 * X) (htX : t ≤ 4 * X ^ 2) :
    ‖∑ n ∈ Finset.range N, rotation (phase t (a + n))‖ ≤
      (4 * N * Real.sqrt (t / (4 * X ^ 2)) / (2 * Real.pi) +
        2 / Real.sqrt (t / (4 * X ^ 2))) * (3 + 2 * Real.pi) := by
  have hdom {x : ℝ} (hx : x ∈ Set.Icc a (a + N)) :
      0 < x ∧ X ≤ x ∧ x ≤ 2 * X := ⟨hX.trans_le (ha.trans hx.1), ha.trans hx.1, hx.2.trans hb⟩
  have he : 4 * (t / (4 * X ^ 2)) = t / X ^ 2 := by ring
  apply SecondDerivativeTest.square_root_bound (phase t) (fun x ↦ -t / x)
    (fun x ↦ t / x ^ 2) a N (by positivity)
    ((div_le_one (by positivity : 0 < 4 * X ^ 2)).mpr htX) (by norm_num)
    (fun _ hx ↦ hasDerivAt_phase t (hdom hx).1)
    (fun _ hx ↦ hasDerivAt_first t (hdom hx).1)
  intro x hx
  rw [he]
  exact curvature_bounds ht.le hX (hdom hx).2.1 (hdom hx).2.2

end
end RiemannGaussian.LogarithmicSecondDerivativeTest
