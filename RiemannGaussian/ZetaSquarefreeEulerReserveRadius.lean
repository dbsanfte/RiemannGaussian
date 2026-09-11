/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPoleReserveBootstrap
import RiemannGaussian.ZetaSquarefreeEulerQuadraticSieveDecay

/-!
# Transporting the improved zero-free region to the squarefree response

The positive pole reserve enlarges the proved zero-free region. This
module transports that gain to a larger analytic disc for the actual
quotient `zeta(s) / zeta(2*s)`, then to all marked squarefree filters and
all complex polynomial families. The arithmetic Euler budget is retained
when the radius changes; no estimate for the ordinary-prime error follows
from the complete squarefree response alone.
-/

namespace RiemannGaussian
noncomputable section
open Complex Filter Topology

/-- The wider region supplies a common Cauchy radius for every
squarefree mark and every polynomial; the ordinate cap avoids the poles. -/
def squarefreeEulerReserveRadius (y : ℝ) : ℝ :=
  1 + min ((|y| - 1) / 2) (zetaPoleReserveZeroMargin (2 * |y| + 3) / 2)

/-- The new radius remains within both the actual pole separation
and the full doubled-argument zero-free allowance. -/
theorem squarefreeEulerReserveRadius_bounds {y : ℝ} (hy : 1 < |y|) :
    1 < squarefreeEulerReserveRadius y ∧ squarefreeEulerReserveRadius y < |y| ∧
      squarefreeEulerReserveRadius y < 9 / 8 ∧
      2 * (squarefreeEulerReserveRadius y - 1) ≤ zetaPoleReserveZeroMargin (2 * |y| + 3) := by
  obtain ⟨hm, hmu⟩ := zetaPoleReserveZeroMargin_bounds (2 * |y| + 3)
  have hmin : 0 < min ((|y| - 1) / 2) (zetaPoleReserveZeroMargin (2 * |y| + 3) / 2) :=
    lt_min (by linarith) (by positivity)
  have hleft := min_le_left ((|y| - 1) / 2) (zetaPoleReserveZeroMargin (2 * |y| + 3) / 2)
  have hright := min_le_right ((|y| - 1) / 2) (zetaPoleReserveZeroMargin (2 * |y| + 3) / 2)
  unfold squarefreeEulerReserveRadius
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- No ordinate loses its preceding analytic radius. -/
theorem squarefreeEulerRadius_le_reserveRadius (y : ℝ) :
    squarefreeEulerRadius y ≤ squarefreeEulerReserveRadius y := by
  have h := zetaSignedPole_margin_le_poleReserve (2 * |y| + 3)
  have hp := (zetaPoleReserveZeroMargin_bounds (2 * |y| + 3)).1
  unfold squarefreeEulerRadius squarefreeEulerReserveRadius
  exact add_le_add le_rfl (min_le_min_left _
    (show zetaSignedPoleZeroMargin (2 * |y| + 3) / 4 ≤
      zetaPoleReserveZeroMargin (2 * |y| + 3) / 2 by linarith))

/-- Away from the small pole-separation cap the radius increases
strictly. In particular this applies at every actual zero ordinate. -/
theorem squarefreeEulerRadius_lt_reserveRadius {y : ℝ} (hy : 3 / 2 ≤ |y|) :
    squarefreeEulerRadius y < squarefreeEulerReserveRadius y := by
  have hL : 13 / 10 ≤ Real.log (|2 * |y| + 3| + 2) := by
    have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 4)
      (by linarith [le_abs_self (2 * |y| + 3)] : (4 : ℝ) ≤ |2 * |y| + 3| + 2)
    have he : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    rw [he] at hlog
    linarith [Real.log_two_gt_d9]
  have hm := (zetaSignedPole_margin_lt_poleReserveFixed hL).trans_le
    (le_max_right (zetaSignedPoleZeroMargin (2 * |y| + 3))
      (zetaPoleReserveFixedMargin (2 * |y| + 3)))
  change zetaSignedPoleZeroMargin (2 * |y| + 3) < zetaPoleReserveZeroMargin (2 * |y| + 3) at hm
  have hb := zetaSignedPoleZeroMargin_lt_one_quarter (2 * |y| + 3)
  have hr := (zetaPoleReserveZeroMargin_bounds (2 * |y| + 3)).2
  unfold squarefreeEulerRadius squarefreeEulerReserveRadius
  rw [min_eq_right (by linarith : zetaSignedPoleZeroMargin (2 * |y| + 3) / 4 ≤ (|y| - 1) / 2),
    min_eq_right (by linarith : zetaPoleReserveZeroMargin (2 * |y| + 3) / 2 ≤ (|y| - 1) / 2)]
  have hp := zetaSignedPoleZeroMargin_pos (2 * |y| + 3)
  linarith

/-- The larger disc avoids the literal numerator pole and every
zero or pole of the doubled zeta denominator. -/
theorem squarefreeEuler_reserve_disc_safe {y : ℝ} (hy : 1 < |y|) {s : ℂ}
    (hs : s ∈ Metric.closedBall (3 / 2 + I * y) (squarefreeEulerReserveRadius y)) :
    s ≠ 1 ∧ 2 * s ≠ 1 ∧ riemannZeta (2 * s) ≠ 0 := by
  obtain ⟨hr, hry, hru, hmargin⟩ := squarefreeEulerReserveRadius_bounds hy
  have hre := (Complex.abs_re_le_norm (s - (3 / 2 + I * y))).trans
    (mem_closedBall_iff_norm.mp hs)
  have him := (Complex.abs_im_le_norm (s - (3 / 2 + I * y))).trans
    (mem_closedBall_iff_norm.mp hs)
  norm_num at hre him
  have him0 : s.im ≠ 0 := by
    intro h
    simp only [h, zero_sub, abs_neg] at him
    linarith
  have hs1 : s ≠ 1 := by intro h; apply him0; simp [h]
  have hs2 : 2 * s ≠ 1 := by
    intro h
    have hi := congrArg Complex.im h
    norm_num at hi
    exact him0 (by linarith)
  have himBound : |s.im| ≤ |y| + squarefreeEulerReserveRadius y := by
    apply abs_le.mpr
    constructor <;> linarith [(abs_le.mp him).1, (abs_le.mp him).2, le_abs_self y, neg_abs_le y]
  have harg : |(2 * s).im| ≤ |2 * |y| + 3| := by
    rw [abs_of_nonneg (by positivity : 0 ≤ 2 * |y| + 3)]
    norm_num [abs_mul]
    linarith
  have hwidth := zetaPoleReserveZeroMargin_antitone_abs harg
  have hedge : 1 - zetaPoleReserveZeroMargin (2 * s).im ≤ (2 * s).re := by
    norm_num at hwidth ⊢
    have hM := (zetaPoleReserveZeroMargin_bounds (2 * |y| + 3)).1
    nlinarith [(abs_le.mp hre).1]
  exact ⟨hs1, hs2, riemannZeta_ne_zero_of_poleReserve_margin hs2 hedge⟩

/-- Every genuine nontrivial zero ordinate receives a strictly
larger squarefree analytic radius, using the proved eta height floor. -/
theorem squarefreeEulerRadius_lt_reserveRadius_at_zero (rho : NontrivialZetaZero) :
    squarefreeEulerRadius rho.1.im < squarefreeEulerReserveRadius rho.1.im := by
  apply squarefreeEulerRadius_lt_reserveRadius
  nlinarith [nontrivialZetaZero_im_sq_gt_three rho, sq_abs rho.1.im,
    abs_nonneg rho.1.im]

/-- The actual complete squarefree response is analytic throughout
a neighbourhood of the larger closed disc. -/
theorem analyticOnNhd_squarefreeEulerResponse_reserve {y : ℝ} (hy : 1 < |y|) :
    AnalyticOnNhd ℂ squarefreeEulerResponse
      (Metric.closedBall (3 / 2 + I * y) (squarefreeEulerReserveRadius y)) := by
  intro s hs
  obtain ⟨hs1, hs2, hz⟩ := squarefreeEuler_reserve_disc_safe hy hs
  have hnum := analyticOn_riemannZeta s (by simpa using hs1)
  have hden := (analyticOn_riemannZeta (2 * s) (by simpa using hs2)).comp
    (analyticAt_const.mul analyticAt_id)
  exact hnum.div hden hz

/-- The improved domain reaches every original marked arithmetic
filter and all complex polynomials, uniformly over every smaller radius.
The Euler budget changes with the radius and is explicitly retained. -/
theorem exists_squarefreeEuler_reserve_radius_bound (y : ℝ) (hy : 1 < |y|) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℝ), 0 < r → r ≤ squarefreeEulerReserveRadius y →
      ∀ S : Finset ℕ, (∀ a ∈ S, a.Prime) → ∀ P : ℕ,
        Squarefree P → (∀ a ∈ P.primeFactors, a ∉ S) →
        ∀ (p : Polynomial ℂ) (N : ℕ),
          ‖RoughSquarefreeBare.response p S P N (3 / 2 + I * y)‖ ≤
            C * squarefreeEulerBudget (3 / 2 - r) S P * r⁻¹ ^ N *
              ∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k :=
  exists_squarefreeEuler_variable_radius_bound_of_analytic y (squarefreeEulerReserveRadius y)
    (by linarith [(squarefreeEulerReserveRadius_bounds hy).1])
    (by linarith [(squarefreeEulerReserveRadius_bounds hy).2.2.1])
    (analyticOnNhd_squarefreeEulerResponse_reserve hy)

end
end RiemannGaussian
