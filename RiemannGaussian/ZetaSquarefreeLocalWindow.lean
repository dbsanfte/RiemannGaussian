/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaSquarefreeEulerBandRadius

/-!
# Local zero windows for the actual squarefree quotient

The denominator of zeta(s)/zeta(2s) only sees the doubled ordinate window
of the original Cauchy disc. Retaining that window removes the unnecessary
requirement to bound the whole lower divisor. The full closed radius and
the numerator and denominator pole exclusions are unchanged.
-/

namespace RiemannGaussian.SquarefreeLocalWindow
noncomputable section
open Complex Filter Topology SquarefreeEulerBand

/-- The doubled denominator retains the exact local ordinate window of
the original disc, before any absolute-height ceiling is taken. -/
theorem doubled_window {y r : ℝ} {s : ℂ}
    (hs : s ∈ Metric.closedBall (3 / 2 + I * y) r) :
    |(2 * s).im - 2 * y| ≤ 2 * r := by
  have hi := (Complex.abs_im_le_norm (s - (3 / 2 + I * y))).trans
    (mem_closedBall_iff_norm.mp hs)
  norm_num at hi ⊢
  calc
    _ = |(2 : ℝ) * (s.im - y)| := by congr 1; ring
    _ = 2 * |s.im - y| := by rw [abs_mul]; norm_num
    _ ≤ _ := by linarith

/-- Only zeros within the actual doubled ordinate window are needed
to exclude every denominator zero on the complete closed disc. -/
theorem disc_safe {y m : ℝ} (hy : 1 < |y|) (hm : 0 < m) (hmu : m < 1 / 4)
    (hwindow : ∀ ρ : NontrivialZetaZero,
      |ρ.1.im - 2 * y| ≤ 2 * radius y m → ρ.1.re < 1 - m)
    {s : ℂ} (hs : s ∈ Metric.closedBall (3 / 2 + I * y) (radius y m)) :
    s ≠ 1 ∧ 2 * s ≠ 1 ∧ riemannZeta (2 * s) ≠ 0 := by
  obtain ⟨_, hry, _, hmargin⟩ := radius_bounds hy hm hmu
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
  have hedge : 1 - m ≤ (2 * s).re := by
    norm_num
    linarith [(abs_le.mp hre).1]
  refine ⟨hs1, hs2, ?_⟩
  intro hz
  have hpos : 0 < (2 * s).re := by linarith
  have hpole : riemannZeta₁ (2 * s) = 0 := by
    rw [riemannZeta₁_eq_sub_one_mul hs2, hz, mul_zero]
  let ρ : NontrivialZetaZero := ⟨2 * s, isNontrivialZetaZero_of_poleRemoved_eq_zero hpos hpole⟩
  have h := hwindow ρ (doubled_window hs)
  change (2 * s).re < 1 - m at h
  linarith

/-- A proved local zero window supplies the whole squarefree analytic
disc, with no hypothesis concerning zeros at unrelated ordinates. -/
theorem analyticOnNhd_response {y m : ℝ} (hy : 1 < |y|) (hm : 0 < m) (hmu : m < 1 / 4)
    (hwindow : ∀ ρ : NontrivialZetaZero,
      |ρ.1.im - 2 * y| ≤ 2 * radius y m → ρ.1.re < 1 - m) :
    AnalyticOnNhd ℂ squarefreeEulerResponse (Metric.closedBall (3 / 2 + I * y) (radius y m)) := by
  intro s hs
  obtain ⟨hs1, hs2, hz⟩ := disc_safe hy hm hmu hwindow hs
  have hnum := analyticOn_riemannZeta s (by simpa using hs1)
  have hden := (analyticOn_riemannZeta (2 * s) (by simpa using hs2)).comp
    (analyticAt_const.mul analyticAt_id)
  exact hnum.div hden hz

/-- The exact local radius reaches the original marked arithmetic
responses while retaining the full signed two-harmonic prime envelope. -/
theorem exists_response_bound {y m : ℝ} (hy : 1 < |y|) (hm : 0 < m) (hmu : m < 1 / 4)
    (hwindow : ∀ ρ : NontrivialZetaZero,
      |ρ.1.im - 2 * y| ≤ 2 * radius y m → ρ.1.re < 1 - m) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℝ), 0 < r → r ≤ radius y m →
      ∀ S : Finset ℕ, (∀ a ∈ S, a.Prime) → ∀ P : ℕ,
        Squarefree P → (∀ a ∈ P.primeFactors, a ∉ S) →
        ∀ (p : Polynomial ℂ) (N : ℕ),
          ‖RoughSquarefreeBare.response p S P N (3 / 2 + I * y)‖ ≤
            C * SquarefreeEulerPhase.envelope 2 S (3 / 2 + I * y) r * r⁻¹ ^ N *
              ∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k :=
  SquarefreeEulerPhase.exists_response_bound_of_analytic y (radius y m)
    (by linarith [(radius_bounds hy hm hmu).1]) (radius_bounds hy hm hmu).2.2.1.le
    (analyticOnNhd_response hy hm hmu hwindow)

end
end RiemannGaussian.SquarefreeLocalWindow
