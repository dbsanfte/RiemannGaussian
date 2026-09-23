/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GammaThetaFifteen
import RiemannGaussian.ZetaHeightFifteen
import RiemannGaussian.ZetaCountingEndpoint
import RiemannGaussian.ZetaZeroCountCompleteness
import RiemannGaussian.ZetaLowZeroIsolation

/-!
# The complete first conjugate pair of zeta zeros

The checked horizontal path and unwrapped Gamma phase determine the
complete multiplicity count through height fifteen. The independently
isolated critical-line zero and its conjugate exhaust that count, leaving
no unseen zeros anywhere in the critical strip below the stated height.
This is a first complete validation window, not the full 25000-zero audit.
-/

namespace RiemannGaussian.ZetaFirstZeroCompleteness
noncomputable section
open Complex Metric ZetaLowZeroSamples ZetaZeroCountCompleteness

/-- The complete symmetric window through height fifteen contains exactly
two zeros counted with their actual analytic multiplicities. -/
theorem count_fifteen : ZetaFiniteZeroCount.count 15 = 2 := by
  apply ZetaCountingEndpoint.count_eq_two_of_phase (by norm_num)
    ZetaHeightFifteen.horizontal_positive
    ZetaHeightFifteen.endpoint_imaginary_positive.le
  · linarith [GammaThetaFifteen.theta_bounds.1, Real.pi_gt_three]
  · exact GammaThetaFifteen.theta_bounds.2

private theorem isolated_ordinate {z : ℂ}
    (hz : z ∈ closedBall center (1 / 100000 : ℝ)) : 14 < z.im ∧ z.im < 15 := by
  have hh := (Complex.abs_im_le_norm (z - center)).trans (mem_closedBall_iff_norm.mp hz)
  simp only [Complex.sub_im] at hh
  have hc : center.im = (14134725141735 / 10 ^ 12 : ℝ) := by norm_num [center, ordinate]
  rw [hc] at hh
  obtain ⟨hl, hu⟩ := abs_le.mp hh
  constructor <;> norm_num at * <;> linarith

/-- The previously isolated simple zero and its conjugate are the entire
finite divisor through height fifteen. Completeness includes all real parts
in the critical strip, not just a search along the critical line. -/
theorem complete_first_pair : ∃ ρ : NontrivialZetaZero,
    14 < ρ.1.im ∧ ρ.1.im < 15 ∧ ρ.1.re = 1 / 2 ∧
    analyticOrderAt riemannZeta ρ.1 = 1 ∧
    ‖ρ.1 - center‖ < (1 / 50000000 : ℝ) ∧
    spectralZetaZeroWindow 15 = {ρ, NontrivialZetaZero.conjugate ρ} := by
  classical
  obtain ⟨z, hz, hzero, hre, horder, _⟩ := ZetaLowZeroIsolation.isolated_critical_zero
  obtain ⟨hlo, hhi⟩ := isolated_ordinate hz
  have hn : IsNontrivialZetaZero z := by
    refine ⟨hzero, ?_, ?_⟩
    · rintro ⟨n, he⟩
      have hh := congrArg Complex.im he
      norm_num at hh
      linarith
    · intro he
      norm_num [he] at hlo
  let ρ : NontrivialZetaZero := ⟨z, hn⟩
  have hne : ρ ≠ NontrivialZetaZero.conjugate ρ := by
    intro he
    have hh := congrArg (fun τ : NontrivialZetaZero => τ.1.im) he
    change z.im = -z.im at hh
    linarith
  refine ⟨ρ, hlo, hhi, hre, horder, ZetaLowZeroIsolation.zero_distance_lt hz hzero, ?_⟩
  apply window_eq_of_count_le_card (by norm_num)
  · intro τ hτ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hτ
    rcases hτ with rfl | rfl
    · change |z.im| ≤ 15
      rw [abs_of_pos (by linarith)]
      exact hhi.le
    · change |-z.im| ≤ 15
      rw [abs_neg, abs_of_pos (by linarith)]
      exact hhi.le
  · rw [count_fifteen, Finset.card_pair hne]

/-- Every nontrivial zeta zero with absolute ordinate at most fifteen is
on the critical line. The complete count, path checks and isolated pair
are all discharged within the theorem's proof. -/
theorem critical_line_through_fifteen (ρ : NontrivialZetaZero) (hρ : |ρ.1.im| ≤ 15) :
    ρ.1.re = 1 / 2 := by
  obtain ⟨τ, _, _, ht, _, _, hw⟩ := complete_first_pair
  have hm := (mem_spectralZetaZeroWindow (by norm_num : (0 : ℝ) ≤ 15) ρ).mpr
    (by simpa only [zetaSpectralCoordinate_re] using hρ)
  rw [hw] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl
  · exact ht
  · simpa using ht

/-- Actual zeta is nonzero off the critical line in the positive real
half-plane through height fifteen. The pole at one is explicitly excluded. -/
theorem nonzero_through_fifteen {s : ℂ} (hs : 0 < s.re) (hh : |s.im| ≤ 15)
    (hl : s.re ≠ 1 / 2) (h1 : s ≠ 1) : riemannZeta s ≠ 0 := by
  intro hz
  have hn : IsNontrivialZetaZero s := by
    refine ⟨hz, ?_, h1⟩
    rintro ⟨n, he⟩
    have hr := congrArg Complex.re he
    norm_num at hr
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  exact hl (critical_line_through_fifteen ⟨s, hn⟩ hh)

/-- There are no nontrivial zeta zeros with absolute ordinate at most
fourteen; the isolated positive zero is consequently the first one. -/
theorem no_zero_through_fourteen (ρ : NontrivialZetaZero) : 14 < |ρ.1.im| := by
  by_contra hn
  have hρ : |ρ.1.im| ≤ 14 := le_of_not_gt hn
  obtain ⟨τ, ht, _, _, _, _, hw⟩ := complete_first_pair
  have hm := (mem_spectralZetaZeroWindow (by norm_num : (0 : ℝ) ≤ 15) ρ).mpr
    (by simpa only [zetaSpectralCoordinate_re] using hρ.trans (by norm_num))
  rw [hw] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl
  · linarith [le_abs_self ρ.1.im]
  · simp only [NontrivialZetaZero.conjugate_coe, conj_im, abs_neg] at hρ
    linarith [le_abs_self τ.1.im]

end
end RiemannGaussian.ZetaFirstZeroCompleteness
