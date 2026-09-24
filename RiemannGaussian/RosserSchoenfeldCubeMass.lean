/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RosserSchoenfeldFourthMass

/-!
# The complete reciprocal-cube zero mass

A positive quadratic identity compares the inverse cube with inverse
squares and fourth powers. The rigorously isolated first conjugate pair
contributes a strict excess to that comparison. Removing this verified
excess recovers Rosser's classical 0.00167 bound over all nontrivial zeros,
including both signs and all analytic multiplicities.
-/

open Complex
namespace RiemannGaussian.RosserSchoenfeldCubeMass
noncomputable section

/-- Nonnegative excess in the square/fourth-power comparison. -/
private def gap (r : ℝ) : ℝ := (13/1000)/r^2 + (250/13)/r^4 - 1/r^3

/-- Completing the square proves global positivity of the excess. -/
private lemma gap_nonneg {r : ℝ} (hr : 0 < r) : 0 ≤ gap r := by
  have he : gap r = ((13/1000)*r-1/2)^2 / ((13/1000)*r^4) := by
    dsimp [gap]
    field_simp
    ring
  rw [he]
  positivity

/-- A strict excess throughout the verified first-pair norm interval. -/
private lemma gap_lower {r : ℝ} (hl : 707/50 ≤ r) (hu : r ≤ 283/20) :
    (3/16000 : ℝ) < gap r := by
  have hr : 0 < r := by linarith
  have h2 : r^2 ≤ (283/20 : ℝ)^2 := pow_le_pow_left₀ hr.le hu 2
  have h4 : r^4 ≤ (283/20 : ℝ)^4 := pow_le_pow_left₀ hr.le hu 4
  have h3 : (707/50 : ℝ)^3 ≤ r^3 := pow_le_pow_left₀ (by norm_num) hl 3
  have hA := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 13/1000)
    (by positivity : (0 : ℝ) < r^2) h2
  have hB := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 250/13)
    (by positivity : (0 : ℝ) < r^4) h4
  have hC := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
    (by norm_num : (0 : ℝ) < (707/50 : ℝ)^3) h3
  dsimp [gap]
  norm_num at hA hB hC
  simp only [one_div] at *
  linarith

/-- A proved nontrivial zero and its distinct conjugate have controlled norms. -/
private lemma first_norm : ∃ ρ : NontrivialZetaZero,
    (707/50 : ℝ) ≤ ‖(ρ.1 : ℂ)‖ ∧ ‖(ρ.1 : ℂ)‖ ≤ (283/20 : ℝ) ∧
    ρ ≠ NontrivialZetaZero.conjugate ρ := by
  obtain ⟨ρ, ht, _, hb, _, hd, _⟩ := ZetaFirstZeroCompleteness.complete_first_pair
  have hh := (Complex.abs_im_le_norm (ρ.1-ZetaLowZeroSamples.center)).trans_lt hd
  norm_num [Complex.sub_im, ZetaLowZeroSamples.center, ZetaLowZeroSamples.ordinate] at hh
  have hs : ‖(ρ.1 : ℂ)‖^2 = (1/2 : ℝ)^2 + ρ.1.im^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hb]
    ring
  have hbounds := abs_lt.mp hh
  have hlo : (7067/500 : ℝ) < ρ.1.im := by linarith
  have hhi : ρ.1.im < (2827/200 : ℝ) := by linarith
  have hsqlo := mul_pos (show 0 < ρ.1.im-7067/500 by linarith)
    (show 0 < ρ.1.im+7067/500 by linarith)
  have hsqhi := mul_pos (show 0 < 2827/200-ρ.1.im by linarith)
    (show 0 < 2827/200+ρ.1.im by linarith)
  refine ⟨ρ, ?_, ?_, ?_⟩
  · nlinarith [norm_nonneg (ρ.1 : ℂ)]
  · nlinarith [norm_nonneg (ρ.1 : ℂ)]
  · intro he
    have hi := congrArg (fun τ : NontrivialZetaZero => τ.1.im) he
    change ρ.1.im = -ρ.1.im at hi
    linarith

/-- The full inverse-cube series is dominated by the proved inverse-square mass. -/
theorem norm_cube_mass_summable : Summable
    (fun ρ : NontrivialZetaZero => (analyticZetaZeroMultiplicity ρ : ℝ)/‖(ρ.1 : ℂ)‖^3) := by
  apply Summable.of_nonneg_of_le (fun ρ => by positivity) _
    RosserSchoenfeldZeroMass.norm_square_mass_summable
  intro ρ
  have hh := (ZetaFirstZeroCompleteness.no_zero_through_fourteen ρ).trans_le
    (Complex.abs_im_le_norm ρ.1)
  have hn : 0 < ‖(ρ.1 : ℂ)‖ := by linarith
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  exact pow_le_pow_right₀ (by linarith) (by norm_num : 2 ≤ 3)

/-- Positive analytic multiplicity preserves the first-pair saving. -/
private lemma weighted_gap_lower (ρ : NontrivialZetaZero)
    (hl : (707/50 : ℝ) ≤ ‖(ρ.1 : ℂ)‖) (hu : ‖(ρ.1 : ℂ)‖ ≤ (283/20 : ℝ)) :
    (3/16000 : ℝ) < (analyticZetaZeroMultiplicity ρ : ℝ)*gap ‖(ρ.1 : ℂ)‖ := by
  have hm : (1 : ℝ) ≤ (analyticZetaZeroMultiplicity ρ : ℝ) := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive ρ
  have hg := gap_lower hl hu
  have hp := mul_le_mul_of_nonneg_right hm (by linarith : 0 ≤ gap ‖(ρ.1 : ℂ)‖)
  exact hg.trans_le (by simpa only [one_mul] using hp)

/-- Rosser's inverse-cube constant for the complete actual zero divisor. -/
theorem norm_cube_mass_lt :
    (∑' ρ : NontrivialZetaZero,
      (analyticZetaZeroMultiplicity ρ : ℝ)/‖(ρ.1 : ℂ)‖^3) < (167/10^5 : ℝ) := by
  classical
  have h4 := RosserSchoenfeldFourthMass.norm_fourth_mass_summable
  have h4b := RosserSchoenfeldFourthMass.norm_fourth_mass_lt
  have h2 := RosserSchoenfeldZeroMass.norm_square_mass_summable
  have h3 := norm_cube_mass_summable
  have hs : Summable (fun ρ : NontrivialZetaZero =>
      (analyticZetaZeroMultiplicity ρ : ℝ)*gap ‖(ρ.1 : ℂ)‖) := by
    convert ((h2.mul_left (13/1000 : ℝ)).add (h4.mul_left (250/13 : ℝ))).sub h3 using 1 <;>
      first | rfl | (ext ρ; dsimp [gap]; ring)
  have he : (∑' ρ : NontrivialZetaZero,
      (analyticZetaZeroMultiplicity ρ : ℝ)*gap ‖(ρ.1 : ℂ)‖) =
      (13/1000)*(∑' ρ : NontrivialZetaZero, (analyticZetaZeroMultiplicity ρ : ℝ)/‖(ρ.1 : ℂ)‖^2) +
      (250/13)*(∑' ρ : NontrivialZetaZero, (analyticZetaZeroMultiplicity ρ : ℝ)/‖(ρ.1 : ℂ)‖^4) -
      (∑' ρ : NontrivialZetaZero, (analyticZetaZeroMultiplicity ρ : ℝ)/‖(ρ.1 : ℂ)‖^3) := by
    have hf : (fun ρ : NontrivialZetaZero => (analyticZetaZeroMultiplicity ρ : ℝ)*gap ‖(ρ.1 : ℂ)‖) =
        (fun ρ : NontrivialZetaZero =>
          (13/1000)*((analyticZetaZeroMultiplicity ρ : ℝ)/‖(ρ.1 : ℂ)‖^2) +
          (250/13)*((analyticZetaZeroMultiplicity ρ : ℝ)/‖(ρ.1 : ℂ)‖^4) -
          (analyticZetaZeroMultiplicity ρ : ℝ)/‖(ρ.1 : ℂ)‖^3) := by
      ext ρ
      dsimp [gap]
      ring
    rw [hf, ((h2.mul_left (13/1000 : ℝ)).add (h4.mul_left (250/13 : ℝ))).tsum_sub h3,
      (h2.mul_left (13/1000 : ℝ)).tsum_add (h4.mul_left (250/13 : ℝ)), tsum_mul_left, tsum_mul_left]
  obtain ⟨ρ, hl, hu, hne⟩ := first_norm
  have hnconj : ‖((NontrivialZetaZero.conjugate ρ).1 : ℂ)‖=‖(ρ.1 : ℂ)‖ := by
    simp [NontrivialZetaZero.conjugate_coe]
  have hg1 := weighted_gap_lower ρ hl hu
  have hg2 := weighted_gap_lower (NontrivialZetaZero.conjugate ρ)
    (by rwa [hnconj]) (by rwa [hnconj])
  have hfloor := hs.sum_le_tsum {ρ, NontrivialZetaZero.conjugate ρ} (fun τ _ =>
    mul_nonneg (Nat.cast_nonneg _) (gap_nonneg (by
      have ht := (ZetaFirstZeroCompleteness.no_zero_through_fourteen τ).trans_le
        (Complex.abs_im_le_norm τ.1)
      linarith)))
  rw [Finset.sum_pair hne, he] at hfloor
  have h2b := RosserSchoenfeldZeroMass.norm_square_mass_lt
  linarith

end
end RiemannGaussian.RosserSchoenfeldCubeMass
