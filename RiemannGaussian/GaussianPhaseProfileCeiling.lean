/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianPhaseHeatConstraint
import RiemannGaussian.GaussianHalfLaplaceBounds

/-!+# An all-family ceiling for the coarse Gaussian feedback profile

The present unit-multiplicity profile compares the resonant Gaussian source
with the constant pole envelope and the leading nonconstant gamma cost.
For every positive scale and every summable nonnegative cosine family, a
strict surplus improving the input margin forces the normalized input
below `pi/4` and advances it by less than `4`.

This is a ceiling for this specified profile, not for the full Fermi
explicit formula or for zero-free arguments in general. The exact signed
prime term, Fermi reserves, other zeros, and frequency-dependent gamma
costs can supply information absent from this profile. No zero exclusion
or RH conclusion follows from a method ceiling.
-/

namespace RiemannGaussian.GaussianPhaseProfileCeiling
noncomputable section
open MeasureTheory Set
open GaussianFermiZeroPair GaussianFermiLaplaceOrder GaussianHalfLaplaceBounds
open GaussianPhaseHeatConstraint

/-- Positive damping bounds the actual Gaussian half transform by the
unsmoothed exponential integral. -/
theorem halfGaussian_unit_le_recip {x : ℝ} (hx : 0 < x) :
    halfGaussian 1 x ≤ 1 / x := by
  have he : (∫ u in Ioi (0 : ℝ), Real.exp (-x * u)) = 1 / x := by
    simpa using integral_exp_mul_Ioi (neg_neg_of_pos hx) 0
  rw [halfGaussian, ← he]
  apply integral_mono (integrable_window_exp (by norm_num : (0 : ℝ) < 1) x).integrableOn
    (integrableOn_exp_mul_Ioi (neg_neg_of_pos hx) 0)
  intro u
  apply mul_le_of_le_one_left (Real.exp_pos _).le
  unfold window
  apply Real.exp_le_one_iff.mpr
  nlinarith [sq_nonneg u]

/-- Once the normalized input reaches `pi/4`, the pole and leading gamma
cost dominate this Gaussian source at every scale and every larger target.
The only coefficient constraints are the universal frequency-mass bounds. -/
theorem profile_le_cost_of_input_ge {a₀ a₁ M ℓ μ ν : ℝ}
    (ha₁ : 0 ≤ a₁) (hconstant : a₁ ≤ 2 * a₀) (hnonconstant : a₁ ≤ M)
    (hℓ : 0 < ℓ) (hμ : Real.pi / 4 ≤ μ) (hν : μ ≤ ν) :
    a₁ * halfGaussian 1 (ℓ * (ν - μ)) ≤
      a₀ * halfGaussian 1 (-ℓ * μ) + M / (4 * ℓ) := by
  let g : ℝ := Real.sqrt Real.pi / 2
  have hg : g ^ 2 = Real.pi / 4 := by
    dsimp [g]
    nlinarith [Real.sq_sqrt Real.pi_pos.le]
  have ht : g + ℓ * μ / 2 ≤ halfGaussian 1 (-ℓ * μ) := by
    have h := halfGaussian_tangent_lower (by norm_num : (0 : ℝ) < 1) (-ℓ * μ)
    norm_num only [div_one, mul_one] at h
    dsimp only [g]
    linarith
  have hamgm : 2 * g ≤ ℓ * μ + 1 / ℓ := by
    apply (mul_le_mul_iff_right₀ hℓ).mp
    have he : ℓ * (ℓ * μ + 1 / ℓ) = ℓ ^ 2 * μ + 1 := by
      field_simp
    rw [he]
    have hn := mul_nonneg (sq_nonneg ℓ) (sub_nonneg.mpr (hg.le.trans hμ))
    nlinarith [sq_nonneg (ℓ * g - 1)]
  have hscalar : g ≤ (g + ℓ * μ / 2) / 2 + 1 / (4 * ℓ) := by
    have he : 1 / (4 * ℓ) = (1 / ℓ) / 4 := by ring
    rw [he]
    linarith
  have hsource : halfGaussian 1 (ℓ * (ν - μ)) ≤ g := by
    have h := halfGaussian_antitone (by norm_num : (0 : ℝ) < 1)
      (mul_nonneg hℓ.le (sub_nonneg.mpr hν))
    simpa only [halfGaussian_zero, div_one, g] using h
  calc
    _ ≤ a₁ * g := mul_le_mul_of_nonneg_left hsource ha₁
    _ ≤ a₁ * ((g + ℓ * μ / 2) / 2 + 1 / (4 * ℓ)) :=
      mul_le_mul_of_nonneg_left hscalar ha₁
    _ = (a₁ / 2) * (g + ℓ * μ / 2) + a₁ / (4 * ℓ) := by ring
    _ ≤ a₀ * halfGaussian 1 (-ℓ * μ) + M / (4 * ℓ) := by
      apply add_le_add
      · exact (mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ a₁ / 2)).trans
          (mul_le_mul_of_nonneg_right (by linarith : a₁ / 2 ≤ a₀) (halfGaussian_nonneg _ _))
      · exact div_le_div_of_nonneg_right hnonconstant (by positivity)

/-- A normalized advance of at least four is already dominated by the
leading gamma cost alone, for any positive scale. -/
theorem profile_le_cost_of_gap_ge {a₀ a₁ M ℓ μ ν : ℝ}
    (ha₀ : 0 ≤ a₀) (ha₁ : 0 ≤ a₁) (hnonconstant : a₁ ≤ M)
    (hℓ : 0 < ℓ) (hgap : 4 ≤ ν - μ) :
    a₁ * halfGaussian 1 (ℓ * (ν - μ)) ≤
      a₀ * halfGaussian 1 (-ℓ * μ) + M / (4 * ℓ) := by
  have hx : 0 < ℓ * (ν - μ) := mul_pos hℓ (by linarith)
  have hrec : 1 / (ℓ * (ν - μ)) ≤ 1 / (4 * ℓ) :=
    one_div_le_one_div_of_le (by positivity) (by nlinarith)
  calc
    _ ≤ a₁ * (1 / (ℓ * (ν - μ))) :=
      mul_le_mul_of_nonneg_left (halfGaussian_unit_le_recip hx) ha₁
    _ ≤ a₁ * (1 / (4 * ℓ)) := mul_le_mul_of_nonneg_left hrec ha₁
    _ = a₁ / (4 * ℓ) := by ring
    _ ≤ M / (4 * ℓ) := div_le_div_of_nonneg_right hnonconstant (by positivity)
    _ ≤ _ := le_add_of_nonneg_left (mul_nonneg ha₀ (halfGaussian_nonneg _ _))

/-- Strict surplus in this profile forces a finite bound on both the
input and the output, uniformly over the Gaussian scale and coefficients. -/
theorem strict_profile_surplus_bounds {a₀ a₁ M ℓ μ ν : ℝ}
    (ha₀ : 0 ≤ a₀) (ha₁ : 0 ≤ a₁) (hconstant : a₁ ≤ 2 * a₀)
    (hnonconstant : a₁ ≤ M) (hℓ : 0 < ℓ) (hν : μ ≤ ν)
    (hsurplus : a₀ * halfGaussian 1 (-ℓ * μ) + M / (4 * ℓ) <
      a₁ * halfGaussian 1 (ℓ * (ν - μ))) :
    μ < Real.pi / 4 ∧ ν < μ + 4 ∧ ν < Real.pi / 4 + 4 := by
  have hinput : μ < Real.pi / 4 := by
    by_contra h
    exact (not_lt_of_ge (profile_le_cost_of_input_ge ha₁ hconstant hnonconstant hℓ
      (le_of_not_gt h) hν)) hsurplus
  have hgap : ν < μ + 4 := by
    by_contra h
    exact (not_lt_of_ge (profile_le_cost_of_gap_ge ha₀ ha₁ hnonconstant hℓ
      (by linarith))) hsurplus
  exact ⟨hinput, hgap, by linarith⟩

/-- The ceiling applies to every summable nonnegative family with a
nonnegative full cosine kernel. All constant and unit-frequency masses
are extracted from that actual family; no optimizer or phase count is
chosen. The cost here is exactly the stated coarse Gaussian profile. -/
theorem family_profile_ceiling {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hp : ∀ y : ℝ, 0 ≤ zetaPhaseKernel a ω y) {ℓ μ ν : ℝ}
    (hℓ : 0 < ℓ) (hν : μ ≤ ν)
    (hsurplus : frequencyMass a ω 0 * halfGaussian 1 (-ℓ * μ) +
        nonconstantMass a ω / (4 * ℓ) <
      (frequencyMass a ω 1 + frequencyMass a ω (-1)) * halfGaussian 1 (ℓ * (ν - μ))) :
    μ < Real.pi / 4 ∧ ν < μ + 4 ∧ ν < Real.pi / 4 + 4 := by
  exact strict_profile_surplus_bounds (frequencyMass_nonneg ha 0)
    (add_nonneg (frequencyMass_nonneg ha 1) (frequencyMass_nonneg ha (-1)))
    (opposite_frequencyMass_le ha hs hp 1)
    (opposite_frequencyMass_le_nonconstantMass ha hs (by norm_num : (1 : ℝ) ≠ 0))
    hℓ hν hsurplus

/-- Exact dilation of the genuine half transform to unit scale. -/
theorem halfGaussian_unit_rescale {r : ℝ} (hr : 0 < r) (x : ℝ) :
    halfGaussian (1 / r ^ 2) x = r * halfGaussian 1 (r * x) := by
  have hi : 0 < 1 / r := one_div_pos.mpr hr
  have hB : 1 * (1 / r) ^ 2 = 1 / r ^ 2 := by ring
  have hx : r * x * (1 / r) = x := by field_simp
  apply mul_left_cancel₀ hi.ne'
  rw [← hB, ← hx, halfGaussian_scale hi]
  field_simp

/-- Exact scaling connects the all-family ceiling to the unnormalized
Gaussian source and `M*L/4` gamma cost used by the zero-free chain.
Both the logarithmic scale and the Gaussian scale are arbitrary. -/
theorem scaled_family_profile_ceiling {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hp : ∀ y : ℝ, 0 ≤ zetaPhaseKernel a ω y) {ℓ L m d : ℝ}
    (hℓ : 0 < ℓ) (hL : 0 < L) (hd : m ≤ d)
    (hsurplus : frequencyMass a ω 0 * halfGaussian (1 / (ℓ ^ 2 * L ^ 2)) (-m) +
        nonconstantMass a ω * L / 4 <
      (frequencyMass a ω 1 + frequencyMass a ω (-1)) *
        halfGaussian (1 / (ℓ ^ 2 * L ^ 2)) (d - m)) :
    L * m < Real.pi / 4 ∧ L * d < L * m + 4 ∧ L * d < Real.pi / 4 + 4 := by
  have hscale (x : ℝ) : halfGaussian (1 / (ℓ ^ 2 * L ^ 2)) x =
      (ℓ * L) * halfGaussian 1 ((ℓ * L) * x) := by
    simpa only [mul_pow] using halfGaussian_unit_rescale (mul_pos hℓ hL) x
  have hneg : halfGaussian (1 / (ℓ ^ 2 * L ^ 2)) (-m) =
      (ℓ * L) * halfGaussian 1 (-ℓ * (L * m)) := by
    rw [hscale]
    congr 2
    ring
  have htarget : halfGaussian (1 / (ℓ ^ 2 * L ^ 2)) (d - m) =
      (ℓ * L) * halfGaussian 1 (ℓ * (L * d - L * m)) := by
    rw [hscale]
    congr 2
    ring
  apply family_profile_ceiling ha hs hp hℓ (mul_le_mul_of_nonneg_left hd hL.le)
  apply (mul_lt_mul_iff_left₀ (mul_pos hℓ hL)).mp
  calc
    _ = frequencyMass a ω 0 * halfGaussian (1 / (ℓ ^ 2 * L ^ 2)) (-m) +
        nonconstantMass a ω * L / 4 := by
      rw [hneg]
      field_simp
    _ < _ := hsurplus
    _ = _ := by rw [htarget]; ring

end
end RiemannGaussian.GaussianPhaseProfileCeiling
