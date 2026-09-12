/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaStripBoundaryConstraint
import RiemannGaussian.ZetaClippedEulerFamily
import RiemannGaussian.ZetaRegularizedSechMean
import RiemannGaussian.ZetaNearOneFullDisc

/-!
# The actual cotangent source on the sharp Euler strip

The strip is aligned exactly with the existing balanced Euler line.
Its full left and right integrals are the genuine signed means already
constructed. The rational center correction has favorable sign at the
working heights. Both the marked zero channel and every unmarked channel
retain their actual means and the exact cotangent normalization.
-/

namespace RiemannGaussian.ZetaStripEulerConstraint
noncomputable section
open Complex
open DirichletPowerParameters DerivativeOrderComparison ZetaNearOneLocalDisc

/-- The half-width aligns the left strip edge with the balanced Euler line. -/
def halfWidth (k : ℕ) (x : ℝ) : ℝ := delta k + x

/-- The right strip edge lies strictly inside the absolute Euler half-plane. -/
def rightLine (k : ℕ) (x : ℝ) : ℝ := 1 + delta k + 2 * x

/-- The exact physical height scale of the strip boundary density. -/
def verticalScale (k : ℕ) (x : ℝ) : ℝ := 2 * halfWidth k x / Real.pi

/-- Every positive center shift gives a positive actual strip half-width. -/
theorem halfWidth_pos (k : ℕ) {x : ℝ} (hx : 0 < x) : 0 < halfWidth k x :=
  add_pos (delta_pos k) hx

/-- The entire right vertical boundary stays strictly on the Euler side. -/
theorem rightLine_gt_one (k : ℕ) {x : ℝ} (hx : 0 < x) : 1 < rightLine k x := by
  unfold rightLine
  linarith [delta_pos k]

/-- The physical vertical scale is strictly positive. -/
theorem verticalScale_pos (k : ℕ) {x : ℝ} (hx : 0 < x) : 0 < verticalScale k x := by
  unfold verticalScale
  exact div_pos (mul_pos (by norm_num) (halfWidth_pos k hx)) Real.pi_pos

/-- The left physical boundary is exactly the balanced Euler line at every height. -/
theorem leftPoint_eq (k : ℕ) (x t u : ℝ) :
    center x t - (halfWidth k x : ℂ) + ((2 * halfWidth k x / Real.pi * u : ℝ) : ℂ) * I =
      (line k : ℂ) + I * ((t + verticalScale k x * u : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [center, halfWidth, verticalScale, delta_eq_one_sub_line]

/-- The right physical boundary is exactly the original Euler mean parametrization. -/
theorem rightPoint_eq (k : ℕ) (x t u : ℝ) :
    center x t + (halfWidth k x : ℂ) + ((2 * halfWidth k x / Real.pi * u : ℝ) : ℂ) * I =
      (rightLine k x : ℂ) + I * ((t + verticalScale k x * u : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [center, halfWidth, rightLine, verticalScale]
  ring

/-- The existing center schedule discharges all strip boundary geometry hypotheses. -/
theorem geometry (k : ℕ) (hk : 2 ≤ k) {x : ℝ} (hx : 0 < x) (hx' : x ≤ delta k / 4) (t : ℝ) :
    (1 / 2 : ℝ) ≤ (center x t).re - halfWidth k x ∧
      (center x t).re + halfWidth k x ≤ 3 / 2 := by
  have hd := ZetaNearOneFullDisc.delta_le_two_sevenths hk
  have hl := half_le_line k (by omega)
  have he := delta_eq_one_sub_line k
  simp only [center, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im,
    zero_mul, mul_zero, sub_zero, add_zero, halfWidth]
  constructor <;> linarith

/-- The actual boundary functional retains its complete signed left and right
means with the exact physical factor; this is an identity before estimation. -/
theorem boundary_eq (k : ℕ) (x t M : ℝ) :
    ZetaStripBoundaryConstraint.boundary (center x t) (halfWidth k x) M =
      (1 / (2 * halfWidth k x)) *
        (ZetaClippedEulerMean.mean k M t (verticalScale k x) -
          ZetaRegularizedSechMean.mean (rightLine k x) t (verticalScale k x)) := by
  rw [ZetaStripBoundaryConstraint.boundary_eq_density]
  simp_rw [leftPoint_eq, rightPoint_eq]
  rfl

/-- The exact rational center correction has favorable sign on every
working nonconstant phase channel. -/
theorem center_pole_nonpos (k : ℕ) (hk : 2 ≤ k) {x t : ℝ} (hx : 0 < x)
    (hx' : x ≤ delta k / 4) (ht : 2 ≤ |t|) :
    (1 / (center x t - 1) - 1 / (center x t + 1)).re ≤ 0 := by
  have hg := (geometry k hk hx hx' t).2
  have hw := halfWidth_pos k hx
  apply RationalVerticalCorrection.pole_re_nonpos_of_height
  · simp [center]; linarith
  · linarith
  · simpa [center] using ht

/-- Every unmarked channel has an actual complete signed mean bound,
with no positive charge for the rational center correction. -/
theorem logDeriv_le_means (k : ℕ) (hk : 2 ≤ k) {x t M : ℝ} (hx : 0 < x)
    (hx' : x ≤ delta k / 4) (ht : 2 ≤ |t|) (hM : 0 ≤ M) :
    (-logDeriv riemannZeta (center x t)).re ≤
      (1 / (2 * halfWidth k x)) *
        (ZetaClippedEulerMean.mean k M t (verticalScale k x) -
          ZetaRegularizedSechMean.mean (rightLine k x) t (verticalScale k x)) := by
  have hg := geometry k hk hx hx' t
  have h := ZetaStripBoundaryConstraint.logDeriv_le_boundary
    (c := center x t) (by simpa [center] using hx) (halfWidth_pos k hx) hg.1 hg.2 hM
  rw [boundary_eq] at h
  linarith [center_pole_nonpos k hk hx hx' ht]

/-- A selected actual zero above the balanced line lies in the whole strip,
with no artificial smaller-disc source cutoff. -/
theorem zero_mem_strip (k : ℕ) (ρ : NontrivialZetaZero) {x : ℝ} (hx : 0 < x)
    (hnear : line k < ρ.1.re) : ρ.1 ∈ AnalyticStripDisc.strip (center x ρ.1.im) (halfWidth k x) := by
  change |ρ.1.re - (center x ρ.1.im).re| < halfWidth k x
  have hc : (center x ρ.1.im).re = 1 + x := by simp [center]
  rw [hc, abs_of_neg (by linarith [NontrivialZetaZero.re_lt_one ρ])]
  unfold halfWidth
  rw [delta_eq_one_sub_line]
  linarith

/-- The actual selected zero keeps its full cotangent source and multiplicity
against the two complete signed arithmetic means. -/
theorem selected_source_le_means (k : ℕ) (hk : 2 ≤ k) (ρ : NontrivialZetaZero) {x M : ℝ}
    (hx : 0 < x) (hx' : x ≤ delta k / 4) (ht : 2 ≤ |ρ.1.im|) (hM : 0 ≤ M)
    (hnear : line k < ρ.1.re) :
    (-logDeriv riemannZeta (center x ρ.1.im)).re + (analyticZetaZeroMultiplicity ρ : ℝ) *
      (Real.pi / (2 * halfWidth k x)) *
        Real.cot (Real.pi * (1 + x - ρ.1.re) / (2 * halfWidth k x)) ≤
      (1 / (2 * halfWidth k x)) *
        (ZetaClippedEulerMean.mean k M ρ.1.im (verticalScale k x) -
          ZetaRegularizedSechMean.mean (rightLine k x) ρ.1.im (verticalScale k x)) := by
  have hg := geometry k hk hx hx' ρ.1.im
  have h := ZetaStripBoundaryConstraint.selected_zero_constraint ρ
    (c := center x ρ.1.im) (by simpa [center] using hx) (halfWidth_pos k hx) hg.1 hg.2 hM
    (zero_mem_strip k ρ hx hnear) (by simp [center])
  rw [boundary_eq] at h
  have hc : (center x ρ.1.im).re = 1 + x := by simp [center]
  rw [hc] at h
  linarith [center_pole_nonpos k hk hx hx' ht]

end
end RiemannGaussian.ZetaStripEulerConstraint
