/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiCarrierReflectionEnergy

/-!
# The complete coupled strip correction and its positive source excess

Along every expanding admissible family of the proved outer rectangles,
the joint pole/strip correction has an actual limit: the reflected source
plus the strictly positive reflection energy of an off-axis zero. No
separate convergence of the pole series or strip sides is assumed.
An independent eventual ceiling at the source would therefore suffice
for the contradiction. The ceiling itself remains unproved.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Topology
namespace RiemannGaussian
noncomputable section

/-- Actual expanding contour families satisfying every geometric
condition below exist for each genuine zero, with a linearly growing scale. -/
theorem exists_suzukiXiReflection_contour_family (rho : NontrivialZetaZero) :
    ∃ R l r u : ℕ → ℝ, Tendsto R atTop atTop ∧
      ∀ n, 1 ≤ R n ∧ 2 * |(zetaSpectralCoordinate rho.1).re| ≤ R n ∧
        SuzukiXiCarrierRealRectangleAdmissible (l n) (r n) (u n) ∧
        (-R n - 1 < l n ∧ l n < -R n) ∧ (R n < r n ∧ r n < R n + 1) ∧
          (R n < u n ∧ u n < R n + 1) := by
  let B := max 1 (2 * |(zetaSpectralCoordinate rho.1).re|)
  let R := fun n : ℕ => (n : ℝ) + B
  have hR (n : ℕ) : 1 ≤ R n := by
    dsimp only [R, B]
    linarith [Nat.cast_nonneg (α := ℝ) n, le_max_left (1 : ℝ) (2 * |(zetaSpectralCoordinate rho.1).re|)]
  have ha (n : ℕ) : 2 * |(zetaSpectralCoordinate rho.1).re| ≤ R n := by
    dsimp only [R, B]
    linarith [Nat.cast_nonneg (α := ℝ) n, le_max_right (1 : ℝ) (2 * |(zetaSpectralCoordinate rho.1).re|)]
  choose l r u hadm hl hr hu using fun n => exists_suzukiXiCarrierRealRectangleAdmissible (hR n)
  refine ⟨R, l, r, u, ?_, fun n => ⟨hR n, ha n, hadm n, hl n, hr n, hu n⟩⟩
  have ht : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  apply Filter.tendsto_atTop.2
  intro C
  filter_upwards [ht.eventually (eventually_ge_atTop C)] with n hn
  change C ≤ (n : ℝ) + B
  dsimp only [B]
  linarith [le_max_left (1 : ℝ) (2 * |(zetaSpectralCoordinate rho.1).re|)]

private lemma comparison_at_outer_window
    (rho : NontrivialZetaZero) (hzero : 1 / 2 < rho.1.re) {R l r u : ℝ}
    (hR : 1 ≤ R) (ha : 2 * |(zetaSpectralCoordinate rho.1).re| ≤ R)
    (hadm : SuzukiXiCarrierRealRectangleAdmissible l r u)
    (hl : -R - 1 < l ∧ l < -R) (hr : R < r ∧ r < R + 1) (hu : R < u ∧ u < R + 1) :
    suzukiXiReflectionStripCorrection rho l r u =
      2 * Real.pi / (analyticZetaZeroMultiplicity rho : ℝ) +
        (suzukiXiReflectionPairQuadratic rho (fun a b => suzukiXiTruncatedBoundaryCarrierGramKernel a b l r)).re +
        (suzukiXiReflectionPairQuadratic rho (fun a b =>
          suzukiXiOtherSidesGram a b l r 0 u - suzukiXiCarrierStripSidesGram a b l r)).re ∧
    ‖suzukiXiReflectionPairQuadratic rho (fun a b =>
      suzukiXiOtherSidesGram a b l r 0 u - suzukiXiCarrierStripSidesGram a b l r)‖ ≤
        512 * (zetaSpectralCoordinate rho.1).im ^ 2 / R ^ 3 := by
  constructor
  · apply suzukiXiReflectionStripCorrection_eq_source_add_energy_add_error rho hzero hadm
    · linarith [neg_le_abs (zetaSpectralCoordinate rho.1).re, hl.2]
    · linarith [le_abs_self (zetaSpectralCoordinate rho.1).re, hr.1]
    · linarith [hu.1]
  · apply norm_suzukiXiReflectionPairQuadratic_side_error_le rho hR hadm
    · rw [abs_of_neg (by linarith [hl.2])]
      linarith [hl.2]
    · rw [abs_of_pos (by linarith [hr.1])]
      exact hr.1.le
    · exact ha
    · exact hu.1.le
    · linarith [hu.2]
    · rw [abs_of_pos (sub_pos.mpr hadm.1)]
      linarith [hl.1, hr.2]

/-- The complete coupled correction converges to source plus actual
reflection energy along every expanding admissible outer-window family.
Every retained pole and strip term stays inside this joint limit. -/
theorem tendsto_suzukiXiReflectionStripCorrection_source_add_energy
    (rho : NontrivialZetaZero) (hzero : 1 / 2 < rho.1.re) {R l r u : ℕ → ℝ}
    (hlim : Tendsto R atTop atTop)
    (hgeom : ∀ n, 1 ≤ R n ∧ 2 * |(zetaSpectralCoordinate rho.1).re| ≤ R n ∧
      SuzukiXiCarrierRealRectangleAdmissible (l n) (r n) (u n) ∧
      (-R n - 1 < l n ∧ l n < -R n) ∧ (R n < r n ∧ r n < R n + 1) ∧
        (R n < u n ∧ u n < R n + 1)) :
    Tendsto (fun n => suzukiXiReflectionStripCorrection rho (l n) (r n) (u n)) atTop
      (𝓝 (2 * Real.pi / (analyticZetaZeroMultiplicity rho : ℝ) + suzukiXiReflectionBoundaryEnergy rho)) := by
  have hl : Tendsto l atTop atBot := by
    apply Filter.tendsto_atBot.2
    intro B
    filter_upwards [hlim.eventually (eventually_ge_atTop (-B))] with n hn
    have hln := (hgeom n).2.2.2.1.2
    linarith
  have hr : Tendsto r atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro B
    filter_upwards [hlim.eventually (eventually_ge_atTop B)] with n hn
    have hrn := (hgeom n).2.2.2.2.1.1
    linarith
  let err := fun n => suzukiXiReflectionPairQuadratic rho (fun a b =>
    suzukiXiOtherSidesGram a b (l n) (r n) 0 (u n) - suzukiXiCarrierStripSidesGram a b (l n) (r n))
  have hcomparison (n : ℕ) := comparison_at_outer_window rho hzero
    (hgeom n).1 (hgeom n).2.1 (hgeom n).2.2.1
    (hgeom n).2.2.2.1 (hgeom n).2.2.2.2.1 (hgeom n).2.2.2.2.2
  have hallowance : Tendsto (fun n => 512 * (zetaSpectralCoordinate rho.1).im ^ 2 / (R n) ^ 3)
      atTop (𝓝 0) := by
    have hi := ((tendsto_inv_atTop_zero.comp hlim).pow 3).const_mul
      (512 * (zetaSpectralCoordinate rho.1).im ^ 2)
    simpa only [Function.comp_def, div_eq_mul_inv, inv_pow, zero_pow (by decide : (3 : ℕ) ≠ 0), mul_zero] using hi
  have herr : Tendsto err atTop (𝓝 (0 : ℂ)) :=
    squeeze_zero_norm' (Eventually.of_forall fun n => (hcomparison n).2) hallowance
  have henergy := tendsto_suzukiXiReflection_truncated_energy rho hl hr
  have herrRe := Complex.continuous_re.continuousAt.tendsto.comp herr
  have heq : (fun n => suzukiXiReflectionStripCorrection rho (l n) (r n) (u n)) =
      fun n => 2 * Real.pi / (analyticZetaZeroMultiplicity rho : ℝ) +
        (suzukiXiReflectionPairQuadratic rho (fun a b =>
          suzukiXiTruncatedBoundaryCarrierGramKernel a b (l n) (r n))).re + (err n).re :=
    funext fun n => (hcomparison n).1
  rw [heq]
  simpa only [Function.comp_def, zero_re, add_zero] using (tendsto_const_nhds.add henergy).add herrRe

/-- Even an independent source ceiling with an arbitrary vanishing
allowance would contradict a right-half zero: the actual limiting energy
supplies a strict positive excess, rather than an assumed margin. -/
theorem not_eventually_suzukiXiReflectionStripCorrection_le_source_add_vanishing
    (rho : NontrivialZetaZero) (hzero : 1 / 2 < rho.1.re) {R l r u allowance : ℕ → ℝ}
    (hlim : Tendsto R atTop atTop) (hallowance : Tendsto allowance atTop (𝓝 0))
    (hgeom : ∀ n, 1 ≤ R n ∧ 2 * |(zetaSpectralCoordinate rho.1).re| ≤ R n ∧
      SuzukiXiCarrierRealRectangleAdmissible (l n) (r n) (u n) ∧
      (-R n - 1 < l n ∧ l n < -R n) ∧ (R n < r n ∧ r n < R n + 1) ∧
        (R n < u n ∧ u n < R n + 1)) :
    ¬ (∀ᶠ n in atTop, suzukiXiReflectionStripCorrection rho (l n) (r n) (u n) ≤
      2 * Real.pi / (analyticZetaZeroMultiplicity rho : ℝ) + allowance n) := by
  intro hupper
  have ht := (tendsto_suzukiXiReflectionStripCorrection_source_add_energy rho hzero hlim hgeom).sub hallowance
  have hle : (2 * Real.pi / (analyticZetaZeroMultiplicity rho : ℝ) +
      suzukiXiReflectionBoundaryEnergy rho) - 0 ≤ 2 * Real.pi / (analyticZetaZeroMultiplicity rho : ℝ) := by
    apply le_of_tendsto ht
    filter_upwards [hupper] with n hn
    linarith
  have hpos := suzukiXiReflectionBoundaryEnergy_pos rho (by
    rw [zetaSpectralCoordinate_im]
    linarith)
  linarith

/-- A hypothetical right-half zero is incompatible with an independent
eventual source ceiling on its actual coupled correction. No prescribed
strict deficit is required: the genuine reflection energy supplies the margin. -/
theorem not_eventually_suzukiXiReflectionStripCorrection_le_source
    (rho : NontrivialZetaZero) (hzero : 1 / 2 < rho.1.re) {R l r u : ℕ → ℝ}
    (hlim : Tendsto R atTop atTop)
    (hgeom : ∀ n, 1 ≤ R n ∧ 2 * |(zetaSpectralCoordinate rho.1).re| ≤ R n ∧
      SuzukiXiCarrierRealRectangleAdmissible (l n) (r n) (u n) ∧
      (-R n - 1 < l n ∧ l n < -R n) ∧ (R n < r n ∧ r n < R n + 1) ∧
        (R n < u n ∧ u n < R n + 1)) :
    ¬ (∀ᶠ n in atTop, suzukiXiReflectionStripCorrection rho (l n) (r n) (u n) ≤
      2 * Real.pi / (analyticZetaZeroMultiplicity rho : ℝ)) := by
  intro hupper
  have hle := le_of_tendsto
    (tendsto_suzukiXiReflectionStripCorrection_source_add_energy rho hzero hlim hgeom) hupper
  have hpos := suzukiXiReflectionBoundaryEnergy_pos rho (by
    rw [zetaSpectralCoordinate_im]
    linarith)
  linarith

end
end RiemannGaussian
