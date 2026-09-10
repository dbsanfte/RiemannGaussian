/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiReflectionMassArea
import RiemannGaussian.SuzukiCarrierSmoothReflectionLimit
import RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevLogAverageLaplaceBoundaryHeatCommonHoleComparison

/-!
# Ordinary reflection areas and independently vanishing current edges

Local integrability removes the puncture parameter from the actual area
source. The two mass-current edges have an independent inverse-square
height bound. Their removal leaves the complete signed mass variation
and remainder, whose combined ordinary area limit is the original
positive reflected source. No upper bound for that combination is assumed.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Interval
namespace RiemannGaussian
noncomputable section

/-- The actual two oriented current edges, with their source coefficient. -/
def suzukiXiReflectionMassEdge (rho : NontrivialZetaZero) (r c tau R : ℝ) : ℂ :=
  2 * I * (r : ℂ)^2 * (∫ y : ℝ in 0..R,
    suzukiXiReflectionMassCurrent rho r c tau y R - suzukiXiReflectionMassCurrent rho r c tau y (-R))

private lemma current_remote_bound (rho : NontrivialZetaZero)
    {r tau R v y : ℝ} (hr : 0 < r) (htau : 0 ≤ tau) (hR : 0 < R)
    (hv : R ≤ |v|) (ha : 2 * |(zetaSpectralCoordinate rho.1).re| ≤ R)
    (hy : y ∈ Icc 0 R) (c : ℝ) :
    ‖suzukiXiReflectionMassCurrent rho r c tau y v‖ ≤
      64 * (zetaSpectralCoordinate rho.1).im ^ 2 / (r ^ 3 * R ^ 3) := by
  have hB : ‖suzukiSmoothSpectralBoundaryHeat c tau ((v : ℂ) + (y : ℂ) * I)‖ ≤ 2 * R := by
    rw [suzukiSmoothSpectralBoundaryHeat_eq]
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero,
      sub_zero, add_zero, add_im, mul_im, mul_one, zero_add, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) hy.1) (Real.exp_pos _).le)]
    calc
      _ ≤ 2 * y * 1 := mul_le_mul_of_nonneg_left
        (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr htau)
          (add_nonneg (sq_nonneg _) (sq_nonneg _)))) (mul_nonneg (by norm_num) hy.1)
      _ ≤ 2 * R := by linarith [hy.2]
  calc
    _ ≤ ‖suzukiXiHorizontalReflectionHeat rho c tau y v‖ / (2*r^3) :=
      norm_suzukiXiReflectionMassCurrent_le rho hr c tau y v
    _ ≤ (64 * (zetaSpectralCoordinate rho.1).im ^ 2 / R ^ 4 * (2 * R)) / (2*r^3) := by
      unfold suzukiXiHorizontalReflectionHeat
      rw [norm_mul]
      gcongr
      exact norm_suzukiXiReflectionWeight_vertical_le rho hR hv ha
    _ = _ := by field_simp

/-- An independent bound for the complete current-edge contribution.
It holds for every center and nonnegative heat time, including zero time. -/
theorem norm_suzukiXiReflectionMassEdge_le (rho : NontrivialZetaZero)
    {r tau R : ℝ} (hr : 0 < r) (htau : 0 ≤ tau) (hR : 0 < R) (c : ℝ)
    (ha : 2 * |(zetaSpectralCoordinate rho.1).re| ≤ R) :
    ‖suzukiXiReflectionMassEdge rho r c tau R‖ ≤
      256 * (zetaSpectralCoordinate rho.1).im ^ 2 / (r * R ^ 2) := by
  have hint : ‖∫ y : ℝ in 0..R,
      suzukiXiReflectionMassCurrent rho r c tau y R - suzukiXiReflectionMassCurrent rho r c tau y (-R)‖ ≤
        (128 * (zetaSpectralCoordinate rho.1).im ^ 2 / (r^3 * R^3)) * |R - 0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro y hy
    have hy' : y ∈ Icc 0 R := by
      simpa only [uIcc_of_le hR.le] using uIoc_subset_uIcc hy
    calc
      _ ≤ ‖suzukiXiReflectionMassCurrent rho r c tau y R‖ +
          ‖suzukiXiReflectionMassCurrent rho r c tau y (-R)‖ := norm_sub_le _ _
      _ ≤ 64 * (zetaSpectralCoordinate rho.1).im^2 / (r^3*R^3) +
          64 * (zetaSpectralCoordinate rho.1).im^2 / (r^3*R^3) :=
        add_le_add (current_remote_bound rho hr htau hR (by rw [abs_of_pos hR]) ha hy' c)
          (current_remote_bound rho hr htau hR (by simp [abs_of_pos hR]) ha hy' c)
      _ = _ := by ring
  rw [suzukiXiReflectionMassEdge, norm_mul]
  have hn : ‖2 * I * (r : ℂ)^2‖ = 2 * r^2 := by
    simp [norm_pow, abs_of_pos hr]
  rw [hn]
  calc
    _ ≤ (2*r^2) * ((128 * (zetaSpectralCoordinate rho.1).im^2 / (r^3*R^3)) * |R-0|) := by
      gcongr
    _ = _ := by rw [sub_zero, abs_of_pos hR]; field_simp; ring

/-- The current edges vanish independently for each fixed positive
smoothing radius. No Gaussian decay or arithmetic hypothesis is needed. -/
theorem tendsto_suzukiXiReflectionMassEdge_zero (rho : NontrivialZetaZero)
    {r tau : ℝ} (hr : 0 < r) (htau : 0 ≤ tau) (c : ℝ) :
    Tendsto (suzukiXiReflectionMassEdge rho r c tau) atTop (𝓝 0) := by
  have ht : Tendsto (fun R : ℝ => 256 * (zetaSpectralCoordinate rho.1).im ^ 2 / (r * R^2))
      atTop (𝓝 0) := by
    have hpow : Tendsto (fun R : ℝ => R^2) atTop atTop :=
      tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
    have h := (tendsto_const_nhds (x := 256 * (zetaSpectralCoordinate rho.1).im^2 / r)).div_atTop hpow
    simpa only [div_div] using h
  apply squeeze_zero_norm' _ ht
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    eventually_ge_atTop (2 * |(zetaSpectralCoordinate rho.1).re|)] with R hR ha
  exact norm_suzukiXiReflectionMassEdge_le rho hr htau hR c ha

/-- Local integrability identifies the prior excision limit with the
ordinary area. The reflected source is retained with its original sign. -/
theorem rectangularAreaIntegral_suzukiXiSmoothReflectionSource_eq_boundary_add_mass
    (rho : NontrivialZetaZero) (hzero : 1 / 2 < rho.1.re) {r : ℝ} (hr : 0 < r)
    (c tau l v b u : ℝ) (hb0 : 0 ≤ b)
    (hl : l < (starRingEnd ℂ (zetaSpectralCoordinate rho.1)).re)
    (hv : (starRingEnd ℂ (zetaSpectralCoordinate rho.1)).re < v)
    (hb : b < (starRingEnd ℂ (zetaSpectralCoordinate rho.1)).im)
    (hu : (starRingEnd ℂ (zetaSpectralCoordinate rho.1)).im < u) :
    rectangularAreaIntegral l v b u (suzukiXiSmoothReflectionSource rho r c tau) =
      rectangularBoundaryIntegral l v b u (suzukiXiSmoothReflectionField rho r c tau) +
        (2 * Real.pi * I) * ((analyticZetaZeroMultiplicity rho : ℂ)⁻¹ *
          suzukiSmoothSpectralBoundaryHeat c tau (starRingEnd ℂ (zetaSpectralCoordinate rho.1))) := by
  exact tendsto_nhds_unique
    (tendsto_rectangularAreaIntegralOutsideCenteredSquare_eq_full l v b u
      (starRingEnd ℂ (zetaSpectralCoordinate rho.1)) (suzukiXiSmoothReflectionSource rho r c tau)
      (locallyIntegrable_suzukiXiSmoothReflectionSource rho hr c tau) hl hv hb hu)
    (tendsto_area_suzukiXiSmoothReflectionSource rho hzero hr c tau l v b u hb0 hl hv hb hu)

/-- The source is recovered by ordinary expanding planar integrals,
with the puncture parameter completely removed at fixed smoothing radius. -/
theorem tendsto_integral_suzukiXiSmoothReflectionSource_area
    (rho : NontrivialZetaZero) (hzero : 1 / 2 < rho.1.re) {r tau : ℝ}
    (hr : 0 < r) (htau : 0 < tau) (c : ℝ) :
    Tendsto (fun R : ℝ => ∫ z in [[-R,R]] ×ℂ [[0,R]], suzukiXiSmoothReflectionSource rho r c tau z)
      atTop (𝓝 ((2 * Real.pi * I) * ((analyticZetaZeroMultiplicity rho : ℂ)⁻¹ *
        suzukiSmoothSpectralBoundaryHeat c tau (starRingEnd ℂ (zetaSpectralCoordinate rho.1))))) := by
  let a := starRingEnd ℂ (zetaSpectralCoordinate rho.1)
  let L := (2 * Real.pi * I) * ((analyticZetaZeroMultiplicity rho : ℂ)⁻¹ *
    suzukiSmoothSpectralBoundaryHeat c tau a)
  have ht : Tendsto (fun R : ℝ => rectangularBoundaryIntegral (-R) R 0 R
      (suzukiXiSmoothReflectionField rho r c tau) + L) atTop (𝓝 L) := by
    simpa only [zero_add] using (tendsto_suzukiXiSmoothReflectionField_boundary_zero rho hr htau c).add_const L
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_gt_atTop |a.re|,
    eventually_gt_atTop a.im] with R hR hRe hIm
  have ha : 0 < a.im := by
    dsimp [a]
    rw [zetaSpectralCoordinate_im]
    linarith
  have he := rectangularAreaIntegral_suzukiXiSmoothReflectionSource_eq_boundary_add_mass
    rho hzero hr c tau (-R) R 0 R le_rfl
      (by linarith [neg_le_abs a.re]) (lt_of_le_of_lt (le_abs_self a.re) hRe) ha hIm
  rw [rectangularAreaIntegral_eq_setIntegral (by linarith) hR.le _
    ((locallyIntegrable_suzukiXiSmoothReflectionSource rho hr c tau).integrableOn_isCompact
      (isCompact_uIcc.reProdIm isCompact_uIcc))] at he
  exact he.symm

/-- After the independently vanishing current edges are removed,
the complete signed variation and remainder still recover the strictly
positive reflected source. An independent upper bound for this pair
is the remaining arithmetic obligation. -/
theorem tendsto_suzukiXiReflectionMass_signed_area
    (rho : NontrivialZetaZero) (hzero : 1 / 2 < rho.1.re) {r tau : ℝ}
    (hr : 0 < r) (htau : 0 < tau) (c : ℝ) :
    Tendsto (fun R : ℝ =>
      -4 * I * (r : ℂ)^2 *
        (∫ z in [[-R,R]] ×ℂ [[0,R]], suzukiXiPlanarReflectionMassVariation rho r c tau z) -
      ∫ z in [[-R,R]] ×ℂ [[0,R]], suzukiXiPlanarReflectionMassRemainder rho r c tau z)
      atTop (𝓝 ((2 * Real.pi * I) * ((analyticZetaZeroMultiplicity rho : ℂ)⁻¹ *
        suzukiSmoothSpectralBoundaryHeat c tau (starRingEnd ℂ (zetaSpectralCoordinate rho.1))))) := by
  have ht := (tendsto_integral_suzukiXiSmoothReflectionSource_area rho hzero hr htau c).sub
    (tendsto_suzukiXiReflectionMassEdge_zero rho hr htau.le c)
  simp only [sub_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  rw [integral_suzukiXiSmoothReflectionSource_eq_mass_rectangle rho hr c tau
    (-R) R 0 R (by linarith) hR.le, suzukiXiReflectionMassEdge]
  ring

end
end RiemannGaussian
