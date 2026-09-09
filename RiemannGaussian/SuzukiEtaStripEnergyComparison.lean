/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiEtaCompletedStripBound
import RiemannGaussian.SuzukiEtaJointRecovery

/-!
# Retaining the carrier energy in the original finite correction matrix

The actual finite strip matrix is the signed integral of the original
reflection weight times the carrier. Its completed eta remainder splits
off an explicit quadratic strip energy. The resulting equality keeps
the full pole matrix, the energy and the signed remainder together.
The independent quartic remainder floor gives an upper comparison, but
does not bound the remaining pole/energy combination by the source.
-/

open Complex MeasureTheory Set
namespace RiemannGaussian
noncomputable section

private lemma mixed_vertical_integrable (rho sigma : NontrivialZetaZero) (N : ℕ) {v : ℝ}
    (hv : SuzukiXiEtaVerticalAdmissible v)
    (hN : ∀ y ∈ Icc (0 : ℝ) (1 / 2), suzukiEtaFiniteCarrierDenominator N
      (suzukiArithmeticZetaArgument ((v : ℂ) + (y : ℂ) * I)) ≠ 0) :
    IntervalIntegrable (fun y : ℝ => suzukiXiEtaFiniteMixedChannel rho sigma N
      ((v : ℂ) + (y : ℂ) * I)) volume 0 (1 / 2) := by
  have hnode (a : NontrivialZetaZero) (y : ℝ) :
      (v : ℂ) + (y : ℂ) * I ≠ zetaSpectralCoordinate a.1 := by
    intro he
    apply hv.1 _ (Or.inl ((riemannXiSpectral_eq_zero_iff_exists_zetaZero _).mpr ⟨a, rfl⟩))
    rw [← he]
    simp
  have hw : ContinuousOn (fun y : ℝ => 1 /
      ((((v : ℂ) + (y : ℂ) * I) - starRingEnd ℂ (zetaSpectralCoordinate rho.1)) *
        (((v : ℂ) + (y : ℂ) * I) - zetaSpectralCoordinate sigma.1))) (uIcc 0 (1 / 2)) := by
    apply continuousOn_const.div₀ (by fun_prop)
    intro y _hy
    apply mul_ne_zero
    · apply sub_ne_zero.mpr
      simpa only [NontrivialZetaZero.spectralCoordinate_conjugatePartner] using hnode rho.conjugatePartner y
    · exact sub_ne_zero.mpr (hnode sigma y)
  have h := intervalIntegrable_suzukiXiEtaFiniteCarrier_of_regular_path N
    (fun y => (v : ℂ) + (y : ℂ) * I) _ (by fun_prop) hw
    (fun y hy => mem_suzukiXiEtaExtendedCarrierDomain_vertical hv (by
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hy
      linarith [hy.1]))
    (fun y hy => hN y (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] using hy))
  simpa only [suzukiXiEtaFiniteMixedChannel, div_eq_mul_inv, one_mul, mul_comm] using h

/-- The finite mixed reflection test retains the very same complex
weight as the original carrier, including totalized node values. -/
theorem suzukiXiEtaFiniteReflectionChannel_eq_weight_mul
    (rho : NontrivialZetaZero) (N : ℕ) (z : ℂ) :
    suzukiXiReflectionPairQuadratic rho (fun a b => suzukiXiEtaFiniteMixedChannel a b N z) =
      suzukiXiReflectionWeight rho z * suzukiXiEtaFiniteCarrier N z := by
  simp only [suzukiXiReflectionPairQuadratic, suzukiXiEtaFiniteMixedChannel,
    suzukiXiReflectionWeight, suzukiXiReflectionCauchyDifference,
    NontrivialZetaZero.spectralCoordinate_conjugatePartner, conj_conj, div_eq_mul_inv, mul_inv]
  ring

private lemma reflection_integrable (rho : NontrivialZetaZero) (N : ℕ) {v : ℝ}
    (hv : SuzukiXiEtaVerticalAdmissible v)
    (hN : ∀ y ∈ Icc (0 : ℝ) (1 / 2), suzukiEtaFiniteCarrierDenominator N
      (suzukiArithmeticZetaArgument ((v : ℂ) + (y : ℂ) * I)) ≠ 0) :
    IntervalIntegrable (fun y : ℝ => suzukiXiReflectionWeight rho ((v : ℂ) + (y : ℂ) * I) *
      suzukiXiEtaFiniteCarrier N ((v : ℂ) + (y : ℂ) * I)) volume 0 (1 / 2) := by
  have hK (a b : NontrivialZetaZero) := mixed_vertical_integrable a b N hv hN
  have h : IntervalIntegrable (fun y : ℝ => suzukiXiReflectionPairQuadratic rho
      (fun a b => suzukiXiEtaFiniteMixedChannel a b N ((v : ℂ) + (y : ℂ) * I))) volume 0 (1 / 2) :=
    (((hK rho rho).sub (hK rho rho.conjugatePartner)).sub
      (hK rho.conjugatePartner rho)).add (hK rho.conjugatePartner rho.conjugatePartner)
  simpa only [suzukiXiEtaFiniteReflectionChannel_eq_weight_mul] using h

/-- The complete finite strip Gram correction is exactly its two
oriented real integrals. Every mixed entry is genuinely integrable. -/
theorem suzukiXiEtaFiniteReflectionStripGram_eq_integral
    (rho : NontrivialZetaZero) (N : ℕ) {l r b u : ℝ}
    (hlv : SuzukiXiEtaVerticalAdmissible l) (hrv : SuzukiXiEtaVerticalAdmissible r)
    (hu : 1 / 2 ≤ u) (hreg : SuzukiXiEtaFiniteObservationRegular N l r b u) :
    (suzukiXiReflectionPairQuadratic rho (fun a c => suzukiXiEtaFiniteStripSidesGram a c l r N)).re =
      ∫ y : ℝ in 0..(1 / 2),
        (suzukiXiReflectionWeight rho ((r : ℂ) + (y : ℂ) * I) *
          suzukiXiEtaFiniteCarrier N ((r : ℂ) + (y : ℂ) * I)).re -
        (suzukiXiReflectionWeight rho ((l : ℂ) + (y : ℂ) * I) *
          suzukiXiEtaFiniteCarrier N ((l : ℂ) + (y : ℂ) * I)).re := by
  have hNl (y : ℝ) (hy : y ∈ Icc 0 (1 / 2)) := (hreg.strip hu hy).1
  have hNr (y : ℝ) (hy : y ∈ Icc 0 (1 / 2)) := (hreg.strip hu hy).2
  have hpath (v : ℝ) (hv : SuzukiXiEtaVerticalAdmissible v)
      (hN : ∀ y ∈ Icc (0 : ℝ) (1 / 2), suzukiEtaFiniteCarrierDenominator N
        (suzukiArithmeticZetaArgument ((v : ℂ) + (y : ℂ) * I)) ≠ 0) :
      suzukiXiReflectionPairQuadratic rho (fun a c => ∫ y : ℝ in 0..(1 / 2),
        suzukiXiEtaFiniteMixedChannel a c N ((v : ℂ) + (y : ℂ) * I)) =
      ∫ y : ℝ in 0..(1 / 2), suzukiXiReflectionWeight rho ((v : ℂ) + (y : ℂ) * I) *
        suzukiXiEtaFiniteCarrier N ((v : ℂ) + (y : ℂ) * I) := by
    rw [suzukiXiReflectionPairQuadratic_intervalIntegral rho _ _ _
      (fun a c => mixed_vertical_integrable a c N hv hN)]
    simp only [suzukiXiEtaFiniteReflectionChannel_eq_weight_mul]
  have hside : suzukiXiReflectionPairQuadratic rho (fun a c => suzukiXiEtaFiniteStripSides a c l r N) =
      I * (∫ y : ℝ in 0..(1 / 2), suzukiXiReflectionWeight rho ((r : ℂ) + (y : ℂ) * I) *
        suzukiXiEtaFiniteCarrier N ((r : ℂ) + (y : ℂ) * I)) -
      I * (∫ y : ℝ in 0..(1 / 2), suzukiXiReflectionWeight rho ((l : ℂ) + (y : ℂ) * I) *
        suzukiXiEtaFiniteCarrier N ((l : ℂ) + (y : ℂ) * I)) := by
    rw [← hpath r hrv hNr, ← hpath l hlv hNl]
    unfold suzukiXiReflectionPairQuadratic suzukiXiEtaFiniteStripSides
    ring
  have hproj (w : ℂ) : ((w - starRingEnd ℂ w) / (2 * I)).re = w.im := by
    have he : (w - starRingEnd ℂ w) / (2 * I) = (w.im : ℂ) := by
      rw [Complex.sub_conj]
      push_cast
      field_simp
    rw [he, ofReal_re]
  unfold suzukiXiEtaFiniteStripSidesGram
  rw [suzukiXiReflectionPairQuadratic_signedProjection, hproj, hside]
  simp only [sub_im, I_mul_im]
  have hir := reflection_integrable rho N hrv hNr
  have hil := reflection_integrable rho N hlv hNl
  have hre {f : ℝ → ℂ} (hf : IntervalIntegrable f volume 0 (1 / 2)) :
      (∫ y : ℝ in 0..(1 / 2), f y).re = ∫ y : ℝ in 0..(1 / 2), (f y).re :=
    (intervalIntegral.intervalIntegral_re hf).symm
  rw [hre hir, hre hil]
  exact (intervalIntegral.integral_sub ⟨hir.1.re, hir.2.re⟩ ⟨hil.1.re, hil.2.re⟩).symm

/-- The actual quadratic strip energy, with the dyadic coefficients
and both complex reflection weights retained before integration. -/
def suzukiXiEtaFiniteReflectionStripEnergyDensity
    (rho : NontrivialZetaZero) (l r : ℝ) (N : ℕ) (y : ℝ) : ℝ :=
    -suzukiEtaDyadicWeightCoefficient (I * suzukiXiReflectionWeight rho ((r : ℂ) + (y : ℂ) * I))
      (suzukiArithmeticZetaArgument ((r : ℂ) + (y : ℂ) * I)) *
      normSq (suzukiXiEtaFiniteCarrier N ((r : ℂ) + (y : ℂ) * I)) -
    suzukiEtaDyadicWeightCoefficient (-I * suzukiXiReflectionWeight rho ((l : ℂ) + (y : ℂ) * I))
      (suzukiArithmeticZetaArgument ((l : ℂ) + (y : ℂ) * I)) *
      normSq (suzukiXiEtaFiniteCarrier N ((l : ℂ) + (y : ℂ) * I))

/-- Before integration the quadratic energy is exactly the completed
remainder minus the original oriented carrier density. -/
theorem suzukiXiEtaFiniteReflectionStripEnergyDensity_eq_completed_sub_carrier
    (rho : NontrivialZetaZero) (l r : ℝ) (N : ℕ) (y : ℝ) :
    suzukiXiEtaFiniteReflectionStripEnergyDensity rho l r N y =
      (suzukiXiEtaFiniteReflectionCompletedSide rho r N y -
        suzukiXiEtaFiniteReflectionCompletedSide rho l N y) -
      ((suzukiXiReflectionWeight rho ((r : ℂ) + (y : ℂ) * I) *
          suzukiXiEtaFiniteCarrier N ((r : ℂ) + (y : ℂ) * I)).re -
        (suzukiXiReflectionWeight rho ((l : ℂ) + (y : ℂ) * I) *
          suzukiXiEtaFiniteCarrier N ((l : ℂ) + (y : ℂ) * I)).re) := by
  rw [suzukiXiEtaFiniteReflectionCompletedSide_eq_carrier_sub_energy,
    suzukiXiEtaFiniteReflectionCompletedSide_eq_carrier_sub_energy]
  have hneg (W s : ℂ) : suzukiEtaDyadicWeightCoefficient (-I * W) s =
      -suzukiEtaDyadicWeightCoefficient (I * W) s := by simp [suzukiEtaDyadicWeightCoefficient]
  unfold suzukiXiEtaFiniteReflectionStripEnergyDensity
  rw [hneg]
  ring

/-- The quadratic energy is genuinely integrable for each regular
finite truncation on the actual strip segments. -/
theorem intervalIntegrable_suzukiXiEtaFiniteReflectionStripEnergyDensity
    (rho : NontrivialZetaZero) (N : ℕ) {l r b u : ℝ}
    (hlv : SuzukiXiEtaVerticalAdmissible l) (hrv : SuzukiXiEtaVerticalAdmissible r)
    (hu : 1 / 2 ≤ u) (hreg : SuzukiXiEtaFiniteObservationRegular N l r b u) :
    IntervalIntegrable (suzukiXiEtaFiniteReflectionStripEnergyDensity rho l r N) volume 0 (1 / 2) := by
  have hNl (y : ℝ) (hy : y ∈ Icc 0 (1 / 2)) := (hreg.strip hu hy).1
  have hNr (y : ℝ) (hy : y ∈ Icc 0 (1 / 2)) := (hreg.strip hu hy).2
  have hil := intervalIntegrable_suzukiXiEtaFiniteReflectionCompletedSide rho N hlv hNl
  have hir := intervalIntegrable_suzukiXiEtaFiniteReflectionCompletedSide rho N hrv hNr
  have hre {f : ℝ → ℂ} (hf : IntervalIntegrable f volume 0 (1 / 2)) :
      IntervalIntegrable (fun y => (f y).re) volume 0 (1 / 2) := ⟨hf.1.re, hf.2.re⟩
  have hsl := hre (reflection_integrable rho N hlv hNl)
  have hsr := hre (reflection_integrable rho N hrv hNr)
  change IntervalIntegrable (fun y => suzukiXiEtaFiniteReflectionStripEnergyDensity rho l r N y)
    volume 0 (1 / 2)
  simpa only [suzukiXiEtaFiniteReflectionStripEnergyDensity_eq_completed_sub_carrier] using
    (hir.sub hil).sub (hsr.sub hsl)

/-- The complete strip energy integrates its literal signed density,
with the dyadic coefficients and both side orientations retained. -/
def suzukiXiEtaFiniteReflectionStripEnergy (rho : NontrivialZetaZero) (l r : ℝ) (N : ℕ) : ℝ :=
  ∫ y : ℝ in 0..(1 / 2), suzukiXiEtaFiniteReflectionStripEnergyDensity rho l r N y

/-- The matched phase quadrants make the retained quadratic strip
energy nonnegative for every regular truncation, using its genuine integral. -/
theorem suzukiXiEtaFiniteReflectionStripEnergy_nonneg
    (rho : NontrivialZetaZero) (N : ℕ) {l r b u : ℝ}
    (hlv : SuzukiXiEtaVerticalAdmissible l) (hrv : SuzukiXiEtaVerticalAdmissible r)
    (hu : 1 / 2 ≤ u) (hreg : SuzukiXiEtaFiniteObservationRegular N l r b u)
    (hl : 100 ≤ |l - (zetaSpectralCoordinate rho.1).re|)
    (hr : 100 ≤ |r - (zetaSpectralCoordinate rho.1).re|)
    (hlcos : Real.cos (l * Real.log 2) ≤ 0) (hrcos : Real.cos (r * Real.log 2) ≤ 0)
    (hlsin : Real.sin (l * Real.log 2) ≤ -1 / 2) (hrsin : 1 / 2 ≤ Real.sin (r * Real.log 2)) :
    0 ≤ suzukiXiEtaFiniteReflectionStripEnergy rho l r N := by
  have hpoint (y : ℝ) (hy : y ∈ Icc 0 (1 / 2)) :
      0 ≤ suzukiXiEtaFiniteReflectionStripEnergyDensity rho l r N y := by
    have hlc := suzukiEtaDyadicWeightCoefficient_reflection_left_le rho hl hy hlcos hlsin
    have hrc := suzukiEtaDyadicWeightCoefficient_reflection_right_le rho hr hy hrcos hrsin
    have hlog : 0 ≤ Real.log 2 / 32 := by positivity
    have hle : suzukiEtaDyadicWeightCoefficient
        (-I * suzukiXiReflectionWeight rho ((l : ℂ) + (y : ℂ) * I))
          (suzukiArithmeticZetaArgument ((l : ℂ) + (y : ℂ) * I)) ≤ 0 :=
      hlc.trans (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hlog) (norm_nonneg _))
    have hre : suzukiEtaDyadicWeightCoefficient
        (I * suzukiXiReflectionWeight rho ((r : ℂ) + (y : ℂ) * I))
          (suzukiArithmeticZetaArgument ((r : ℂ) + (y : ℂ) * I)) ≤ 0 :=
      hrc.trans (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hlog) (norm_nonneg _))
    exact sub_nonneg.mpr ((mul_nonpos_of_nonpos_of_nonneg hle (normSq_nonneg _)).trans
      (mul_nonneg (neg_nonneg.mpr hre) (normSq_nonneg _)))
  have h := intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := 1 / 2)
    (by norm_num) intervalIntegrable_const
    (intervalIntegrable_suzukiXiEtaFiniteReflectionStripEnergyDensity rho N hlv hrv hu hreg) hpoint
  simpa only [intervalIntegral.integral_zero, suzukiXiEtaFiniteReflectionStripEnergy] using h

/-- The energy is exactly the completed remainder minus the original
strip Gram correction. This preserves their cancellation. -/
theorem suzukiXiEtaFiniteReflectionStripEnergy_eq_completed_sub_strip
    (rho : NontrivialZetaZero) (N : ℕ) {l r b u : ℝ}
    (hlv : SuzukiXiEtaVerticalAdmissible l) (hrv : SuzukiXiEtaVerticalAdmissible r)
    (hu : 1 / 2 ≤ u) (hreg : SuzukiXiEtaFiniteObservationRegular N l r b u) :
    suzukiXiEtaFiniteReflectionStripEnergy rho l r N =
      suzukiXiEtaFiniteReflectionCompletedStrip rho l r N -
        (suzukiXiReflectionPairQuadratic rho (fun a c => suzukiXiEtaFiniteStripSidesGram a c l r N)).re := by
  have hNl (y : ℝ) (hy : y ∈ Icc 0 (1 / 2)) := (hreg.strip hu hy).1
  have hNr (y : ℝ) (hy : y ∈ Icc 0 (1 / 2)) := (hreg.strip hu hy).2
  have hil := intervalIntegrable_suzukiXiEtaFiniteReflectionCompletedSide rho N hlv hNl
  have hir := intervalIntegrable_suzukiXiEtaFiniteReflectionCompletedSide rho N hrv hNr
  have hre {f : ℝ → ℂ} (hf : IntervalIntegrable f volume 0 (1 / 2)) :
      IntervalIntegrable (fun y => (f y).re) volume 0 (1 / 2) := ⟨hf.1.re, hf.2.re⟩
  have hsl := hre (reflection_integrable rho N hlv hNl)
  have hsr := hre (reflection_integrable rho N hrv hNr)
  rw [suzukiXiEtaFiniteReflectionStripGram_eq_integral rho N hlv hrv hu hreg]
  unfold suzukiXiEtaFiniteReflectionCompletedStrip suzukiXiEtaFiniteReflectionStripEnergy
  rw [← intervalIntegral.integral_sub (hir.sub hil) (hsr.sub hsl)]
  simp only [suzukiXiEtaFiniteReflectionStripEnergyDensity_eq_completed_sub_carrier]

/-- The full finite joint correction keeps the complete pole matrix,
the quadratic strip energy and the favorable signed remainder together. -/
theorem suzukiXiEtaFiniteReflectionCorrection_eq_poles_add_energy_sub_completed
    (rho : NontrivialZetaZero) (N : ℕ) {l r b u : ℝ}
    (hlv : SuzukiXiEtaVerticalAdmissible l) (hrv : SuzukiXiEtaVerticalAdmissible r)
    (hu : 1 / 2 ≤ u) (hreg : SuzukiXiEtaFiniteObservationRegular N l r b u) :
    suzukiXiEtaFiniteReflectionCorrection rho l r b u N =
      2 * Real.pi *
        (suzukiXiReflectionPairQuadratic rho (fun a c => suzukiXiEtaFinitePoleMatrix a c l r b u N)).re +
      suzukiXiEtaFiniteReflectionStripEnergy rho l r N -
      suzukiXiEtaFiniteReflectionCompletedStrip rho l r N := by
  rw [suzukiXiEtaFiniteReflectionStripEnergy_eq_completed_sub_strip rho N hlv hrv hu hreg]
  unfold suzukiXiEtaFiniteReflectionCorrection suzukiXiEtaFiniteJointCorrection suzukiXiReflectionPairQuadratic
  simp only [add_re, sub_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
  ring

/-- Removing only the adverse part of the completed remainder leaves
its favorable part coupled to the pole term and quadratic energy. -/
theorem suzukiXiEtaFiniteReflectionCorrection_sub_negativePart
    (rho : NontrivialZetaZero) (N : ℕ) {l r b u : ℝ}
    (hlv : SuzukiXiEtaVerticalAdmissible l) (hrv : SuzukiXiEtaVerticalAdmissible r)
    (hu : 1 / 2 ≤ u) (hreg : SuzukiXiEtaFiniteObservationRegular N l r b u) :
    suzukiXiEtaFiniteReflectionCorrection rho l r b u N -
        max (-suzukiXiEtaFiniteReflectionCompletedStrip rho l r N) 0 =
      2 * Real.pi *
        (suzukiXiReflectionPairQuadratic rho (fun a c => suzukiXiEtaFinitePoleMatrix a c l r b u N)).re +
      suzukiXiEtaFiniteReflectionStripEnergy rho l r N -
      max (suzukiXiEtaFiniteReflectionCompletedStrip rho l r N) 0 := by
  rw [suzukiXiEtaFiniteReflectionCorrection_eq_poles_add_energy_sub_completed rho N hlv hrv hu hreg]
  have h := max_zero_sub_max_neg_zero_eq_self (suzukiXiEtaFiniteReflectionCompletedStrip rho l r N)
  linarith

/-- The independent signed arithmetic floor supplies a quartic upper
allowance for the full joint correction. The remaining pole/energy
budget is explicit and is not bounded by the zero source here. -/
theorem suzukiXiEtaFiniteReflectionCorrection_le_poles_add_energy
    (rho : NontrivialZetaZero) (N : ℕ) {R l r b u : ℝ} (hR : 200 ≤ R)
    (hl : R ≤ |l|) (hr : R ≤ |r|) (ha : 2 * |(zetaSpectralCoordinate rho.1).re| ≤ R)
    (hlv : SuzukiXiEtaVerticalAdmissible l) (hrv : SuzukiXiEtaVerticalAdmissible r)
    (hu : 1 / 2 ≤ u) (hreg : SuzukiXiEtaFiniteObservationRegular N l r b u)
    (hlcos : Real.cos (l * Real.log 2) ≤ 0) (hrcos : Real.cos (r * Real.log 2) ≤ 0)
    (hlsin : Real.sin (l * Real.log 2) ≤ -1 / 2) (hrsin : 1 / 2 ≤ Real.sin (r * Real.log 2)) :
    suzukiXiEtaFiniteReflectionCorrection rho l r b u N ≤
      2 * Real.pi *
        (suzukiXiReflectionPairQuadratic rho (fun a c => suzukiXiEtaFinitePoleMatrix a c l r b u N)).re +
      suzukiXiEtaFiniteReflectionStripEnergy rho l r N +
      512 * (zetaSpectralCoordinate rho.1).im ^ 2 / (Real.log 2 * R ^ 4) := by
  rw [suzukiXiEtaFiniteReflectionCorrection_eq_poles_add_energy_sub_completed rho N hlv hrv hu hreg]
  have h := suzukiXiEtaFiniteReflectionCompletedStrip_lower rho N hR hl hr ha hlv hrv hu hreg
    hlcos hrcos hlsin hrsin
  linarith

end
end RiemannGaussian
