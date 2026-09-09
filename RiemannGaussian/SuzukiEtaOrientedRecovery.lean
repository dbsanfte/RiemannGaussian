/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiEtaStripEnergyComparison
import RiemannGaussian.SuzukiEtaExpandingRecovery

/-!
# Vanishing adverse remainder on actual expanding eta contours

The completed-square bound applies to every regular finite truncation
on the oriented phase contours. Its negative part is bounded by an
explicit quartic allowance. On constructed expanding contours, that
negative part tends to zero while the complete pole/strip correction
still tends to the original source plus reflection energy. This does
not assert decay of the whole signed remainder or a bound for the
remaining coupled pole, quadratic-energy and favorable-remainder terms.
-/

open Complex Filter Set Topology
namespace RiemannGaussian
noncomputable section

/-- The adverse part of the actual integrated eta remainder has a
quartic allowance independent of the regular truncation length. -/
theorem suzukiXiEtaFiniteReflectionCompletedStrip_negativePart_le
    (rho : NontrivialZetaZero) (N : ℕ) {R l r b u : ℝ} (hR : 200 ≤ R)
    (hl : R ≤ |l|) (hr : R ≤ |r|) (ha : 2 * |(zetaSpectralCoordinate rho.1).re| ≤ R)
    (hlv : SuzukiXiEtaVerticalAdmissible l) (hrv : SuzukiXiEtaVerticalAdmissible r)
    (hu : 1 / 2 ≤ u) (hreg : SuzukiXiEtaFiniteObservationRegular N l r b u)
    (hlcos : Real.cos (l * Real.log 2) ≤ 0) (hrcos : Real.cos (r * Real.log 2) ≤ 0)
    (hlsin : Real.sin (l * Real.log 2) ≤ -1 / 2) (hrsin : 1 / 2 ≤ Real.sin (r * Real.log 2)) :
    max (-suzukiXiEtaFiniteReflectionCompletedStrip rho l r N) 0 ≤
      512 * (zetaSpectralCoordinate rho.1).im ^ 2 / (Real.log 2 * R ^ 4) := by
  have h := suzukiXiEtaFiniteReflectionCompletedStrip_lower rho N hR hl hr ha hlv hrv hu hreg
    hlcos hrcos hlsin hrsin
  exact max_le (by linarith) (by positivity)

private lemma quartic_allowance_tendsto (rho : NontrivialZetaZero) {R : ℕ → ℝ}
    (hR : Tendsto R atTop atTop) :
    Tendsto (fun n => 512 * (zetaSpectralCoordinate rho.1).im ^ 2 / (Real.log 2 * R n ^ 4))
      atTop (𝓝 0) := by
  have h := ((tendsto_inv_atTop_zero.comp hR).pow 4).const_mul
    (512 * (zetaSpectralCoordinate rho.1).im ^ 2 / Real.log 2)
  simpa only [Function.comp_def, zero_pow (by norm_num : (4 : ℕ) ≠ 0), mul_zero, inv_pow,
    div_mul_eq_div_mul_one_div, one_div] using h

/-- Actual expanding contours with matched sine orientations recover
the complete original source-plus-energy limit and have a vanishing
negative completed remainder. All poles, both strip sides and genuine
regularity at the selected common truncations remain explicit. -/
theorem exists_suzukiXiEtaFiniteReflection_oriented_recovery
    (rho : NontrivialZetaZero) (hzero : 1 / 2 < rho.1.re) :
    ∃ R l r b u : ℕ → ℝ, ∃ N : ℕ → ℕ,
      Tendsto R atTop atTop ∧ Tendsto N atTop atTop ∧
      (∀ n, 200 ≤ R n ∧ 2 * |(zetaSpectralCoordinate rho.1).re| ≤ R n ∧
        SuzukiXiCarrierRealRectangleAdmissible (l n) (r n) (u n) ∧
        (-R n - 1 < l n ∧ l n < -R n) ∧ (R n < r n ∧ r n < R n + 1) ∧
        (R n < u n ∧ u n < R n + 1) ∧
        SuzukiXiEtaVerticalAdmissible (l n) ∧ SuzukiXiEtaVerticalAdmissible (r n) ∧
        Real.cos (l n * Real.log 2) < 0 ∧ Real.cos (r n * Real.log 2) < 0 ∧
        Real.sin (l n * Real.log 2) < -1 / 2 ∧ 1 / 2 < Real.sin (r n * Real.log 2) ∧
        0 < b n ∧ b n < 1 / 2 ∧ SuzukiXiCarrierRectangleAdmissible (l n) (r n) (b n) (u n) ∧
        SuzukiXiEtaFiniteObservationRegular (N n) (l n) (r n) (b n) (u n)) ∧
      (∀ n, |suzukiXiEtaFiniteReflectionCorrection rho (l n) (r n) (b n) (u n) (N n) -
        suzukiXiReflectionStripCorrection rho (l n) (r n) (u n)| < 1 / ((n : ℝ) + 1)) ∧
      (∀ n, max (-suzukiXiEtaFiniteReflectionCompletedStrip rho (l n) (r n) (N n)) 0 ≤
        512 * (zetaSpectralCoordinate rho.1).im ^ 2 / (Real.log 2 * R n ^ 4)) ∧
      Tendsto (fun n => max (-suzukiXiEtaFiniteReflectionCompletedStrip rho (l n) (r n) (N n)) 0)
        atTop (𝓝 0) ∧
      Tendsto (fun n => suzukiXiEtaFiniteReflectionCorrection rho (l n) (r n) (b n) (u n) (N n))
        atTop (𝓝 (2 * Real.pi / (analyticZetaZeroMultiplicity rho : ℝ) +
          suzukiXiReflectionBoundaryEnergy rho)) ∧
      Tendsto (fun n =>
        2 * Real.pi * (suzukiXiReflectionPairQuadratic rho
          (fun a c => suzukiXiEtaFinitePoleMatrix a c (l n) (r n) (b n) (u n) (N n))).re +
        suzukiXiEtaFiniteReflectionStripEnergy rho (l n) (r n) (N n) -
        max (suzukiXiEtaFiniteReflectionCompletedStrip rho (l n) (r n) (N n)) 0)
        atTop (𝓝 (2 * Real.pi / (analyticZetaZeroMultiplicity rho : ℝ) +
          suzukiXiReflectionBoundaryEnergy rho)) := by
  obtain ⟨R, l, r, u, hR, hG⟩ :=
    exists_suzukiXiEtaOrientedPhase_contour_family (2 * |(zetaSpectralCoordinate rho.1).re|)
  have hgeom (n : ℕ) : 1 ≤ R n ∧ 2 * |(zetaSpectralCoordinate rho.1).re| ≤ R n ∧
      SuzukiXiCarrierRealRectangleAdmissible (l n) (r n) (u n) ∧
      (-R n - 1 < l n ∧ l n < -R n) ∧ (R n < r n ∧ r n < R n + 1) ∧
      (R n < u n ∧ u n < R n + 1) ∧
      SuzukiXiEtaVerticalAdmissible (l n) ∧ SuzukiXiEtaVerticalAdmissible (r n) := by
    obtain ⟨hRn, ha, hadm, hl, hr, hu, hlv, hrv, _hphase⟩ := hG n
    exact ⟨by linarith, ha, hadm, hl, hr, hu, hlv, hrv⟩
  obtain ⟨b, N, hN, hb, herr, hlim⟩ :=
    exists_suzukiXiEtaFiniteReflection_recovery_on_contour_family rho hzero R l r u hR hgeom
  have hfloor (n : ℕ) :
      max (-suzukiXiEtaFiniteReflectionCompletedStrip rho (l n) (r n) (N n)) 0 ≤
        512 * (zetaSpectralCoordinate rho.1).im ^ 2 / (Real.log 2 * R n ^ 4) := by
    obtain ⟨hRn, ha, _hadm, hl, hr, hu, hlv, hrv, hlcos, hrcos, hlsin, hrsin⟩ := hG n
    apply suzukiXiEtaFiniteReflectionCompletedStrip_negativePart_le rho (N n) hRn
      (by rw [abs_of_neg (by linarith : l n < 0)]; linarith [hl.2])
      (by rw [abs_of_pos (by linarith : 0 < r n)]; exact hr.1.le)
      ha hlv hrv (by linarith [hu.1]) (hb n).2.2.2 hlcos.le hrcos.le hlsin.le hrsin.le
  have hneg : Tendsto
      (fun n => max (-suzukiXiEtaFiniteReflectionCompletedStrip rho (l n) (r n) (N n)) 0)
      atTop (𝓝 0) :=
    squeeze_zero (fun n => le_max_right _ _) hfloor (quartic_allowance_tendsto rho hR)
  refine ⟨R, l, r, b, u, N, hR, hN, ?_, herr, hfloor, hneg, hlim, ?_⟩
  · intro n
    obtain ⟨hRn, ha, hadm, hl, hr, hu, hlv, hrv, hlcos, hrcos, hlsin, hrsin⟩ := hG n
    exact ⟨hRn, ha, hadm, hl, hr, hu, hlv, hrv, hlcos, hrcos, hlsin, hrsin,
      (hb n).1, (hb n).2.1, (hb n).2.2.1, (hb n).2.2.2⟩
  · have h := hlim.sub hneg
    simp only [sub_zero] at h
    apply h.congr'
    exact Eventually.of_forall fun n => by
      obtain ⟨hRn, _ha, _hadm, _hl, _hr, hu, hlv, hrv, _hphase⟩ := hG n
      exact suzukiXiEtaFiniteReflectionCorrection_sub_negativePart rho (N n) hlv hrv
        (by linarith [hu.1]) (hb n).2.2.2

end
end RiemannGaussian
