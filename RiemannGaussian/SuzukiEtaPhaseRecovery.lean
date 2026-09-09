/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiEtaExpandingRecovery
import RiemannGaussian.SuzukiEtaPhaseContours
import RiemannGaussian.SuzukiEtaPhaseEnergy

/-!
# Complete arithmetic recovery on favorable dyadic phases

The phase-controlled actual contours support the complete previously
proved arithmetic recovery. Every genuine pole and both strip sides
remain present, the common truncation error tends to zero, and both
vertical phases support the independent completion estimates.
The positive source-plus-energy limit is unchanged. Controlling the
remaining signed arithmetic term is still necessary for a contradiction.
-/

open Complex Filter Set Topology
namespace RiemannGaussian
noncomputable section

/-- Favorable dyadic phases coexist with the full finite arithmetic
source-energy limit for every hypothetical right-half zero. The phase
choice preserves all poles, both strip sides and the vanishing common
truncation error; it does not assert an independent source ceiling. -/
theorem exists_suzukiXiEtaFiniteReflection_phase_recovery
    (rho : NontrivialZetaZero) (hzero : 1 / 2 < rho.1.re) :
    ∃ R l r b u : ℕ → ℝ, ∃ N : ℕ → ℕ,
      Tendsto R atTop atTop ∧ Tendsto N atTop atTop ∧
      (∀ n, 1 ≤ R n ∧ 2 * |(zetaSpectralCoordinate rho.1).re| ≤ R n ∧
        SuzukiXiCarrierRealRectangleAdmissible (l n) (r n) (u n) ∧
        (-R n - 1 < l n ∧ l n < -R n) ∧ (R n < r n ∧ r n < R n + 1) ∧
        (R n < u n ∧ u n < R n + 1) ∧
        SuzukiXiEtaVerticalAdmissible (l n) ∧ SuzukiXiEtaVerticalAdmissible (r n) ∧
        Real.cos (l n * Real.log 2) < 0 ∧ Real.cos (r n * Real.log 2) < 0 ∧
        0 < b n ∧ b n < 1 / 2 ∧ SuzukiXiCarrierRectangleAdmissible (l n) (r n) (b n) (u n) ∧
        SuzukiXiEtaFiniteObservationRegular (N n) (l n) (r n) (b n) (u n)) ∧
      (∀ n, |suzukiXiEtaFiniteReflectionCorrection rho (l n) (r n) (b n) (u n) (N n) -
        suzukiXiReflectionStripCorrection rho (l n) (r n) (u n)| < 1 / ((n : ℝ) + 1)) ∧
      Tendsto (fun n => suzukiXiEtaFiniteReflectionCorrection rho (l n) (r n) (b n) (u n) (N n))
        atTop (𝓝 (2 * Real.pi / (analyticZetaZeroMultiplicity rho : ℝ) +
          suzukiXiReflectionBoundaryEnergy rho)) := by
  obtain ⟨R, l, r, u, hR, hG⟩ :=
    exists_suzukiXiEtaPhase_contour_family (2 * |(zetaSpectralCoordinate rho.1).re|)
  have hgeom (n : ℕ) : 1 ≤ R n ∧ 2 * |(zetaSpectralCoordinate rho.1).re| ≤ R n ∧
      SuzukiXiCarrierRealRectangleAdmissible (l n) (r n) (u n) ∧
      (-R n - 1 < l n ∧ l n < -R n) ∧ (R n < r n ∧ r n < R n + 1) ∧
      (R n < u n ∧ u n < R n + 1) ∧
      SuzukiXiEtaVerticalAdmissible (l n) ∧ SuzukiXiEtaVerticalAdmissible (r n) := by
    obtain ⟨hRn, ha, hadm, hl, hr, hu, hlv, hrv, _hphase⟩ := hG n
    exact ⟨hRn, ha, hadm, hl, hr, hu, hlv, hrv⟩
  obtain ⟨b, N, hN, hb, herr, hlim⟩ :=
    exists_suzukiXiEtaFiniteReflection_recovery_on_contour_family rho hzero R l r u hR hgeom
  refine ⟨R, l, r, b, u, N, hR, hN, ?_, herr, hlim⟩
  intro n
  obtain ⟨hRn, ha, hadm, hl, hr, hu, hlv, hrv, hlcos, hrcos⟩ := hG n
  exact ⟨hRn, ha, hadm, hl, hr, hu, hlv, hrv, hlcos, hrcos, hb n⟩

end
end RiemannGaussian
