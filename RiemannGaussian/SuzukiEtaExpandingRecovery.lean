/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiEtaJointRecovery
import RiemannGaussian.SuzukiEtaObservationRegularity

/-!
# Vanishing arithmetic recovery error along expanding Suzuki contours

Choose actual eta-compatible outer rectangles and positive bottom lifts
that retain every genuine pole. A sufficiently long common eta truncation
at each scale approximates the entire signed joint correction within
`1/(n+1)`. Both the outer scale and the truncation length tend to infinity.
The resulting finite arithmetic expression inherits the original exact
source-plus-energy limit. This is an adapted diagonal approximation, not
a uniform bound for every pair of contour and truncation sizes and not
the independent source ceiling required for RH.
-/

open Complex Filter Metric Set Topology
open scoped Topology
namespace RiemannGaussian
noncomputable section

/-- Any actual compatible expanding contour family admits one common
eta truncation per contour with vanishing recovery error. Geometric
constraints such as favorable dyadic phases can be imposed upstream
and are preserved by this construction. -/
theorem exists_suzukiXiEtaFiniteReflection_recovery_on_contour_family
    (rho : NontrivialZetaZero) (hzero : 1 / 2 < rho.1.re)
    (R l r u : ℕ → ℝ) (hR : Tendsto R atTop atTop)
    (hG : ∀ n, 1 ≤ R n ∧ 2 * |(zetaSpectralCoordinate rho.1).re| ≤ R n ∧
        SuzukiXiCarrierRealRectangleAdmissible (l n) (r n) (u n) ∧
        (-R n - 1 < l n ∧ l n < -R n) ∧ (R n < r n ∧ r n < R n + 1) ∧
        (R n < u n ∧ u n < R n + 1) ∧
        SuzukiXiEtaVerticalAdmissible (l n) ∧ SuzukiXiEtaVerticalAdmissible (r n)) :
    ∃ b : ℕ → ℝ, ∃ N : ℕ → ℕ, Tendsto N atTop atTop ∧
      (∀ n, 0 < b n ∧ b n < 1 / 2 ∧
        SuzukiXiCarrierRectangleAdmissible (l n) (r n) (b n) (u n) ∧
        SuzukiXiEtaFiniteObservationRegular (N n) (l n) (r n) (b n) (u n)) ∧
      (∀ n, |suzukiXiEtaFiniteReflectionCorrection rho (l n) (r n) (b n) (u n) (N n) -
        suzukiXiReflectionStripCorrection rho (l n) (r n) (u n)| < 1 / ((n : ℝ) + 1)) ∧
      Tendsto (fun n => suzukiXiEtaFiniteReflectionCorrection rho (l n) (r n) (b n) (u n) (N n))
        atTop (𝓝 (2 * Real.pi / (analyticZetaZeroMultiplicity rho : ℝ) +
          suzukiXiReflectionBoundaryEnergy rho)) := by
  have hrec (n : ℕ) : ∃ b : ℝ, 0 < b ∧ b < 1 / 2 ∧
      SuzukiXiCarrierRectangleAdmissible (l n) (r n) b (u n) ∧
      Tendsto (suzukiXiEtaFiniteReflectionCorrection rho (l n) (r n) b (u n)) atTop
        (𝓝 (suzukiXiReflectionStripCorrection rho (l n) (r n) (u n))) := by
    obtain ⟨hRn, _ha, hadm, _hl, _hr, hu, hlv, hrv⟩ := hG n
    exact exists_suzukiXiEtaFiniteReflectionCorrection_tendsto rho hadm hlv hrv (by linarith [hu.1])
  choose b hb hbhalf hbadm hlim using hrec
  have hchoose (n : ℕ) : ∃ M : ℕ, n ≤ M ∧
      SuzukiXiEtaFiniteObservationRegular M (l n) (r n) (b n) (u n) ∧
      |suzukiXiEtaFiniteReflectionCorrection rho (l n) (r n) (b n) (u n) M -
        suzukiXiReflectionStripCorrection rho (l n) (r n) (u n)| < 1 / ((n : ℝ) + 1) := by
    have heps : 0 < 1 / ((n : ℝ) + 1) := one_div_pos.mpr (by positivity)
    have hsmall := (Metric.tendsto_nhds.mp (hlim n)) _ heps
    obtain ⟨hRn, _ha, _hadm, _hl, _hr, hu, hlv, hrv⟩ := hG n
    have hreg := eventually_suzukiXiEtaFiniteObservationRegular (hbadm n) hlv hrv
      (hb n) (ne_of_lt (hbhalf n)) (by linarith [hu.1])
    obtain ⟨M, hMN, hMreg, hM⟩ := ((eventually_ge_atTop n).and (hreg.and hsmall)).exists
    exact ⟨M, hMN, hMreg, by simpa only [Real.dist_eq] using hM⟩
  choose N hNge hNreg hNerr using hchoose
  have hN : Tendsto N atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro k
    filter_upwards [eventually_ge_atTop k] with n hn
    exact hn.trans (hNge n)
  have hgeom (n : ℕ) : 1 ≤ R n ∧ 2 * |(zetaSpectralCoordinate rho.1).re| ≤ R n ∧
      SuzukiXiCarrierRealRectangleAdmissible (l n) (r n) (u n) ∧
      (-R n - 1 < l n ∧ l n < -R n) ∧ (R n < r n ∧ r n < R n + 1) ∧
        (R n < u n ∧ u n < R n + 1) := by
    obtain ⟨hRn, ha, hadm, hl, hr, hu, _hv⟩ := hG n
    exact ⟨hRn, ha, hadm, hl, hr, hu⟩
  have hJ := tendsto_suzukiXiReflectionStripCorrection_source_add_energy rho hzero hR hgeom
  have heps : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
  have herr : Tendsto (fun n =>
      suzukiXiEtaFiniteReflectionCorrection rho (l n) (r n) (b n) (u n) (N n) -
        suzukiXiReflectionStripCorrection rho (l n) (r n) (u n)) atTop (𝓝 (0 : ℝ)) := by
    apply squeeze_zero_norm' _ heps
    exact Eventually.of_forall fun n => by simpa only [Real.norm_eq_abs] using (hNerr n).le
  refine ⟨b, N, hN, fun n => ⟨hb n, hbhalf n, hbadm n, hNreg n⟩, hNerr, ?_⟩
  simpa only [sub_add_cancel, zero_add] using herr.add hJ

/-- Actual finite eta expressions recover the complete joint correction
with a vanishing prescribed error along constructed expanding contours.
All poles and both strip sides use one common truncation at each scale.
The exact source and strictly positive reflection energy remain in the
limit under a hypothetical right-half zero. -/
theorem exists_suzukiXiEtaFiniteReflection_expanding_recovery
    (rho : NontrivialZetaZero) (hzero : 1 / 2 < rho.1.re) :
    ∃ R l r b u : ℕ → ℝ, ∃ N : ℕ → ℕ,
      Tendsto R atTop atTop ∧ Tendsto N atTop atTop ∧
      (∀ n, 1 ≤ R n ∧ 2 * |(zetaSpectralCoordinate rho.1).re| ≤ R n ∧
        SuzukiXiCarrierRealRectangleAdmissible (l n) (r n) (u n) ∧
        (-R n - 1 < l n ∧ l n < -R n) ∧ (R n < r n ∧ r n < R n + 1) ∧
        (R n < u n ∧ u n < R n + 1) ∧
        SuzukiXiEtaVerticalAdmissible (l n) ∧ SuzukiXiEtaVerticalAdmissible (r n) ∧
        0 < b n ∧ b n < 1 / 2 ∧ SuzukiXiCarrierRectangleAdmissible (l n) (r n) (b n) (u n)) ∧
      (∀ n, |suzukiXiEtaFiniteReflectionCorrection rho (l n) (r n) (b n) (u n) (N n) -
        suzukiXiReflectionStripCorrection rho (l n) (r n) (u n)| < 1 / ((n : ℝ) + 1)) ∧
      Tendsto (fun n => suzukiXiEtaFiniteReflectionCorrection rho (l n) (r n) (b n) (u n) (N n))
        atTop (𝓝 (2 * Real.pi / (analyticZetaZeroMultiplicity rho : ℝ) +
          suzukiXiReflectionBoundaryEnergy rho)) := by
  obtain ⟨R, l, r, u, hR, hG⟩ := exists_suzukiXiEtaReflection_contour_family rho
  obtain ⟨b, N, hN, hb, herr, hlim⟩ :=
    exists_suzukiXiEtaFiniteReflection_recovery_on_contour_family rho hzero R l r u hR hG
  refine ⟨R, l, r, b, u, N, hR, hN, ?_, herr, hlim⟩
  intro n
  obtain ⟨hRn, ha, hadm, hl, hr, hu, hlv, hrv⟩ := hG n
  exact ⟨hRn, ha, hadm, hl, hr, hu, hlv, hrv, (hb n).1, (hb n).2.1, (hb n).2.2.1⟩

end
end RiemannGaussian
