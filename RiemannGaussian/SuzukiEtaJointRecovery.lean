/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiEtaStripSides
import RiemannGaussian.SuzukiCarrierPoleWindowGap
import RiemannGaussian.SuzukiCarrierReflectionLimit

/-!
# Arithmetic recovery of the actual joint pole and strip correction

A positive bottom displacement preserves every genuine pole in the
original real-bottom rectangle. The finite eta matrix therefore recovers
that complete pole group and the two original strip sides at once. The
bottom can be chosen before the mixed nodes and complex weights. No
finite-carrier convergence through shared real xi/denominator zeros is
asserted or needed.
-/

open Complex Filter Metric Set Topology
open scoped Topology
namespace RiemannGaussian
noncomputable section

/-- One positive bottom recovers the complete actual complex correction
matrix for all mixed nodes. The original real-bottom pole group and both
closed strip segments are retained, including arbitrary pole orders. -/
theorem exists_suzukiXiEtaFiniteJointCorrection_actual_matrix
    {l r u : ℝ} (hadm : SuzukiXiCarrierRealRectangleAdmissible l r u)
    (hlv : SuzukiXiEtaVerticalAdmissible l) (hrv : SuzukiXiEtaVerticalAdmissible r)
    (huhalf : u ≠ 1 / 2) :
    ∃ b : ℝ, 0 < b ∧ b < 1 / 2 ∧ SuzukiXiCarrierRectangleAdmissible l r b u ∧
      ∀ rho sigma : NontrivialZetaZero,
        Tendsto (suzukiXiEtaFiniteJointCorrection rho sigma l r b u) atTop
          (𝓝 ((2 * Real.pi : ℝ) *
            ∑ c ∈ suzukiXiCarrierGenuinePoleWindow l r 0 u, suzukiXiMixedCarrierPoleResidue rho sigma c -
              suzukiXiCarrierStripSidesGram rho sigma l r)) := by
  obtain ⟨b, hb, hbhalf, hbadm, hwindow⟩ :=
    exists_suzukiXiCarrier_admissible_bottom_same_genuine_poles hadm
  refine ⟨b, hb, hbhalf, hbadm, ?_⟩
  intro rho sigma
  have hp := tendsto_suzukiXiEtaFinitePoleMatrix rho sigma hbadm hlv hrv
    (by linarith) (ne_of_lt hbhalf) huhalf
  rw [hwindow] at hp
  exact (hp.const_mul ((2 * Real.pi : ℝ) : ℂ)).sub
    (tendsto_suzukiXiEtaFiniteStripSidesGram rho sigma hlv hrv)

/-- The same positive bottom works for every finite complex weight
family. All mixed terms share the same eta truncation before the limit. -/
theorem exists_suzukiXiEtaFiniteJointCorrection_actual_weighted
    {l r u : ℝ} (hadm : SuzukiXiCarrierRealRectangleAdmissible l r u)
    (hlv : SuzukiXiEtaVerticalAdmissible l) (hrv : SuzukiXiEtaVerticalAdmissible r)
    (huhalf : u ≠ 1 / 2) :
    ∃ b : ℝ, 0 < b ∧ b < 1 / 2 ∧
      ∀ (S : Finset NontrivialZetaZero) (w : NontrivialZetaZero → ℂ),
        Tendsto (fun N => ∑ rho ∈ S, ∑ sigma ∈ S, starRingEnd ℂ (w rho) * w sigma *
          suzukiXiEtaFiniteJointCorrection rho sigma l r b u N) atTop
          (𝓝 (∑ rho ∈ S, ∑ sigma ∈ S, starRingEnd ℂ (w rho) * w sigma *
            ((2 * Real.pi : ℝ) *
              ∑ c ∈ suzukiXiCarrierGenuinePoleWindow l r 0 u, suzukiXiMixedCarrierPoleResidue rho sigma c -
                suzukiXiCarrierStripSidesGram rho sigma l r))) := by
  obtain ⟨b, hb, hbhalf, _hbadm, hlim⟩ :=
    exists_suzukiXiEtaFiniteJointCorrection_actual_matrix hadm hlv hrv huhalf
  refine ⟨b, hb, hbhalf, ?_⟩
  intro S w
  exact tendsto_finsetSum S fun rho _ => tendsto_finsetSum S fun sigma _ =>
    (hlim rho sigma).const_mul (starRingEnd ℂ (w rho) * w sigma)

/-- The finite arithmetic reflection test keeps the pole and strip
matrices coupled before taking the real part. -/
def suzukiXiEtaFiniteReflectionCorrection (rho : NontrivialZetaZero)
    (l r b u : ℝ) (N : ℕ) : ℝ :=
  (suzukiXiReflectionPairQuadratic rho (fun a c =>
    suzukiXiEtaFiniteJointCorrection a c l r b u N)).re

/-- The original actual reflection correction is recovered by finite
eta contours and strip sides, with every genuine carrier pole retained. -/
theorem exists_suzukiXiEtaFiniteReflectionCorrection_tendsto
    (rho : NontrivialZetaZero) {l r u : ℝ}
    (hadm : SuzukiXiCarrierRealRectangleAdmissible l r u)
    (hlv : SuzukiXiEtaVerticalAdmissible l) (hrv : SuzukiXiEtaVerticalAdmissible r)
    (huhalf : u ≠ 1 / 2) :
    ∃ b : ℝ, 0 < b ∧ b < 1 / 2 ∧ SuzukiXiCarrierRectangleAdmissible l r b u ∧
      Tendsto (suzukiXiEtaFiniteReflectionCorrection rho l r b u) atTop
        (𝓝 (suzukiXiReflectionStripCorrection rho l r u)) := by
  obtain ⟨b, hb, hbhalf, hbadm, hlim⟩ :=
    exists_suzukiXiEtaFiniteJointCorrection_actual_matrix hadm hlv hrv huhalf
  refine ⟨b, hb, hbhalf, hbadm, ?_⟩
  have hQ := (((hlim rho rho).sub (hlim rho rho.conjugatePartner)).sub
    (hlim rho.conjugatePartner rho)).add (hlim rho.conjugatePartner rho.conjugatePartner)
  have hRe := Complex.continuous_re.continuousAt.tendsto.comp hQ
  convert hRe using 1
  congr 1
  simp only [suzukiXiReflectionStripCorrection, suzukiXiReflectionPairQuadratic,
    sub_re, add_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
  ring_nf

/-- Actual eta-compatible expanding outer contour families exist for
every genuine zero with all geometry required by the source-energy limit. -/
theorem exists_suzukiXiEtaReflection_contour_family (rho : NontrivialZetaZero) :
    ∃ R l r u : ℕ → ℝ, Tendsto R atTop atTop ∧
      ∀ n, 1 ≤ R n ∧ 2 * |(zetaSpectralCoordinate rho.1).re| ≤ R n ∧
        SuzukiXiCarrierRealRectangleAdmissible (l n) (r n) (u n) ∧
        (-R n - 1 < l n ∧ l n < -R n) ∧ (R n < r n ∧ r n < R n + 1) ∧
        (R n < u n ∧ u n < R n + 1) ∧
        SuzukiXiEtaVerticalAdmissible (l n) ∧ SuzukiXiEtaVerticalAdmissible (r n) := by
  let B := max 1 (2 * |(zetaSpectralCoordinate rho.1).re|)
  let R := fun n : ℕ => (n : ℝ) + B
  have hR (n : ℕ) : 1 ≤ R n := by
    dsimp only [R, B]
    linarith [Nat.cast_nonneg (α := ℝ) n, le_max_left (1 : ℝ) (2 * |(zetaSpectralCoordinate rho.1).re|)]
  have ha (n : ℕ) : 2 * |(zetaSpectralCoordinate rho.1).re| ≤ R n := by
    dsimp only [R, B]
    linarith [Nat.cast_nonneg (α := ℝ) n, le_max_right (1 : ℝ) (2 * |(zetaSpectralCoordinate rho.1).re|)]
  choose l r u hadm hlv hrv hl hr hu using fun n => exists_suzukiXiEtaRealRectangleAdmissible (hR n)
  exact ⟨R, l, r, u, tendsto_atTop_add_const_right atTop B tendsto_natCast_atTop_atTop,
    fun n => ⟨hR n, ha n, hadm n, hl n, hr n, hu n, hlv n, hrv n⟩⟩

end
end RiemannGaussian
