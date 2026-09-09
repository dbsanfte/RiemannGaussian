/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiEtaContourGeometry
import RiemannGaussian.SuzukiEtaPoleGroups
import RiemannGaussian.SuzukiCarrierContourStrip

/-!
# Finite arithmetic contours and both complete strip sides

The same eta truncation now recovers entire upper contour pole groups and
the two original vertical segments including their endpoints. We retain
the full complex pole matrix and the conjugate-transposed strip matrix,
then couple their arithmetic approximations before any signed projection.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Topology
namespace RiemannGaussian
noncomputable section

private lemma node_weight_continuous (rho sigma : NontrivialZetaZero)
    {a b : ℝ} {gamma : ℝ → ℂ} (hc : ContinuousOn gamma (uIcc a b))
    (hne : ∀ t ∈ uIcc a b, gamma t ∉ suzukiXiCarrierSingularSet) :
    ContinuousOn (fun t => 1 /
      ((gamma t - starRingEnd ℂ (zetaSpectralCoordinate rho.1)) *
        (gamma t - zetaSpectralCoordinate sigma.1))) (uIcc a b) := by
  apply continuousOn_const.div₀ ((hc.sub continuousOn_const).mul (hc.sub continuousOn_const))
  intro t ht
  apply mul_ne_zero
  · apply sub_ne_zero.mpr
    intro he
    apply hne t ht
    left
    rw [he, ← NontrivialZetaZero.spectralCoordinate_conjugatePartner]
    exact (riemannXiSpectral_eq_zero_iff_exists_zetaZero _).mpr ⟨_, rfl⟩
  · apply sub_ne_zero.mpr
    intro he
    apply hne t ht
    left
    rw [he]
    exact (riemannXiSpectral_eq_zero_iff_exists_zetaZero _).mpr ⟨sigma, rfl⟩

/-- Every fixed nonsingular path in the full eta domain retains the original
ordered mixed node factors in its arithmetic integral limit. -/
theorem tendsto_intervalIntegral_suzukiXiEtaFiniteMixedChannel (rho sigma : NontrivialZetaZero) {a b : ℝ} (gamma : ℝ → ℂ)
    (hc : ContinuousOn gamma (uIcc a b))
    (hgeom : ∀ t ∈ uIcc a b, gamma t ∈ suzukiXiEtaExtendedCarrierDomain)
    (hne : ∀ t ∈ uIcc a b, gamma t ∉ suzukiXiCarrierSingularSet) :
    Tendsto (fun N => ∫ t : ℝ in a..b, suzukiXiEtaFiniteMixedChannel rho sigma N (gamma t)) atTop
      (𝓝 (∫ t : ℝ in a..b, suzukiXiMixedCarrierChannel rho sigma (gamma t))) := by
  have h := tendsto_intervalIntegral_suzukiXiEtaFiniteCarrier_on_completionDomain gamma
    (fun t => 1 / ((gamma t - starRingEnd ℂ (zetaSpectralCoordinate rho.1)) *
      (gamma t - zetaSpectralCoordinate sigma.1))) hc (node_weight_continuous rho sigma hc hne) hgeom
  simpa only [suzukiXiEtaFiniteMixedChannel, suzukiXiMixedCarrierChannel,
    div_eq_mul_inv, one_mul, mul_comm] using h


/-- Every finite vertical segment above height minus one half on an
admissible line has the genuine mixed arithmetic limit, including its
crossing of spectral height one half. -/
theorem tendsto_suzukiXiEtaFiniteMixed_vertical
    (rho sigma : NontrivialZetaZero) {v a b : ℝ}
    (hv : SuzukiXiEtaVerticalAdmissible v) (ha : -1 / 2 < a) (hb : -1 / 2 < b) :
    Tendsto (fun N => ∫ y : ℝ in a..b,
      suzukiXiEtaFiniteMixedChannel rho sigma N ((v : ℂ) + (y : ℂ) * I)) atTop
      (𝓝 (∫ y : ℝ in a..b, suzukiXiMixedCarrierChannel rho sigma ((v : ℂ) + (y : ℂ) * I))) := by
  apply tendsto_intervalIntegral_suzukiXiEtaFiniteMixedChannel rho sigma _ (by fun_prop)
  · intro y hy
    apply mem_suzukiXiEtaExtendedCarrierDomain_vertical hv
    exact (lt_min ha hb).trans_le hy.1
  · intro y _hy hc
    exact hv.1 _ hc (by simp)

/-- Finite eta contours converge on full admissible upper rectangles,
including sides that cross the upper spectral strip boundary. Only the
horizontal heights avoid one half; the vertical crossings are included. -/
theorem tendsto_suzukiXiEtaFiniteMixedContour_on_completionDomain
    (rho sigma : NontrivialZetaZero) {l r b u : ℝ}
    (hadm : SuzukiXiCarrierRectangleAdmissible l r b u)
    (hlv : SuzukiXiEtaVerticalAdmissible l) (hrv : SuzukiXiEtaVerticalAdmissible r)
    (hb : -1 / 2 < b) (hbhalf : b ≠ 1 / 2) (huhalf : u ≠ 1 / 2) :
    Tendsto (fun N => rectangularBoundaryIntegral l r b u (suzukiXiEtaFiniteMixedChannel rho sigma N))
      atTop (𝓝 (rectangularBoundaryIntegral l r b u (suzukiXiMixedCarrierChannel rho sigma))) := by
  have hhorizontal (v : ℝ) (hv0 : -1 / 2 < v) (hvhalf : v ≠ 1 / 2)
      (hv : ∀ c ∈ suzukiXiCarrierSingularSet, c.im ≠ v) :=
    tendsto_intervalIntegral_suzukiXiEtaFiniteMixedChannel rho sigma (a := l) (b := r)
      (fun x => (x : ℂ) + (v : ℂ) * I) (by fun_prop)
      (fun x _ => mem_suzukiXiEtaExtendedCarrierDomain_of_im_ne_half
        (by simpa using hv0) (by simpa using hvhalf)
        (fun he => hv _ (Or.inr he) (by simp)))
      (fun x _ hc => hv _ hc (by simp))
  have hbot := hhorizontal b hb hbhalf (fun c hc => (hadm.2.2 c hc).2.2.1)
  have htop := hhorizontal u (hb.trans hadm.2.1) huhalf (fun c hc => (hadm.2.2 c hc).2.2.2)
  have hr := tendsto_suzukiXiEtaFiniteMixed_vertical rho sigma hrv hb (hb.trans hadm.2.1)
  have hl := tendsto_suzukiXiEtaFiniteMixed_vertical rho sigma hlv hb (hb.trans hadm.2.1)
  exact ((hbot.sub htop).add (hr.const_mul I)).sub (hl.const_mul I)

/-- The full complex arithmetic pole matrix subtracts the exact xi
source after dividing by the original oriented residue factor. -/
def suzukiXiEtaFinitePoleMatrix (rho sigma : NontrivialZetaZero)
    (l r b u : ℝ) (N : ℕ) : ℂ :=
  rectangularBoundaryIntegral l r b u (suzukiXiEtaFiniteMixedChannel rho sigma N) /
    ((2 * Real.pi : ℝ) * I) - suzukiXiMixedContourXiSource rho sigma l r b u

/-- The full complex finite eta pole matrix converges to every genuine
pole residue in the upper rectangle, including arbitrary analytic orders. -/
theorem tendsto_suzukiXiEtaFinitePoleMatrix
    (rho sigma : NontrivialZetaZero) {l r b u : ℝ}
    (hadm : SuzukiXiCarrierRectangleAdmissible l r b u)
    (hlv : SuzukiXiEtaVerticalAdmissible l) (hrv : SuzukiXiEtaVerticalAdmissible r)
    (hb : -1 / 2 < b) (hbhalf : b ≠ 1 / 2) (huhalf : u ≠ 1 / 2) :
    Tendsto (suzukiXiEtaFinitePoleMatrix rho sigma l r b u) atTop
      (𝓝 (∑ c ∈ suzukiXiCarrierGenuinePoleWindow l r b u, suzukiXiMixedCarrierPoleResidue rho sigma c)) := by
  have h := tendsto_suzukiXiEtaFiniteMixedContour_on_completionDomain rho sigma hadm hlv hrv hb hbhalf huhalf
  rw [suzukiXiMixedCarrierChannel_rectangle_eq_source_add_poles rho sigma hadm] at h
  have hdiv := (h.div_const ((2 * Real.pi : ℝ) * I)).sub_const (suzukiXiMixedContourXiSource rho sigma l r b u)
  convert hdiv using 1
  congr 1
  field_simp
  congr 1
  ring

/-- The finite arithmetic versions of both original strip segments,
with the right side upward and the left side downward. -/
def suzukiXiEtaFiniteStripSides (rho sigma : NontrivialZetaZero) (l r : ℝ) (N : ℕ) : ℂ :=
  I * (∫ y : ℝ in 0..(1 / 2), suzukiXiEtaFiniteMixedChannel rho sigma N ((r : ℂ) + (y : ℂ) * I)) -
    I * (∫ y : ℝ in 0..(1 / 2), suzukiXiEtaFiniteMixedChannel rho sigma N ((l : ℂ) + (y : ℂ) * I))

/-- Both complete closed strip segments have their signed arithmetic
limit under one common eta truncation. Neither endpoint is discarded. -/
theorem tendsto_suzukiXiEtaFiniteStripSides (rho sigma : NontrivialZetaZero) {l r : ℝ}
    (hlv : SuzukiXiEtaVerticalAdmissible l) (hrv : SuzukiXiEtaVerticalAdmissible r) :
    Tendsto (suzukiXiEtaFiniteStripSides rho sigma l r) atTop
      (𝓝 (suzukiXiMixedCarrierStripSides rho sigma l r)) := by
  exact ((tendsto_suzukiXiEtaFiniteMixed_vertical rho sigma hrv (by norm_num) (by norm_num)).const_mul I).sub
    ((tendsto_suzukiXiEtaFiniteMixed_vertical rho sigma hlv (by norm_num) (by norm_num)).const_mul I)

/-- The arithmetic strip matrix retains the original conjugate transpose,
so all mixed complex weights can be kept until the final projection. -/
def suzukiXiEtaFiniteStripSidesGram (rho sigma : NontrivialZetaZero) (l r : ℝ) (N : ℕ) : ℂ :=
  (suzukiXiEtaFiniteStripSides rho sigma l r N -
    starRingEnd ℂ (suzukiXiEtaFiniteStripSides sigma rho l r N)) / (2 * I)

/-- The finite arithmetic strip matrix converges entrywise to the exact
matrix in the real Gram comparison, including its conjugate transpose. -/
theorem tendsto_suzukiXiEtaFiniteStripSidesGram (rho sigma : NontrivialZetaZero) {l r : ℝ}
    (hlv : SuzukiXiEtaVerticalAdmissible l) (hrv : SuzukiXiEtaVerticalAdmissible r) :
    Tendsto (suzukiXiEtaFiniteStripSidesGram rho sigma l r) atTop
      (𝓝 (suzukiXiCarrierStripSidesGram rho sigma l r)) := by
  have hconj := (continuous_star : Continuous (star : ℂ → ℂ)).continuousAt.tendsto.comp
    (tendsto_suzukiXiEtaFiniteStripSides sigma rho hlv hrv)
  exact ((tendsto_suzukiXiEtaFiniteStripSides rho sigma hlv hrv).sub hconj).div_const (2 * I)

/-- The original pole and strip corrections are coupled at each finite
arithmetic truncation, before weights or real parts are taken. -/
def suzukiXiEtaFiniteJointCorrection (rho sigma : NontrivialZetaZero)
    (l r b u : ℝ) (N : ℕ) : ℂ :=
  (2 * Real.pi : ℝ) * suzukiXiEtaFinitePoleMatrix rho sigma l r b u N -
    suzukiXiEtaFiniteStripSidesGram rho sigma l r N

/-- One eta truncation approximates the complete joint correction for
every fixed finite complex weight family, with all mixed phases retained. -/
theorem tendsto_suzukiXiEtaFiniteJointCorrection_weighted
    (S : Finset NontrivialZetaZero) (w : NontrivialZetaZero → ℂ) {l r b u : ℝ}
    (hadm : SuzukiXiCarrierRectangleAdmissible l r b u)
    (hlv : SuzukiXiEtaVerticalAdmissible l) (hrv : SuzukiXiEtaVerticalAdmissible r)
    (hb : -1 / 2 < b) (hbhalf : b ≠ 1 / 2) (huhalf : u ≠ 1 / 2) :
    Tendsto (fun N => ∑ rho ∈ S, ∑ sigma ∈ S, starRingEnd ℂ (w rho) * w sigma *
      suzukiXiEtaFiniteJointCorrection rho sigma l r b u N) atTop
      (𝓝 (∑ rho ∈ S, ∑ sigma ∈ S, starRingEnd ℂ (w rho) * w sigma *
        ((2 * Real.pi : ℝ) *
          ∑ c ∈ suzukiXiCarrierGenuinePoleWindow l r b u, suzukiXiMixedCarrierPoleResidue rho sigma c -
            suzukiXiCarrierStripSidesGram rho sigma l r))) := by
  apply tendsto_finsetSum S
  intro rho _hrho
  apply tendsto_finsetSum S
  intro sigma _hsigma
  exact (((tendsto_suzukiXiEtaFinitePoleMatrix rho sigma hadm hlv hrv hb hbhalf huhalf).const_mul
    ((2 * Real.pi : ℝ) : ℂ)).sub (tendsto_suzukiXiEtaFiniteStripSidesGram rho sigma hlv hrv)).const_mul _

end
end RiemannGaussian
