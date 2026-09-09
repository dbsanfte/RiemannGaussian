/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiEtaCarrierLimit

/-!
# Complete pole groups from finite arithmetic contour integrals

On admissible rectangles inside the open spectral strip, finite paired
eta carrier contours converge to the exact xi source and full carrier
residue sum. All analytic pole orders are retained. The only exclusions
are on the four contour sides, where denominator nonvanishing and genuine
integrability of sufficiently long finite approximants are supplied by
the compact convergence theorem.

The full complex weighted matrix is retained before taking its signed
projection. These are arithmetic approximation theorems for complete
pole groups, not an independent bound at the RH source threshold.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Topology
namespace RiemannGaussian
noncomputable section

/-- The original ordered mixed channel with its carrier replaced by the
finite arithmetic eta quotient. The node denominators are unchanged. -/
def suzukiXiEtaFiniteMixedChannel (rho sigma : NontrivialZetaZero) (N : ℕ) (z : ℂ) : ℂ :=
  suzukiXiEtaFiniteCarrier N z /
    ((z - starRingEnd ℂ (zetaSpectralCoordinate rho.1)) * (z - zetaSpectralCoordinate sigma.1))

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

private lemma path_limit (rho sigma : NontrivialZetaZero) {a b : ℝ} (gamma : ℝ → ℂ)
    (hc : ContinuousOn gamma (uIcc a b))
    (hstrip : ∀ t ∈ uIcc a b, -1 / 2 < (gamma t).im ∧ (gamma t).im < 1 / 2)
    (hne : ∀ t ∈ uIcc a b, gamma t ∉ suzukiXiCarrierSingularSet) :
    Tendsto (fun N => ∫ t : ℝ in a..b, suzukiXiEtaFiniteMixedChannel rho sigma N (gamma t)) atTop
      (𝓝 (∫ t : ℝ in a..b, suzukiXiMixedCarrierChannel rho sigma (gamma t))) := by
  have hg : ∀ t ∈ uIcc a b, gamma t ∈ suzukiXiEtaCarrierDomain := by
    intro t ht
    rw [mem_suzukiXiEtaCarrierDomain]
    exact ⟨(hstrip t ht).1, (hstrip t ht).2, fun he => hne t ht (Or.inr he)⟩
  have h := tendsto_intervalIntegral_suzukiXiEtaFiniteCarrier gamma
    (fun t => 1 / ((gamma t - starRingEnd ℂ (zetaSpectralCoordinate rho.1)) *
      (gamma t - zetaSpectralCoordinate sigma.1))) hc (node_weight_continuous rho sigma hc hne) hg
  simpa only [suzukiXiEtaFiniteMixedChannel, suzukiXiMixedCarrierChannel,
    div_eq_mul_inv, one_mul, mul_comm] using h

/-- The finite arithmetic mixed contours converge to the actual mixed
contour on every admissible rectangle inside the open spectral strip.
No restriction is imposed on pole orders or xi zeros in the interior. -/
theorem tendsto_suzukiXiEtaFiniteMixedContour
    (rho sigma : NontrivialZetaZero) {l r b u : ℝ}
    (hadm : SuzukiXiCarrierRectangleAdmissible l r b u)
    (hb : -1 / 2 < b) (hu : u < 1 / 2) :
    Tendsto (fun N => rectangularBoundaryIntegral l r b u (suzukiXiEtaFiniteMixedChannel rho sigma N))
      atTop (𝓝 (rectangularBoundaryIntegral l r b u (suzukiXiMixedCarrierChannel rho sigma))) := by
  have hhorizontal (v : ℝ) (hv0 : -1 / 2 < v) (hv1 : v < 1 / 2)
      (hv : ∀ c ∈ suzukiXiCarrierSingularSet, c.im ≠ v) :=
    path_limit rho sigma (a := l) (b := r) (fun x => (x : ℂ) + (v : ℂ) * I)
      (by fun_prop)
      (fun _ _ => by simpa using And.intro hv0 hv1)
      (fun x _ hc => hv _ hc (by simp))
  have hvertical (v : ℝ) (hv : ∀ c ∈ suzukiXiCarrierSingularSet, c.re ≠ v) :=
    path_limit rho sigma (a := b) (b := u) (fun y => (v : ℂ) + (y : ℂ) * I)
      (by fun_prop)
      (fun y hy => by
        have hy' : b ≤ y ∧ y ≤ u := by simpa only [uIcc_of_le hadm.2.1.le, mem_Icc] using hy
        simpa only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_one,
          zero_mul, add_zero, zero_add] using
          And.intro (hb.trans_le hy'.1) (hy'.2.trans_lt hu))
      (fun y _ hc => hv _ hc (by simp))
  have hbot := hhorizontal b hb (hadm.2.1.trans hu) (fun c hc => (hadm.2.2 c hc).2.2.1)
  have htop := hhorizontal u (hb.trans hadm.2.1) hu (fun c hc => (hadm.2.2 c hc).2.2.2)
  have hr := hvertical r (fun c hc => (hadm.2.2 c hc).2.1)
  have hl := hvertical l (fun c hc => (hadm.2.2 c hc).1)
  exact ((hbot.sub htop).add (hr.const_mul I)).sub (hl.const_mul I)

/-- Finite arithmetic contours recover the complete actual xi source
and carrier-pole correction, including every higher-order residue. -/
theorem tendsto_suzukiXiEtaFiniteMixedContour_source_add_poles
    (rho sigma : NontrivialZetaZero) {l r b u : ℝ}
    (hadm : SuzukiXiCarrierRectangleAdmissible l r b u)
    (hb : -1 / 2 < b) (hu : u < 1 / 2) :
    Tendsto (fun N => rectangularBoundaryIntegral l r b u (suzukiXiEtaFiniteMixedChannel rho sigma N))
      atTop (𝓝 ((2 * Real.pi : ℝ) * I *
        (suzukiXiMixedContourXiSource rho sigma l r b u +
          ∑ c ∈ suzukiXiCarrierGenuinePoleWindow l r b u, suzukiXiMixedCarrierPoleResidue rho sigma c))) := by
  rw [← suzukiXiMixedCarrierChannel_rectangle_eq_source_add_poles rho sigma hadm]
  exact tendsto_suzukiXiEtaFiniteMixedContour rho sigma hadm hb hu

/-- The arithmetic contour limit retains the full weighted mixed matrix
for any finite complex weight family, with all pole orders and phases. -/
theorem tendsto_suzukiXiEtaFiniteWeightedContour_source_add_poles
    (S : Finset NontrivialZetaZero) (w : NontrivialZetaZero → ℂ) {l r b u : ℝ}
    (hadm : SuzukiXiCarrierRectangleAdmissible l r b u)
    (hb : -1 / 2 < b) (hu : u < 1 / 2) :
    Tendsto (fun N => ∑ rho ∈ S, ∑ sigma ∈ S, starRingEnd ℂ (w rho) * w sigma *
      rectangularBoundaryIntegral l r b u (suzukiXiEtaFiniteMixedChannel rho sigma N))
      atTop (𝓝 ((2 * Real.pi : ℝ) * I *
        ∑ rho ∈ S, ∑ sigma ∈ S, starRingEnd ℂ (w rho) * w sigma *
          (suzukiXiMixedContourXiSource rho sigma l r b u +
            ∑ c ∈ suzukiXiCarrierGenuinePoleWindow l r b u, suzukiXiMixedCarrierPoleResidue rho sigma c))) := by
  have h := tendsto_finsetSum S (fun rho _ => tendsto_finsetSum S (fun sigma _ =>
    (tendsto_suzukiXiEtaFiniteMixedContour_source_add_poles rho sigma hadm hb hu).const_mul
      (starRingEnd ℂ (w rho) * w sigma)))
  convert h using 1
  congr 1
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rho _hrho
  apply Finset.sum_congr rfl
  intro sigma _hsigma
  ring

/-- A finite arithmetic approximation of the signed full carrier-pole
form. The exact xi-node source is subtracted with its original sign and
multiplicity, so it is not hidden in the error term. -/
def suzukiXiEtaFinitePoleForm (S : Finset NontrivialZetaZero)
    (w : NontrivialZetaZero → ℂ) (l r b u : ℝ) (N : ℕ) : ℝ :=
  (∑ rho ∈ S, ∑ sigma ∈ S, starRingEnd ℂ (w rho) * w sigma *
    rectangularBoundaryIntegral l r b u (suzukiXiEtaFiniteMixedChannel rho sigma N)).im /
      (2 * Real.pi) -
    (∑ rho ∈ S, ∑ sigma ∈ S, starRingEnd ℂ (w rho) * w sigma *
      suzukiXiMixedContourXiSource rho sigma l r b u).re

/-- The literal finite eta expression converges to the signed form of
the complete actual pole group. No simple-pole replacement, deletion of
xi sources, or loss of mixed weights occurs in the limit. -/
theorem tendsto_suzukiXiEtaFinitePoleForm
    (S : Finset NontrivialZetaZero) (w : NontrivialZetaZero → ℂ) {l r b u : ℝ}
    (hadm : SuzukiXiCarrierRectangleAdmissible l r b u)
    (hb : -1 / 2 < b) (hu : u < 1 / 2) :
    Tendsto (suzukiXiEtaFinitePoleForm S w l r b u) atTop
      (𝓝 (∑ rho ∈ S, ∑ sigma ∈ S, starRingEnd ℂ (w rho) * w sigma *
        ∑ c ∈ suzukiXiCarrierGenuinePoleWindow l r b u, suzukiXiMixedCarrierPoleResidue rho sigma c).re) := by
  let Z : ℂ := ∑ rho ∈ S, ∑ sigma ∈ S, starRingEnd ℂ (w rho) * w sigma *
    suzukiXiMixedContourXiSource rho sigma l r b u
  let K : ℂ := ∑ rho ∈ S, ∑ sigma ∈ S, starRingEnd ℂ (w rho) * w sigma *
    ∑ c ∈ suzukiXiCarrierGenuinePoleWindow l r b u, suzukiXiMixedCarrierPoleResidue rho sigma c
  have hsum : (∑ rho ∈ S, ∑ sigma ∈ S, starRingEnd ℂ (w rho) * w sigma *
      (suzukiXiMixedContourXiSource rho sigma l r b u +
        ∑ c ∈ suzukiXiCarrierGenuinePoleWindow l r b u, suzukiXiMixedCarrierPoleResidue rho sigma c)) =
          Z + K := by
    simp only [mul_add, Finset.sum_add_distrib, Z, K]
  have h := tendsto_suzukiXiEtaFiniteWeightedContour_source_add_poles S w hadm hb hu
  rw [hsum] at h
  have him := Complex.continuous_im.continuousAt.tendsto.comp h
  have hres := (him.div_const (2 * Real.pi)).sub_const Z.re
  have he : (((2 * Real.pi : ℝ) : ℂ) * I * (Z + K)).im / (2 * Real.pi) - Z.re = K.re := by
    simp only [mul_im, mul_re, ofReal_re, ofReal_im, I_re, I_im, zero_mul, mul_zero,
      mul_one, sub_zero, add_zero, zero_add, add_im, add_re]
    field_simp
    ring
  rw [he] at hres
  exact hres

/-- An actual signed upper bound for the whole finite pole group using
only its finite arithmetic contour approximation and any prescribed
positive error. Comparing that arithmetic expression with the RH source
ceiling remains a separate, unproved obligation. -/
theorem eventually_suzukiXiPoleForm_le_etaFinite_add
    (S : Finset NontrivialZetaZero) (w : NontrivialZetaZero → ℂ) {l r b u : ℝ}
    (hadm : SuzukiXiCarrierRectangleAdmissible l r b u)
    (hb : -1 / 2 < b) (hu : u < 1 / 2) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop,
      (∑ rho ∈ S, ∑ sigma ∈ S, starRingEnd ℂ (w rho) * w sigma *
        ∑ c ∈ suzukiXiCarrierGenuinePoleWindow l r b u, suzukiXiMixedCarrierPoleResidue rho sigma c).re ≤
          suzukiXiEtaFinitePoleForm S w l r b u N + epsilon := by
  have h := (Metric.tendsto_nhds.mp (tendsto_suzukiXiEtaFinitePoleForm S w hadm hb hu)) epsilon hepsilon
  filter_upwards [h] with N hN
  rw [Real.dist_eq] at hN
  have hlo := (abs_lt.mp hN).1
  linarith

end
end RiemannGaussian
