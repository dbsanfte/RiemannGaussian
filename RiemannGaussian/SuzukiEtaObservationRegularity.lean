/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiEtaContourGeometry

/-!
# Simultaneous regularity of the finite arithmetic observation paths

One sufficiently long eta truncation has nonzero denominators on both
horizontal sides and on both vertical segments extended down to zero.
For the actual expanding geometry these four paths include the entire
lifted contour and both original closed strip segments. This property
can be retained when selecting a diagonal approximation, before any
mixed node or weight is chosen.
-/

open Complex Filter MeasureTheory Set Topology
namespace RiemannGaussian
noncomputable section

/-- Simultaneous finite-denominator nonvanishing on the two horizontal
sides and the vertical sides extended to the real axis. -/
def SuzukiXiEtaFiniteObservationRegular (N : ℕ) (l r b u : ℝ) : Prop :=
  (∀ x ∈ uIcc l r,
    suzukiEtaFiniteCarrierDenominator N (suzukiArithmeticZetaArgument ((x : ℂ) + (b : ℂ) * I)) ≠ 0 ∧
    suzukiEtaFiniteCarrierDenominator N (suzukiArithmeticZetaArgument ((x : ℂ) + (u : ℂ) * I)) ≠ 0) ∧
  ∀ y ∈ uIcc 0 u,
    suzukiEtaFiniteCarrierDenominator N (suzukiArithmeticZetaArgument ((l : ℂ) + (y : ℂ) * I)) ≠ 0 ∧
    suzukiEtaFiniteCarrierDenominator N (suzukiArithmeticZetaArgument ((r : ℂ) + (y : ℂ) * I)) ≠ 0

private lemma eventually_path_regular {a b : ℝ} (gamma : ℝ → ℂ)
    (hc : ContinuousOn gamma (uIcc a b))
    (hD : ∀ t ∈ uIcc a b, gamma t ∈ suzukiXiEtaExtendedCarrierDomain) :
    ∀ᶠ N in atTop, ∀ t ∈ uIcc a b,
      suzukiEtaFiniteCarrierDenominator N (suzukiArithmeticZetaArgument (gamma t)) ≠ 0 := by
  have hK : IsCompact (gamma '' uIcc a b) := isCompact_uIcc.image_of_continuousOn hc
  have hKD : gamma '' uIcc a b ⊆ suzukiXiEtaExtendedCarrierDomain := by
    rintro _ ⟨t, ht, rfl⟩
    exact hD t ht
  filter_upwards [eventually_suzukiXiEtaFiniteDenominator_ne_zero_on_compact_on_completionDomain hK hKD]
    with N hN
  exact fun t ht => hN _ (mem_image_of_mem gamma ht)

/-- The actual finite denominator is eventually nonzero on all
observation paths simultaneously. Interior pole orders are unrestricted. -/
theorem eventually_suzukiXiEtaFiniteObservationRegular {l r b u : ℝ}
    (hadm : SuzukiXiCarrierRectangleAdmissible l r b u)
    (hlv : SuzukiXiEtaVerticalAdmissible l) (hrv : SuzukiXiEtaVerticalAdmissible r)
    (hb : 0 < b) (hbhalf : b ≠ 1 / 2) (huhalf : u ≠ 1 / 2) :
    ∀ᶠ N in atTop, SuzukiXiEtaFiniteObservationRegular N l r b u := by
  have hhorizontal (v : ℝ) (hv0 : 0 < v) (hvhalf : v ≠ 1 / 2)
      (hv : ∀ c ∈ suzukiXiCarrierSingularSet, c.im ≠ v) :=
    eventually_path_regular (a := l) (b := r) (fun x => (x : ℂ) + (v : ℂ) * I)
      (by fun_prop) (fun x _ => mem_suzukiXiEtaExtendedCarrierDomain_of_im_ne_half
        (by simp only [add_im, ofReal_im, mul_I_im, ofReal_re, zero_add]; linarith)
        (by simpa using hvhalf) (fun he => hv _ (Or.inr he) (by simp)))
  have hu : 0 < u := hb.trans hadm.2.1
  have hvertical (v : ℝ) (hv : SuzukiXiEtaVerticalAdmissible v) :=
    eventually_path_regular (a := 0) (b := u) (fun y => (v : ℂ) + (y : ℂ) * I)
      (by fun_prop) (fun y hy => mem_suzukiXiEtaExtendedCarrierDomain_vertical hv (by
        rw [uIcc_of_le hu.le] at hy
        linarith [hy.1]))
  filter_upwards [hhorizontal b hb hbhalf (fun c hc => (hadm.2.2 c hc).2.2.1),
    hhorizontal u hu huhalf (fun c hc => (hadm.2.2 c hc).2.2.2),
    hvertical l hlv, hvertical r hrv] with N hbot htop hleft hright
  exact ⟨fun x hx => ⟨hbot x hx, htop x hx⟩, fun y hy => ⟨hleft y hy, hright y hy⟩⟩

/-- A selected regular observation has true nonzero finite denominators
throughout both original strip segments, including their endpoints. -/
theorem SuzukiXiEtaFiniteObservationRegular.strip {N : ℕ} {l r b u y : ℝ}
    (hreg : SuzukiXiEtaFiniteObservationRegular N l r b u)
    (hu : 1 / 2 ≤ u) (hy : y ∈ Icc 0 (1 / 2)) :
    suzukiEtaFiniteCarrierDenominator N (suzukiArithmeticZetaArgument ((l : ℂ) + (y : ℂ) * I)) ≠ 0 ∧
    suzukiEtaFiniteCarrierDenominator N (suzukiArithmeticZetaArgument ((r : ℂ) + (y : ℂ) * I)) ≠ 0 := by
  apply hreg.2 y
  rw [uIcc_of_le (by linarith : 0 ≤ u)]
  exact ⟨hy.1, hy.2.trans hu⟩

/-- Every selected finite truncation with nonzero path denominators
has genuine weighted path integrals. The weight may be any continuous
complex function; nonvanishing is not merely eventual in this statement. -/
theorem intervalIntegrable_suzukiXiEtaFiniteCarrier_of_regular_path
    (N : ℕ) {a b : ℝ} (gamma : ℝ → ℂ) (w : ℝ → ℂ)
    (hgamma : ContinuousOn gamma (uIcc a b)) (hw : ContinuousOn w (uIcc a b))
    (hgeom : ∀ t ∈ uIcc a b, gamma t ∈ suzukiXiEtaExtendedCarrierDomain)
    (hN : ∀ t ∈ uIcc a b,
      suzukiEtaFiniteCarrierDenominator N (suzukiArithmeticZetaArgument (gamma t)) ≠ 0) :
    IntervalIntegrable (fun t => w t * suzukiXiEtaFiniteCarrier N (gamma t)) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply hw.mul
  intro t ht
  have hnum : AnalyticAt ℂ (fun s => I * pairedEtaCorePartialSum N s)
      (suzukiArithmeticZetaArgument (gamma t)) := analyticAt_const.mul
    ((differentiable_pairedEtaCorePartialSum N).analyticAt _)
  have hden := analyticAt_suzukiEtaFiniteCarrierDenominator_on_completionDomain N (hgeom t ht).1
  have harg : Continuous suzukiArithmeticZetaArgument := by
    unfold suzukiArithmeticZetaArgument
    fun_prop
  exact ((hnum.div hden (hN t ht)).continuousAt.comp harg.continuousAt).comp_continuousWithinAt
    (hgamma t ht)

end
end RiemannGaussian
