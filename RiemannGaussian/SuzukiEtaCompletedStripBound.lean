/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiEtaReflectionRemainder
import RiemannGaussian.SuzukiEtaObservationRegularity
import RiemannGaussian.SuzukiEtaStripSides

/-!
# A quartic lower bound for the integrated signed eta strip remainder

Both original strip segments use the same finite eta truncation and
their original orientations. Genuine continuity and integrability hold
for each selected regular truncation. The signed completed eta remainder
then has the independent lower bound `-512*Im(alpha)^2/(log(2)*R^4)`.
No carrier denominator separation constant enters this bound.
-/

open Complex Filter MeasureTheory Set Topology
namespace RiemannGaussian
noncomputable section

private lemma continuous_reflection_weight (rho : NontrivialZetaZero) {v : ℝ}
    (hv : SuzukiXiEtaVerticalAdmissible v) :
    Continuous (fun y : ℝ => suzukiXiReflectionWeight rho ((v : ℂ) + (y : ℂ) * I)) := by
  have hnode (a : NontrivialZetaZero) (y : ℝ) :
      (v : ℂ) + (y : ℂ) * I ≠ zetaSpectralCoordinate a.1 := by
    intro he
    apply hv.1 _ (Or.inl ((riemannXiSpectral_eq_zero_iff_exists_zetaZero _).mpr ⟨a, rfl⟩))
    rw [← he]
    simp
  have hc (a : NontrivialZetaZero) :
      Continuous (fun y : ℝ => (((v : ℂ) + (y : ℂ) * I) - zetaSpectralCoordinate a.1)⁻¹) :=
    (show Continuous (fun y : ℝ => ((v : ℂ) + (y : ℂ) * I) - zetaSpectralCoordinate a.1) by fun_prop).inv₀
      (fun y => sub_ne_zero.mpr (hnode a y))
  convert (((hc rho).sub (hc rho.conjugatePartner)).pow 2).neg using 1
  funext y
  simp only [suzukiXiReflectionWeight, suzukiXiReflectionCauchyDifference,
    NontrivialZetaZero.spectralCoordinate_conjugatePartner, Pi.neg_apply, Pi.pow_apply, Pi.sub_apply]

private lemma continuous_completed_quotient (N : ℕ) {a b : ℝ}
    (gamma : ℝ → ℂ) (B : ℝ → ℂ)
    (hg : ContinuousOn gamma (uIcc a b)) (hB : ContinuousOn B (uIcc a b))
    (hgeom : ∀ t ∈ uIcc a b, gamma t ∈ suzukiXiEtaExtendedCarrierDomain)
    (hN : ∀ t ∈ uIcc a b,
      suzukiEtaFiniteCarrierDenominator N (suzukiArithmeticZetaArgument (gamma t)) ≠ 0) :
    ContinuousOn (fun t =>
      (B t * suzukiEtaFiniteCompletedNumerator N (suzukiArithmeticZetaArgument (gamma t))).re /
        normSq (suzukiEtaFiniteCarrierDenominator N (suzukiArithmeticZetaArgument (gamma t)))) (uIcc a b) := by
  have harg : Continuous suzukiArithmeticZetaArgument := by
    unfold suzukiArithmeticZetaArgument
    fun_prop
  have hC : ContinuousOn (fun t => suzukiXiEtaFiniteCarrier N (gamma t)) (uIcc a b) := by
    intro t ht
    have hnum : AnalyticAt ℂ (fun s => I * pairedEtaCorePartialSum N s)
        (suzukiArithmeticZetaArgument (gamma t)) := analyticAt_const.mul
      ((differentiable_pairedEtaCorePartialSum N).analyticAt _)
    have hden := analyticAt_suzukiEtaFiniteCarrierDenominator_on_completionDomain N (hgeom t ht).1
    exact ((hnum.div hden (hN t ht)).continuousAt.comp harg.continuousAt).comp_continuousWithinAt (hg t ht)
  have hL : ContinuousOn (fun t => pairedEtaFactorLogDerivative (suzukiArithmeticZetaArgument (gamma t)))
      (uIcc a b) := by
    intro t ht
    have hF : AnalyticAt ℂ pairedEtaFactor (suzukiArithmeticZetaArgument (gamma t)) :=
      (show Differentiable ℂ pairedEtaFactor from fun s => (hasDerivAt_pairedEtaFactor s).differentiableAt).analyticAt _
    have heq : pairedEtaFactorLogDerivative = fun s => deriv pairedEtaFactor s / pairedEtaFactor s := by
      funext s
      rw [← logDeriv_pairedEtaFactor, logDeriv_apply]
    have hLc : ContinuousAt pairedEtaFactorLogDerivative (suzukiArithmeticZetaArgument (gamma t)) := by
      rw [heq]
      exact (hF.deriv.div hF (hgeom t ht).1.2.2).continuousAt
    exact (hLc.comp harg.continuousAt).comp_continuousWithinAt (hg t ht)
  have hcoef : ContinuousOn (fun t => suzukiEtaDyadicWeightCoefficient (B t)
      (suzukiArithmeticZetaArgument (gamma t))) (uIcc a b) :=
    (Complex.continuous_re.comp_continuousOn (hB.mul hL.star)).neg
  have hcont := (Complex.continuous_im.comp_continuousOn (hB.mul hC)).sub
    (hcoef.mul (Complex.continuous_normSq.comp_continuousOn hC))
  apply hcont.congr
  intro t _ht
  have h := im_mul_suzukiEtaFiniteCarrier_eq_completed_add_energy (B t) N
    (suzukiArithmeticZetaArgument (gamma t))
  dsimp only [suzukiXiEtaFiniteCarrier, Pi.sub_apply, Pi.mul_apply, Function.comp_apply] at *
  linarith

/-- Every regular actual vertical observation gives a genuine
integrable signed completed eta density with its full reflection weight. -/
theorem intervalIntegrable_suzukiXiEtaFiniteReflectionCompletedSide
    (rho : NontrivialZetaZero) (N : ℕ) {v : ℝ} (hv : SuzukiXiEtaVerticalAdmissible v)
    (hN : ∀ y ∈ Icc (0 : ℝ) (1 / 2), suzukiEtaFiniteCarrierDenominator N
      (suzukiArithmeticZetaArgument ((v : ℂ) + (y : ℂ) * I)) ≠ 0) :
    IntervalIntegrable (suzukiXiEtaFiniteReflectionCompletedSide rho v N) volume 0 (1 / 2) := by
  apply ContinuousOn.intervalIntegrable
  apply continuous_completed_quotient N (fun y => (v : ℂ) + (y : ℂ) * I)
    (fun y => I * suzukiXiReflectionWeight rho ((v : ℂ) + (y : ℂ) * I)) (by fun_prop)
    (continuous_const.mul (continuous_reflection_weight rho hv)).continuousOn
  · intro y hy
    apply mem_suzukiXiEtaExtendedCarrierDomain_vertical hv
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hy
    linarith [hy.1]
  · intro y hy
    exact hN y (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] using hy)

/-- The two signed completed eta integrals with the original right-up,
left-down orientations and one common arithmetic truncation. -/
def suzukiXiEtaFiniteReflectionCompletedStrip (rho : NontrivialZetaZero) (l r : ℝ) (N : ℕ) : ℝ :=
  ∫ y : ℝ in 0..(1 / 2), suzukiXiEtaFiniteReflectionCompletedSide rho r N y -
    suzukiXiEtaFiniteReflectionCompletedSide rho l N y

/-- The full signed eta/derivative remainder on the two strip sides
has an independent quartic lower allowance for every regular truncation. -/
theorem suzukiXiEtaFiniteReflectionCompletedStrip_lower
    (rho : NontrivialZetaZero) (N : ℕ) {R l r b u : ℝ} (hR : 200 ≤ R)
    (hl : R ≤ |l|) (hr : R ≤ |r|) (ha : 2 * |(zetaSpectralCoordinate rho.1).re| ≤ R)
    (hlv : SuzukiXiEtaVerticalAdmissible l) (hrv : SuzukiXiEtaVerticalAdmissible r)
    (hu : 1 / 2 ≤ u) (hreg : SuzukiXiEtaFiniteObservationRegular N l r b u)
    (hlcos : Real.cos (l * Real.log 2) ≤ 0) (hrcos : Real.cos (r * Real.log 2) ≤ 0)
    (hlsin : Real.sin (l * Real.log 2) ≤ -1 / 2) (hrsin : 1 / 2 ≤ Real.sin (r * Real.log 2)) :
    -(512 * (zetaSpectralCoordinate rho.1).im ^ 2 / (Real.log 2 * R ^ 4)) ≤
      suzukiXiEtaFiniteReflectionCompletedStrip rho l r N := by
  have hil := intervalIntegrable_suzukiXiEtaFiniteReflectionCompletedSide rho N hlv
    (fun y hy => (hreg.strip hu hy).1)
  have hir := intervalIntegrable_suzukiXiEtaFiniteReflectionCompletedSide rho N hrv
    (fun y hy => (hreg.strip hu hy).2)
  have h := intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := 1 / 2)
    (by norm_num) intervalIntegrable_const (hir.sub hil)
    (fun y hy => suzukiXiEtaFiniteReflectionCompletedSide_pair_lower rho N hR hl hr ha hy hlcos hrcos hlsin hrsin)
  rw [intervalIntegral.integral_const] at h
  change _ ≤ suzukiXiEtaFiniteReflectionCompletedStrip rho l r N at h
  convert h using 1
  simp only [sub_zero, smul_eq_mul]
  ring

/-- The exact pointwise decomposition retains the signed carrier
and the dyadic quadratic energy after the completed remainder is bounded. -/
theorem suzukiXiEtaFiniteReflectionCompletedSide_eq_carrier_sub_energy
    (rho : NontrivialZetaZero) (v : ℝ) (N : ℕ) (y : ℝ) :
    suzukiXiEtaFiniteReflectionCompletedSide rho v N y =
      (suzukiXiReflectionWeight rho ((v : ℂ) + (y : ℂ) * I) *
        suzukiXiEtaFiniteCarrier N ((v : ℂ) + (y : ℂ) * I)).re -
      suzukiEtaDyadicWeightCoefficient (I * suzukiXiReflectionWeight rho ((v : ℂ) + (y : ℂ) * I))
        (suzukiArithmeticZetaArgument ((v : ℂ) + (y : ℂ) * I)) *
        normSq (suzukiXiEtaFiniteCarrier N ((v : ℂ) + (y : ℂ) * I)) := by
  have h := im_mul_suzukiEtaFiniteCarrier_eq_completed_add_energy
    (I * suzukiXiReflectionWeight rho ((v : ℂ) + (y : ℂ) * I)) N
    (suzukiArithmeticZetaArgument ((v : ℂ) + (y : ℂ) * I))
  rw [mul_assoc, I_mul_im] at h
  dsimp only [suzukiXiEtaFiniteReflectionCompletedSide, suzukiXiEtaFiniteCarrier]
  linarith

end
end RiemannGaussian
