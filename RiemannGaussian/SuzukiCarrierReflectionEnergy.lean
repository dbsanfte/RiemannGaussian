/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiCarrierReflectionComparison

/-!
# Strict reflection energy and the remaining source ceiling

For an off-axis node the actual reflection Gram is strictly positive.
Retaining this energy in the signed contour identity gives a positive
limiting excess over the reflected source. Thus an independent eventual
source ceiling would suffice; it would not need a prescribed strict
deficit below the source. That independent ceiling remains open.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Topology
namespace RiemannGaussian
noncomputable section

/-- The literal real-axis carrier is nonzero almost everywhere. Both
xi and carrier-denominator exceptional sets are controlled by the proved
countability of the actual entire divisor. -/
theorem ae_suzukiRealAxisXiZeroCarrier_ne_zero :
    ∀ᵐ x : ℝ, suzukiRealAxisXiZeroCarrier x ≠ 0 := by
  have hc : {x : ℝ | (x : ℂ) ∈ suzukiXiCarrierSingularSet}.Countable :=
    countable_suzukiXiCarrierSingularSet.preimage Complex.ofReal_injective
  have hae : ∀ᵐ x : ℝ, (x : ℂ) ∉ suzukiXiCarrierSingularSet := by
    apply ae_iff.mpr
    simpa only [not_not] using hc.measure_zero (μ := volume)
  filter_upwards [hae] with x hx
  have hA : riemannXiSpectral (x : ℂ) ≠ 0 := fun h => hx (Or.inl h)
  have hE : suzukiXiEValue (x : ℂ) ≠ 0 := fun h => hx (Or.inr h)
  rw [suzukiRealAxisXiZeroCarrier, suzukiXiZeroCarrier_eq_i_mul_xi_div_E hE]
  exact div_ne_zero (mul_ne_zero I_ne_zero hA) hE

/-- Distinct reflected nodes have a nonzero resolvent difference at
every complex argument, with inverse totalization respected at the nodes. -/
theorem suzukiXiReflectionCauchyDifference_ne_zero
    (rho : NontrivialZetaZero) (him : (zetaSpectralCoordinate rho.1).im ≠ 0) (z : ℂ) :
    suzukiXiReflectionCauchyDifference rho z ≠ 0 := by
  intro hz
  have he := inv_inj.mp (sub_eq_zero.mp hz)
  have hnodes : zetaSpectralCoordinate rho.1 = starRingEnd ℂ (zetaSpectralCoordinate rho.1) := by
    linear_combination -he
  have hh := congrArg Complex.im hnodes
  rw [conj_im] at hh
  exact him (by linarith)

/-- The complete actual reflection energy, with the original common
carrier normalization and both mixed entries retained. -/
def suzukiXiReflectionBoundaryEnergy (rho : NontrivialZetaZero) : ℝ :=
  (suzukiXiReflectionPairQuadratic rho suzukiXiBoundaryCarrierGramKernel).re

private lemma integrable_reflection_density (rho : NontrivialZetaZero) :
    Integrable (fun x : ℝ => suzukiXiReflectionPairQuadratic rho
      (fun a b => suzukiXiBoundaryCarrierGramIntegrand a b x)) := by
  exact (((integrable_suzukiXiBoundaryCarrierGramIntegrand rho rho).sub
    (integrable_suzukiXiBoundaryCarrierGramIntegrand rho rho.conjugatePartner)).sub
    (integrable_suzukiXiBoundaryCarrierGramIntegrand rho.conjugatePartner rho)).add
    (integrable_suzukiXiBoundaryCarrierGramIntegrand rho.conjugatePartner rho.conjugatePartner)

/-- The complete reflection energy is the genuine integral of its real
Gram density, with no contour representation used to establish its sign. -/
theorem suzukiXiReflectionBoundaryEnergy_eq_integral (rho : NontrivialZetaZero) :
    suzukiXiReflectionBoundaryEnergy rho = ∫ x : ℝ,
      (suzukiXiReflectionPairQuadratic rho (fun a b => suzukiXiBoundaryCarrierGramIntegrand a b x)).re := by
  have hi := integrable_suzukiXiBoundaryCarrierGramIntegrand
  have hi01 : Integrable (fun x : ℝ => suzukiXiBoundaryCarrierGramIntegrand rho rho x -
      suzukiXiBoundaryCarrierGramIntegrand rho rho.conjugatePartner x) :=
    (hi rho rho).sub (hi rho rho.conjugatePartner)
  have hi010 : Integrable (fun x : ℝ =>
      (suzukiXiBoundaryCarrierGramIntegrand rho rho x - suzukiXiBoundaryCarrierGramIntegrand rho rho.conjugatePartner x) -
        suzukiXiBoundaryCarrierGramIntegrand rho.conjugatePartner rho x) :=
    hi01.sub (hi rho.conjugatePartner rho)
  have he : suzukiXiReflectionPairQuadratic rho suzukiXiBoundaryCarrierGramKernel =
      ∫ x : ℝ, suzukiXiReflectionPairQuadratic rho (fun a b => suzukiXiBoundaryCarrierGramIntegrand a b x) := by
    unfold suzukiXiReflectionPairQuadratic suzukiXiBoundaryCarrierGramKernel
    rw [← integral_sub (hi rho rho) (hi rho rho.conjugatePartner),
      ← integral_sub hi01 (hi rho.conjugatePartner rho),
      ← integral_add hi010 (hi rho.conjugatePartner rho.conjugatePartner)]
  rw [suzukiXiReflectionBoundaryEnergy, he]
  exact (Complex.reCLM.integral_comp_comm (integrable_reflection_density rho)).symm

/-- The actual full reflection energy is strictly positive for every
off-axis zero. This supplies a retained positive excess over the xi source. -/
theorem suzukiXiReflectionBoundaryEnergy_pos (rho : NontrivialZetaZero)
    (him : (zetaSpectralCoordinate rho.1).im ≠ 0) :
    0 < suzukiXiReflectionBoundaryEnergy rho := by
  rw [suzukiXiReflectionBoundaryEnergy_eq_integral]
  let f := fun x : ℝ => (suzukiXiReflectionPairQuadratic rho
    (fun a b => suzukiXiBoundaryCarrierGramIntegrand a b x)).re
  have hf : Integrable f := Complex.reCLM.integrable_comp (integrable_reflection_density rho)
  have hp : ∀ᵐ x : ℝ, 0 < f x := by
    filter_upwards [ae_suzukiRealAxisXiZeroCarrier_ne_zero] with x hx
    dsimp only [f]
    rw [suzukiXiReflectionPairQuadratic_gramIntegrand, ← Complex.normSq_eq_conj_mul_self, ofReal_re]
    exact Complex.normSq_pos.mpr (mul_ne_zero hx (suzukiXiReflectionCauchyDifference_ne_zero rho him _))
  apply (integral_pos_iff_support_of_nonneg_ae (hp.mono fun _ h => h.le) hf).2
  have he : (Function.support f : Set ℝ) =ᵐ[volume] Set.univ := by
    filter_upwards [hp] with x hx
    apply propext
    constructor
    · intro _
      trivial
    · intro _
      exact hx.ne'
  rw [measure_congr he]
  simp

/-- Any exhaustion of the real axis recovers the complete reflection
energy with its two mixed terms, before applying positivity. -/
theorem tendsto_suzukiXiReflection_truncated_energy
    (rho : NontrivialZetaZero) {l r : ℕ → ℝ}
    (hl : Tendsto l atTop atBot) (hr : Tendsto r atTop atTop) :
    Tendsto (fun n => (suzukiXiReflectionPairQuadratic rho
      (fun a b => suzukiXiTruncatedBoundaryCarrierGramKernel a b (l n) (r n))).re) atTop
      (𝓝 (suzukiXiReflectionBoundaryEnergy rho)) := by
  have h00 := tendsto_suzukiXiTruncatedBoundaryCarrierGramKernel rho rho hl hr
  have h01 := tendsto_suzukiXiTruncatedBoundaryCarrierGramKernel rho rho.conjugatePartner hl hr
  have h10 := tendsto_suzukiXiTruncatedBoundaryCarrierGramKernel rho.conjugatePartner rho hl hr
  have h11 := tendsto_suzukiXiTruncatedBoundaryCarrierGramKernel rho.conjugatePartner rho.conjugatePartner hl hr
  exact Complex.continuous_re.continuousAt.tendsto.comp (((h00.sub h01).sub h10).add h11)

end
end RiemannGaussian
