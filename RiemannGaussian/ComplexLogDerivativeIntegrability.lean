/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianXiDivisorContour
import RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevLogAverageLaplaceBoundaryHeatFiniteAreaIntegrability
import Mathlib.MeasureTheory.Topology

/-!
# Planar integrability of genuine logarithmic derivatives

A finite-order analytic zero contributes its exact multiplicity divided
by `z-a`, plus an analytic remainder. A complex simple pole is locally
integrable in area. Thus logarithmic derivatives have genuine compact
L1 bounds through their zeros, without taking principal values.
-/

open Complex Filter MeasureTheory Metric Set Topology
namespace RiemannGaussian
noncomputable section

/-- The logarithmic derivative is integrable in area on a neighborhood
of any finite-order analytic point, including a zero of arbitrary order. -/
theorem AnalyticAt.integrableAtFilter_logDeriv_of_finite_order
    {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a) (hfinite : analyticOrderAt f a ≠ ⊤) :
    IntegrableAtFilter (logDeriv f) (𝓝 a) volume := by
  obtain ⟨g, hg, heq⟩ := AnalyticAt.exists_logDeriv_eq_principalPart_add_analytic hf hfinite
  have he := eventually_nhdsWithin_iff.mp heq
  obtain ⟨R, hR, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (hg.eventually_analyticAt.and he)
  have hgC : ContinuousOn g (closedBall a R) :=
    fun z hz => (hball hz).1.continuousAt.continuousWithinAt
  have hp := ((locallyIntegrable_complex_inv_sub a).integrableOn_isCompact
    (isCompact_closedBall a R)).const_mul (analyticOrderNatAt f a : ℂ)
  have hi := hp.add (hgC.integrableOn_compact (isCompact_closedBall a R))
  refine ⟨closedBall a R, closedBall_mem_nhds a hR, hi.congr ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_closedBall,
    (volume.restrict (closedBall a R)).ae_ne a] with z hz hza
  simpa only [div_eq_mul_inv, Pi.add_apply] using ((hball hz).2 hza).symm

/-- An entire function of finite analytic order at every point has a
locally integrable logarithmic derivative on the whole complex plane. -/
theorem locallyIntegrable_logDeriv_of_entire_finite_order {f : ℂ → ℂ}
    (hf : ∀ z, AnalyticAt ℂ f z) (hfinite : ∀ z, analyticOrderAt f z ≠ ⊤) :
    LocallyIntegrable (logDeriv f) volume :=
  fun z => AnalyticAt.integrableAtFilter_logDeriv_of_finite_order (hf z) (hfinite z)

/-- One genuine nonzero value makes an entire function nonzero almost
everywhere in the plane; the exceptional analytic divisor has area zero. -/
theorem ae_ne_zero_of_entire_nonzero {f : ℂ → ℂ}
    (hf : ∀ z, AnalyticAt ℂ f z) {a : ℂ} (ha : f a ≠ 0) :
    ∀ᵐ z : ℂ, f z ≠ 0 := by
  have hA : AnalyticOnNhd ℂ f univ := fun z _ => hf z
  have h := hA.preimage_zero_mem_codiscreteWithin ha (mem_univ a) isConnected_univ
  have he := ae_restrict_le_codiscreteWithin (μ := (volume : Measure ℂ)) MeasurableSet.univ h
  rw [Measure.restrict_univ] at he
  filter_upwards [he] with z hz
  exact hz

end
end RiemannGaussian
