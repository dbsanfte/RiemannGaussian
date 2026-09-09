/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Finite horizontal boundary limits through removable singularities

Analyticity along a compact real interval provides a common neighborhood
and an integrable bound for small horizontal displacements. Altering a
function at finitely many complex points changes none of these line
integrals. Together these facts allow actual meromorphic channels with
removable real singularities to reach their literal boundary integrals.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Topology Interval
namespace RiemannGaussian
noncomputable section

/-- An injective real parametrization meets a finite exceptional set at
only finitely many parameters, so the two interval integrals agree. -/
theorem intervalIntegral_comp_eq_of_finite_exception
    {f g : ℂ → ℂ} (S : Finset ℂ) (he : ∀ z ∉ S, f z = g z)
    (γ : ℝ → ℂ) (hinj : Function.Injective γ) (l r : ℝ) :
    (∫ x : ℝ in l..r, f (γ x)) = ∫ x : ℝ in l..r, g (γ x) := by
  have hfin : {x : ℝ | γ x ∈ S}.Finite :=
    S.finite_toSet.preimage hinj.injOn
  have hae : ∀ᵐ x : ℝ, γ x ∉ S :=
    (ae_iff.mpr (by simpa only [not_not] using hfin.measure_zero (μ := volume)))
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hae] with x hx
  exact fun _ => he _ hx

/-- A finite exceptional set in the complex plane changes no horizontal
interval integral, for any height and either endpoint orientation. -/
theorem horizontalIntervalIntegral_eq_of_finite_exception
    {f g : ℂ → ℂ} (S : Finset ℂ) (he : ∀ z ∉ S, f z = g z) (l r b : ℝ) :
    (∫ x : ℝ in l..r, f ((x : ℂ) + (b : ℂ) * I)) =
      ∫ x : ℝ in l..r, g ((x : ℂ) + (b : ℂ) * I) := by
  apply intervalIntegral_comp_eq_of_finite_exception S he
  intro x y h
  simpa using congrArg Complex.re h

/-- Analyticity at every point of a compact real segment gives continuity
of its horizontal interval integral as the height crosses zero. -/
theorem continuousAt_horizontalIntervalIntegral_of_analyticAt
    {F : ℂ → ℂ} (l r : ℝ) (hF : ∀ x ∈ uIcc l r, AnalyticAt ℂ F (x : ℂ)) :
    ContinuousAt (fun b : ℝ => ∫ x : ℝ in l..r, F ((x : ℂ) + (b : ℂ) * I)) 0 := by
  let K : Set ℂ := Complex.ofReal '' uIcc l r
  have hK : IsCompact K := isCompact_uIcc.image Complex.continuous_ofReal
  obtain ⟨δ, hδ, hstrip⟩ := hK.exists_cthickening_subset_open (isOpen_analyticAt ℂ F)
    (by rintro z ⟨x, hx, rfl⟩; exact hF x hx)
  let Q : Set ℂ := uIcc l r ×ℂ Icc (-δ) δ
  have hQ : IsCompact Q := isCompact_uIcc.reProdIm isCompact_Icc
  have hQF : ∀ z ∈ Q, AnalyticAt ℂ F z := by
    intro z hz
    have hz' : z.re ∈ uIcc l r ∧ z.im ∈ Icc (-δ) δ := hz
    apply hstrip
    apply mem_cthickening_of_dist_le z (z.re : ℂ) δ K ⟨z.re, hz'.1, rfl⟩
    have hd : dist z (z.re : ℂ) = |z.im| := by
      rw [dist_eq_norm, show z - (z.re : ℂ) = (z.im : ℂ) * I by
        linear_combination -(Complex.re_add_im z)]
      simp
    rw [hd]
    exact abs_le.mpr hz'.2
  have hcont : ContinuousOn F Q := fun z hz => (hQF z hz).continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := hQ.bddAbove_image hcont.norm
  have hmem (x b : ℝ) (hx : x ∈ uIcc l r) (hb : b ∈ Icc (-δ) δ) :
      (x : ℂ) + (b : ℂ) * I ∈ Q := by
    simpa only [Q, Complex.mem_reProdIm, add_re, ofReal_re, mul_re, I_re, mul_zero,
      ofReal_im, I_im, zero_mul, sub_self, add_zero, add_im, mul_im, mul_one, zero_add] using
      And.intro hx hb
  have hnhds : Icc (-δ) δ ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (by linarith) hδ
  apply intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ => M)
  · filter_upwards [hnhds] with b hb
    have hc : ContinuousOn (fun x : ℝ => F ((x : ℂ) + (b : ℂ) * I)) (uIcc l r) := by
      intro x hx
      exact ((hQF _ (hmem x b hx hb)).continuousAt.comp
        (f := fun x : ℝ => (x : ℂ) + (b : ℂ) * I) (by fun_prop)).continuousWithinAt
    exact (hc.aestronglyMeasurable measurableSet_uIcc).mono_set uIoc_subset_uIcc
  · filter_upwards [hnhds] with b hb
    exact Eventually.of_forall fun x hx => hM ⟨_, hmem x b (uIoc_subset_uIcc hx) hb, rfl⟩
  · exact intervalIntegrable_const
  · apply Eventually.of_forall
    intro x hx
    have hc : ContinuousAt F ((x : ℂ) + ((0 : ℝ) : ℂ) * I) := by
      simpa only [ofReal_zero, zero_mul, add_zero] using
        (hF x (uIoc_subset_uIcc hx)).continuousAt
    exact hc.comp (f := fun b : ℝ => (x : ℂ) + (b : ℂ) * I) (by fun_prop)

/-- An analytic representative on the real segment suffices for the
literal channel's boundary limit when they differ at only finitely many
complex points. The original exceptional values are retained in the integral. -/
theorem continuousAt_horizontalIntervalIntegral_of_finite_regularization
    {f F : ℂ → ℂ} (S : Finset ℂ) (l r : ℝ)
    (hF : ∀ x ∈ uIcc l r, AnalyticAt ℂ F (x : ℂ)) (he : ∀ z ∉ S, F z = f z) :
    ContinuousAt (fun b : ℝ => ∫ x : ℝ in l..r, f ((x : ℂ) + (b : ℂ) * I)) 0 := by
  have heq : (fun b : ℝ => ∫ x : ℝ in l..r, f ((x : ℂ) + (b : ℂ) * I)) =
      (fun b : ℝ => ∫ x : ℝ in l..r, F ((x : ℂ) + (b : ℂ) * I)) := by
    funext b
    exact (horizontalIntervalIntegral_eq_of_finite_exception S he l r b).symm
  rw [heq]
  exact continuousAt_horizontalIntervalIntegral_of_analyticAt l r hF

end
end RiemannGaussian
