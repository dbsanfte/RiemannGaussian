import RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevLogAverageLaplaceBoundaryHeatFiniteExcision
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# Genuine finite-window area integrability for arithmetic boundary heat

The preceding finite-window theorem assembles Cauchy--Green term by term,
because the weighted principal parts have singularities at the xi divisor.
Those singularities are nevertheless locally integrable in two real
dimensions.  This file proves that fact from the exact radial power bound,
transports it to arbitrary pole centers using invariance of complex Lebesgue
measure, and identifies the project's iterated rectangular area integral
with an ordinary complex-plane set integral.

Consequently the complete finite-window arithmetic source is integrable
through every selected xi zero.  No value at a pole, improper-integral
exchange, or unproved divisor statement is used: equality with the analytic
regularization is needed only almost everywhere, and the exceptional set is
the already-proved finite xi window.
-/

namespace RiemannGaussian

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Interval Topology

/-! ## Locally integrable complex principal parts -/

/-- Complex inversion is locally integrable for planar Lebesgue measure.
The proof uses the exact singular bound `‖z‖⁻¹` and the real dimension
`finrank ℝ ℂ = 2`. -/
theorem locallyIntegrable_complex_inv :
    LocallyIntegrable (fun z : ℂ => z⁻¹) volume := by
  refine locallyIntegrable_of_norm_le_rpow (E := ℂ) (F := ℂ)
      (C := 1) (α := 1) (by norm_num [Complex.finrank_real_complex])
      (by norm_num [Complex.finrank_real_complex]) ?_ ?_
  · filter_upwards with z
    rw [norm_inv, one_mul, Real.rpow_neg_one]
  · exact measurable_id.inv.aestronglyMeasurable

/-- Translation invariance of complex Lebesgue measure moves the locally
integrable inverse singularity from the origin to any prescribed center. -/
theorem locallyIntegrable_complex_inv_sub (c : ℂ) :
    LocallyIntegrable (fun z : ℂ => (z - c)⁻¹) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  let e : ℂ → ℂ := fun z => -c + z
  have hecont : Continuous e := by fun_prop
  have hein : Function.Injective e := by
    intro z w h
    simpa [e] using congrArg (fun q : ℂ => c + q) h
  have himage : IsCompact (e '' K) := hK.image hecont
  have hright : IntegrableOn (fun w : ℂ => w⁻¹) (e '' K) volume :=
    locallyIntegrable_complex_inv.integrableOn_isCompact himage
  have hcomp : IntegrableOn ((fun w : ℂ => w⁻¹) ∘ e)
      (e ⁻¹' (e '' K)) volume :=
    ((measurePreserving_add_left volume (-c)).integrableOn_comp_preimage
      (MeasurableEquiv.addLeft (-c)).measurableEmbedding).2 hright
  have hpre : e ⁻¹' (e '' K) = K := Set.preimage_image_eq K hein
  rw [hpre] at hcomp
  simpa [e, Function.comp_def, sub_eq_add_neg, add_comm] using hcomp

/-- Every complex simple-pole kernel is locally integrable through its pole. -/
theorem locallyIntegrable_simplePoleKernel (L c : ℂ) :
    LocallyIntegrable (simplePoleKernel L c) volume := by
  have h := LocallyIntegrable.continuous_mul
    (continuous_const : Continuous (fun _ : ℂ => L))
    (locallyIntegrable_complex_inv_sub c)
  change LocallyIntegrable (fun z : ℂ => L * (z - c)⁻¹) volume
  exact h

/-- Multiplying a simple pole by the smooth boundary-heat Cauchy--Green
source preserves local integrability through the pole. -/
theorem locallyIntegrable_suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePoleSource
    (x tau : ℝ) (L c : ℂ) :
    LocallyIntegrable
      (suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePoleSource
        x tau L c) volume := by
  have h := LocallyIntegrable.continuous_mul
    (continuous_suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource x tau)
    (locallyIntegrable_simplePoleKernel L c)
  change LocallyIntegrable (fun z : ℂ =>
    suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource x tau z *
      simplePoleKernel L c z) volume
  exact h

/-! ## Rectangular iterated integrals as planar set integrals -/

/-- For an integrable function and correctly ordered endpoints, the iterated
rectangular area integral used by the Cauchy--Green development is exactly
the Lebesgue set integral over the corresponding closed subset of `ℂ`.
Fubini, the volume-preserving real-coordinate equivalence, and nullity of the
one-dimensional endpoint faces are all discharged explicitly. -/
theorem rectangularAreaIntegral_eq_setIntegral
    {l r b u : ℝ} (hlr : l ≤ r) (hbu : b ≤ u) (g : ℂ → ℂ)
    (hg : IntegrableOn g ([[l, r]] ×ℂ [[b, u]]) volume) :
    rectangularAreaIntegral l r b u g =
      ∫ z in [[l, r]] ×ℂ [[b, u]], g z ∂volume := by
  let A : Set ℝ := Set.Icc l r
  let B : Set ℝ := Set.Icc b u
  let R : Set ℂ := A ×ℂ B
  let f : ℝ × ℝ → ℂ := fun p =>
    g (Complex.equivRealProdCLM.symm p)
  have hR : R = [[l, r]] ×ℂ [[b, u]] := by
    simp [R, A, B, uIcc_of_le hlr, uIcc_of_le hbu]
  have hpre : Complex.measurableEquivRealProd.symm ⁻¹' R = A ×ˢ B := by
    rfl
  have hpair : IntegrableOn f (A ×ˢ B) (volume.prod volume) := by
    have h :=
      ((Complex.volume_preserving_equiv_real_prod.symm _).integrableOn_comp_preimage
        (MeasurableEquiv.measurableEmbedding _)).2
        (show IntegrableOn g R volume from hR.symm ▸ hg)
    rw [hpre] at h
    rw [Measure.volume_eq_prod ℝ ℝ] at h
    exact h
  have hprod : Integrable f ((volume.restrict A).prod (volume.restrict B)) := by
    rw [Measure.prod_restrict]
    exact hpair
  have hchange :=
    (Complex.volume_preserving_equiv_real_prod.symm _).setIntegral_preimage_emb
      (MeasurableEquiv.measurableEmbedding _) g R
  unfold rectangularAreaIntegral
  rw [intervalIntegral.integral_of_le hlr]
  simp_rw [intervalIntegral.integral_of_le hbu,
    setIntegral_congr_set (Ioc_ae_eq_Icc (α := ℝ) (μ := volume))]
  calc
    (∫ a in Set.Icc l r, ∫ y in Set.Icc b u,
        g ((a : ℂ) + (y : ℂ) * Complex.I) ∂volume ∂volume) =
        ∫ p, f p ∂((volume.restrict A).prod (volume.restrict B)) := by
      simpa [f, A, B, Complex.equivRealProdCLM_symm_apply] using
        (integral_prod f hprod).symm
    _ = ∫ p in A ×ˢ B, f p ∂(volume.prod volume) := by
      rw [Measure.prod_restrict]
    _ = ∫ z in R, g z ∂volume := by
      rw [hpre] at hchange
      rw [Measure.volume_eq_prod ℝ ℝ] at hchange
      exact hchange
    _ = ∫ z in [[l, r]] ×ℂ [[b, u]], g z ∂volume := by
      rw [hR]

/-! ## The actual finite-window arithmetic source -/

/-- The explicit planar Cauchy--Green source of the heat-weighted arithmetic
response, defined at every point using Lean's totalized arithmetic
continuation. -/
def suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource
    (x tau : ℝ) (z : ℂ) : ℂ :=
  suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource x tau z *
    suzukiChebyshevLogAverageLaplacePoleClearedContinuation z

/-- Away from the genuine finite xi divisor, the actual arithmetic source is
exactly the finite sum of locally integrable principal-part sources plus the
source formed from one analytic remainder. -/
theorem exists_suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource_finitePrincipalPartDecomposition
    (x tau : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ∃ F : ℂ → ℂ,
      (∀ z ∈ suzukiChebyshevLaplaceFiniteSlab T, AnalyticAt ℂ F z) ∧
      (∀ z ∉ suzukiChebyshevLaplaceZeroWindow T,
        suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource x tau z =
          (∑ rho ∈ spectralZetaZeroWindow T,
            suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePoleSource x tau
              (analyticZetaZeroMultiplicity rho : ℂ)
              (suzukiChebyshevLaplaceZeroCoordinate rho) z) +
          suzukiChebyshevLaplaceBoundaryHeatWeightedAnalyticRemainderSource
            x tau F z) := by
  obtain ⟨F, hF, hdecomp⟩ :=
    exists_suzukiChebyshevLaplacePoleClearedWindowAnalyticDecomposition hT
  refine ⟨F, hF, ?_⟩
  intro z hz
  unfold suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource
    suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePoleSource
    suzukiChebyshevLaplaceBoundaryHeatWeightedAnalyticRemainderSource
  rw [hdecomp z hz, mul_add]
  unfold suzukiChebyshevLaplacePoleClearedWindowPrincipalSum
    suzukiChebyshevLaplacePoleClearedPrincipalPart
  rw [Finset.mul_sum]

/-- On every rectangle inside a complete positive bounded-height slab, the
actual arithmetic Cauchy--Green source is genuinely Lebesgue integrable
through all xi zeros in the finite window.  The exceptional divisor is
finite and hence null; no pointwise identity at a pole is asserted. -/
theorem integrableOn_suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource_finiteRectangle
    (x tau l r b u : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hrectangle : [[l, r]] ×ℂ [[b, u]] ⊆
      suzukiChebyshevLaplaceFiniteSlab T) :
    IntegrableOn
      (suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource x tau)
      ([[l, r]] ×ℂ [[b, u]]) volume := by
  let R : Set ℂ := [[l, r]] ×ℂ [[b, u]]
  let W := spectralZetaZeroWindow T
  obtain ⟨F, hF, hdecomp⟩ :=
    exists_suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource_finitePrincipalPartDecomposition
      x tau hT
  let P : NontrivialZetaZero → ℂ → ℂ := fun rho =>
    suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePoleSource x tau
      (analyticZetaZeroMultiplicity rho : ℂ)
      (suzukiChebyshevLaplaceZeroCoordinate rho)
  let H : ℂ → ℂ :=
    suzukiChebyshevLaplaceBoundaryHeatWeightedAnalyticRemainderSource x tau F
  have hcompact : IsCompact R :=
    isCompact_uIcc.reProdIm isCompact_uIcc
  have hpole : ∀ rho ∈ W, IntegrableOn (P rho) R volume := by
    intro rho hrho
    exact
      (locallyIntegrable_suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePoleSource
        x tau (analyticZetaZeroMultiplicity rho : ℂ)
          (suzukiChebyshevLaplaceZeroCoordinate rho)).integrableOn_isCompact
        hcompact
  have hsum : IntegrableOn (fun z => ∑ rho ∈ W, P rho z) R volume := by
    exact integrable_finsetSum W hpole
  have hrem : IntegrableOn H R volume := by
    exact
      ((continuous_suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource
          x tau).continuousOn.mul
        (show AnalyticOnNhd ℂ F R from
          fun z hz => hF z (hrectangle hz)).continuousOn).integrableOn_compact
        hcompact
  have hregular : IntegrableOn
      (fun z => (∑ rho ∈ W, P rho z) + H z) R volume :=
    hsum.add hrem
  apply hregular.congr_fun_ae
  filter_upwards [ae_restrict_of_ae
      ((suzukiChebyshevLaplaceZeroWindow T).finite_toSet.countable.ae_notMem
        volume)] with z hz
  symm
  simpa [W, P, H] using hdecomp z hz

/-- The actual finite-window arithmetic source therefore admits an honest
planar set-integral interpretation on every ordered rectangle in its
complete slab. -/
theorem rectangularAreaIntegral_suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource_eq_setIntegral
    (x tau l r b u : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hlr : l ≤ r) (hbu : b ≤ u)
    (hrectangle : [[l, r]] ×ℂ [[b, u]] ⊆
      suzukiChebyshevLaplaceFiniteSlab T) :
    rectangularAreaIntegral l r b u
        (suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource x tau) =
      ∫ z in [[l, r]] ×ℂ [[b, u]],
        suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource x tau z
        ∂volume := by
  exact rectangularAreaIntegral_eq_setIntegral hlr hbu _
    (integrableOn_suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource_finiteRectangle
      x tau l r b u hT hrectangle)

end

end RiemannGaussian
