/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiCarrierPhase
import RiemannGaussian.AnalyticDoublePoleMoments

/-!
# Local polar cancellation in Suzuki's signed carrier

At every genuine spectral xi zero of multiplicity `m`, both carrier
channels have a removable simple zero with slope `1/m`. Their diagonal
quotients have identical simple-pole coefficients. The signed difference
cancels those poles, including at multiple zeros.

The statements concern punctured neighborhoods of the literal carrier;
its totalized values at denominator zeros are not changed. These local
identities supply the divisor terms for a subsequent global signed contour
estimate. They do not assert that off-axis denominator poles are absent.
-/

open Complex Filter MeasureTheory Metric Set
open scoped Classical Topology

namespace RiemannGaussian
noncomputable section

/-- The reflected carrier, whose real-axis restriction is the conjugate
channel in the signed arithmetic Gram. -/
def suzukiXiSharpCarrier (z : ℂ) : ℂ :=
  starRingEnd ℂ (suzukiXiZeroCarrier (starRingEnd ℂ z))

/-- The reflected carrier agrees with the literal boundary conjugate,
including the already totalized exceptional values. -/
theorem suzukiXiSharpCarrier_ofReal (x : ℝ) :
    suzukiXiSharpCarrier (x : ℂ) =
      starRingEnd ℂ (suzukiRealAxisXiZeroCarrier x) := by
  simp [suzukiXiSharpCarrier, suzukiRealAxisXiZeroCarrier]

/-- Off its denominator divisor, the reflected carrier has the opposite
Cayley parameter and the exact reflected denominator. -/
theorem suzukiXiSharpCarrier_eq_neg_i_mul_xi_div_sharp
    {z : ℂ} (hE : suzukiXiESharpValue z ≠ 0) :
    suzukiXiSharpCarrier z = -I * riemannXiSpectral z / suzukiXiESharpValue z := by
  have hEc : suzukiXiEValue (starRingEnd ℂ z) ≠ 0 := by
    intro he
    apply hE
    rw [suzukiXiESharpValue_eq_conj_E_conj, he, map_zero]
  unfold suzukiXiSharpCarrier
  rw [suzukiXiZeroCarrier_eq_i_mul_xi_div_E hEc, map_div₀, map_mul,
    Complex.conj_I, riemannXiSpectral_conj, starRingEnd_self_apply,
    ← suzukiXiESharpValue_eq_conj_E_conj]

/-- Every nonzero complex Cayley parameter has the same local slope at a
genuine xi zero. The denominator is proved nonzero punctured-locally. -/
theorem exists_suzukiXiCayley_local_model
    (rho : NontrivialZetaZero) {b : ℂ} (hb : b ≠ 0) :
    ∃ q : ℂ → ℂ, AnalyticAt ℂ q (zetaSpectralCoordinate rho.1) ∧
      q (zetaSpectralCoordinate rho.1) = (analyticZetaZeroMultiplicity rho : ℂ)⁻¹ ∧
      ∀ᶠ z in 𝓝[≠] zetaSpectralCoordinate rho.1,
        riemannXiSpectral z + b * deriv riemannXiSpectral z ≠ 0 ∧
        b * riemannXiSpectral z /
            (riemannXiSpectral z + b * deriv riemannXiSpectral z) =
          (z - zetaSpectralCoordinate rho.1) * q z := by
  let alpha := zetaSpectralCoordinate rho.1
  let m : ℂ := analyticZetaZeroMultiplicity rho
  have hm : m ≠ 0 := by
    dsimp [m]
    exact_mod_cast (analyticZetaZeroMultiplicity_positive rho).ne'
  obtain ⟨h, hh, hlog⟩ :=
    exists_logDeriv_riemannXiSpectral_eq_zetaPrincipalPart_add_analytic rho
  let D : ℂ → ℂ := fun z ↦ b * m + (z - alpha) * (1 + b * h z)
  have hDa : AnalyticAt ℂ D alpha := by
    exact analyticAt_const.add
      ((analyticAt_id.sub analyticAt_const).mul
        (analyticAt_const.add (analyticAt_const.mul hh)))
  have hD0 : D alpha ≠ 0 := by
    simpa [D] using mul_ne_zero hb hm
  let q : ℂ → ℂ := fun z ↦ b / D z
  have hq : AnalyticAt ℂ q alpha := analyticAt_const.div hDa hD0
  have hq0 : q alpha = m⁻¹ := by
    dsimp [q, D]
    simp only [sub_self, zero_mul, add_zero]
    field_simp
  have hfinite : analyticOrderAt riemannXiSpectral alpha ≠ ⊤ := by
    dsimp [alpha]
    rw [analyticOrderAt_riemannXiSpectral_zetaSpectralCoordinate,
      analyticOrderAt_riemannXi_eq_riemannZeta]
    exact analyticOrderAt_riemannZeta_nontrivialZero_ne_top rho
  have hxiNe : ∀ᶠ z in 𝓝[≠] alpha, riemannXiSpectral z ≠ 0 :=
    (analyticAt_riemannXiSpectral alpha).eventually_eq_zero_or_eventually_ne_zero.resolve_left
      fun hzero ↦ hfinite (analyticOrderAt_eq_top.mpr hzero)
  have hDNe : ∀ᶠ z in 𝓝[≠] alpha, D z ≠ 0 :=
    (hDa.continuousAt.eventually_ne hD0).filter_mono nhdsWithin_le_nhds
  refine ⟨q, hq, hq0, ?_⟩
  filter_upwards [hlog, hxiNe, hDNe, self_mem_nhdsWithin]
      with z hzlog hxi hDz hza
  have hsub : z - alpha ≠ 0 := sub_ne_zero.mpr hza
  have hDidentity : D z = (z - alpha) *
      (1 + b * logDeriv riemannXiSpectral z) := by
    dsimp [D, alpha, m]
    rw [hzlog]
    field_simp [show z - zetaSpectralCoordinate rho.1 ≠ 0 from hsub]
    ring
  have hfactor : 1 + b * logDeriv riemannXiSpectral z ≠ 0 := by
    intro he
    apply hDz
    rw [hDidentity, he, mul_zero]
  have hEfactor : riemannXiSpectral z + b * deriv riemannXiSpectral z =
      riemannXiSpectral z * (1 + b * logDeriv riemannXiSpectral z) := by
    rw [logDeriv_apply]
    field_simp [hxi]
  have hE : riemannXiSpectral z + b * deriv riemannXiSpectral z ≠ 0 := by
    rw [hEfactor]
    exact mul_ne_zero hxi hfactor
  refine ⟨hE, ?_⟩
  change _ = (z - alpha) * (b / D z)
  rw [hEfactor, hDidentity]
  field_simp [hxi, hsub, hfactor]

/-- Both literal carrier channels have simultaneous local analytic models
with slope `1/m`, at every genuine xi zero, real or nonreal. -/
theorem exists_suzukiXiCarrier_pair_local_model (rho : NontrivialZetaZero) :
    ∃ q r : ℂ → ℂ,
      AnalyticAt ℂ q (zetaSpectralCoordinate rho.1) ∧
      AnalyticAt ℂ r (zetaSpectralCoordinate rho.1) ∧
      q (zetaSpectralCoordinate rho.1) = (analyticZetaZeroMultiplicity rho : ℂ)⁻¹ ∧
      r (zetaSpectralCoordinate rho.1) = (analyticZetaZeroMultiplicity rho : ℂ)⁻¹ ∧
      ∀ᶠ z in 𝓝[≠] zetaSpectralCoordinate rho.1,
        suzukiXiEValue z ≠ 0 ∧ suzukiXiESharpValue z ≠ 0 ∧
        suzukiXiZeroCarrier z = (z - zetaSpectralCoordinate rho.1) * q z ∧
        suzukiXiSharpCarrier z = (z - zetaSpectralCoordinate rho.1) * r z := by
  obtain ⟨q, hq, hq0, hqe⟩ := exists_suzukiXiCayley_local_model rho I_ne_zero
  obtain ⟨r, hr, hr0, hre⟩ := exists_suzukiXiCayley_local_model rho (neg_ne_zero.mpr I_ne_zero)
  refine ⟨q, r, hq, hr, hq0, hr0, ?_⟩
  filter_upwards [hqe, hre] with z hzq hzr
  have hE : suzukiXiEValue z ≠ 0 := by simpa using hzq.1
  have hEs : suzukiXiESharpValue z ≠ 0 := by
    simpa [sub_eq_add_neg] using hzr.1
  refine ⟨hE, hEs, ?_, ?_⟩
  · rw [suzukiXiZeroCarrier_eq_i_mul_xi_div_E hE, suzukiXiEValue_eq]
    exact hzq.2
  · rw [suzukiXiSharpCarrier_eq_neg_i_mul_xi_div_sharp hEs, suzukiXiESharpValue_eq]
    simpa [sub_eq_add_neg] using hzr.2

/-- Off the two denominator divisors, the signed boundary identity extends
meromorphically as the product of the two reflected carrier channels. -/
theorem suzukiXiCarrier_signed_eq_product {z : ℂ}
    (hE : suzukiXiEValue z ≠ 0) (hEs : suzukiXiESharpValue z ≠ 0) :
    (suzukiXiZeroCarrier z - suzukiXiSharpCarrier z) / (2 * I) =
      suzukiXiZeroCarrier z * suzukiXiSharpCarrier z := by
  rw [suzukiXiZeroCarrier_eq_i_mul_xi_div_E hE,
    suzukiXiSharpCarrier_eq_neg_i_mul_xi_div_sharp hEs]
  field_simp [hE, hEs]
  rw [suzukiXiEValue_eq, suzukiXiESharpValue_eq]
  simp [I_sq]
  ring

/-- Each separated diagonal channel has precisely the same simple-pole
coefficient `1/m`. Both complete analytic remainders are retained. -/
theorem exists_suzukiXiCarrier_diagonal_polar_models (rho : NontrivialZetaZero) :
    ∃ p q : ℂ → ℂ,
      AnalyticAt ℂ p (zetaSpectralCoordinate rho.1) ∧
      AnalyticAt ℂ q (zetaSpectralCoordinate rho.1) ∧
      ∀ᶠ z in 𝓝[≠] zetaSpectralCoordinate rho.1,
        suzukiXiZeroCarrier z / (z - zetaSpectralCoordinate rho.1) ^ 2 =
          (analyticZetaZeroMultiplicity rho : ℂ)⁻¹ /
            (z - zetaSpectralCoordinate rho.1) + p z ∧
        suzukiXiSharpCarrier z / (z - zetaSpectralCoordinate rho.1) ^ 2 =
          (analyticZetaZeroMultiplicity rho : ℂ)⁻¹ /
            (z - zetaSpectralCoordinate rho.1) + q z := by
  obtain ⟨f, g, hf, hg, hf0, hg0, he⟩ := exists_suzukiXiCarrier_pair_local_model rho
  let alpha := zetaSpectralCoordinate rho.1
  refine ⟨dslope f alpha, dslope g alpha,
    analyticAt_dslope_of_analyticAt hf hf,
    analyticAt_dslope_of_analyticAt hg hg, ?_⟩
  filter_upwards [he, self_mem_nhdsWithin] with z hz hza
  have hne : z ≠ alpha := hza
  have hsub : z - alpha ≠ 0 := sub_ne_zero.mpr hne
  rw [hz.2.2.1, hz.2.2.2, dslope_of_ne f hne, dslope_of_ne g hne,
    slope_def_field, slope_def_field, hf0, hg0]
  dsimp [alpha] at hsub ⊢
  constructor <;> field_simp [hsub] <;> ring

/-- The signed diagonal quotient has a genuine analytic regularization at
every xi zero, with exact central value `1/m^2`. The two polar channels
cancel before any bound is taken. -/
theorem exists_suzukiXiCarrier_signed_diagonal_regularization (rho : NontrivialZetaZero) :
    ∃ F : ℂ → ℂ,
      AnalyticAt ℂ F (zetaSpectralCoordinate rho.1) ∧
      F (zetaSpectralCoordinate rho.1) = ((analyticZetaZeroMultiplicity rho : ℂ)⁻¹) ^ 2 ∧
      (fun z ↦ (suzukiXiZeroCarrier z - suzukiXiSharpCarrier z) /
        (2 * I * (z - zetaSpectralCoordinate rho.1) ^ 2)) =ᶠ[
          𝓝[≠] zetaSpectralCoordinate rho.1] F := by
  obtain ⟨f, g, hf, hg, hf0, hg0, he⟩ := exists_suzukiXiCarrier_pair_local_model rho
  refine ⟨fun z ↦ f z * g z, hf.mul hg, ?_, ?_⟩
  · change f _ * g _ = _
    rw [hf0, hg0, pow_two]
  · filter_upwards [he, self_mem_nhdsWithin] with z hz hza
    have hsub : z - zetaSpectralCoordinate rho.1 ≠ 0 := sub_ne_zero.mpr hza
    rw [← div_div, suzukiXiCarrier_signed_eq_product hz.1 hz.2.1,
      hz.2.2.1, hz.2.2.2]
    field_simp [hsub]

/-- The exact local signed diagonal limit is positive and depends only on
analytic multiplicity, with no zero simplicity or real-axis assumption. -/
theorem tendsto_suzukiXiCarrier_signed_diagonal (rho : NontrivialZetaZero) :
    Tendsto (fun z ↦ (suzukiXiZeroCarrier z - suzukiXiSharpCarrier z) /
        (2 * I * (z - zetaSpectralCoordinate rho.1) ^ 2))
      (𝓝[≠] zetaSpectralCoordinate rho.1)
      (𝓝 (((analyticZetaZeroMultiplicity rho : ℂ)⁻¹) ^ 2)) := by
  obtain ⟨F, hF, hF0, he⟩ := exists_suzukiXiCarrier_signed_diagonal_regularization rho
  rw [← hF0]
  exact (hF.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' he.symm

private theorem local_two_resolvent_polar_model
    {f q : ℂ → ℂ} {c : ℂ} (hq : AnalyticAt ℂ q c)
    (he : f =ᶠ[𝓝[≠] c] fun z ↦ (z - c) * q z) (u v : ℂ) :
    ∃ p : ℂ → ℂ, AnalyticAt ℂ p c ∧
      (fun z ↦ f z / ((z - u) * (z - v))) =ᶠ[𝓝[≠] c]
        fun z ↦ (if u = c ∧ v = c then q c else 0) / (z - c) + p z := by
  by_cases hu : u = c
  · subst u
    by_cases hv : v = c
    · subst v
      refine ⟨dslope q c, analyticAt_dslope_of_analyticAt hq hq, ?_⟩
      filter_upwards [he, self_mem_nhdsWithin] with z hz hzc
      have hsub := sub_ne_zero.mpr hzc
      simp only [and_self, ↓reduceIte]
      rw [hz, dslope_of_ne q hzc, slope_def_field]
      field_simp [hsub]
      ring
    · refine ⟨fun z ↦ q z / (z - v),
        hq.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr (Ne.symm hv)), ?_⟩
      filter_upwards [he, self_mem_nhdsWithin] with z hz hzc
      have hsub := sub_ne_zero.mpr hzc
      simp only [hv, and_false, ↓reduceIte, zero_div, zero_add]
      rw [hz]
      field_simp [hsub]
  · by_cases hv : v = c
    · subst v
      refine ⟨fun z ↦ q z / (z - u),
        hq.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr (Ne.symm hu)), ?_⟩
      filter_upwards [he, self_mem_nhdsWithin] with z hz hzc
      have hsub := sub_ne_zero.mpr hzc
      simp only [hu, false_and, ↓reduceIte, zero_div, zero_add]
      rw [hz]
      field_simp [hsub]
    · refine ⟨fun z ↦ (z - c) * q z / ((z - u) * (z - v)),
        ((analyticAt_id.sub analyticAt_const).mul hq).div
          ((analyticAt_id.sub analyticAt_const).mul (analyticAt_id.sub analyticAt_const))
          (mul_ne_zero (sub_ne_zero.mpr (Ne.symm hu)) (sub_ne_zero.mpr (Ne.symm hv))), ?_⟩
      filter_upwards [he] with z hz
      simp only [if_neg (show ¬(u = c ∧ v = c) from fun h ↦ hu h.1), zero_div, zero_add, hz]

/-- At any genuine xi node, the full mixed channels have the same polar
coefficient. It survives exactly for the reflected pairing of the two
denominator nodes. This keeps the orientation needed by the Weil form. -/
theorem exists_suzukiXiCarrier_mixed_polar_models
    (rho sigma tau : NontrivialZetaZero) :
    let L : ℂ := if starRingEnd ℂ (zetaSpectralCoordinate rho.1) =
        zetaSpectralCoordinate tau.1 ∧
        zetaSpectralCoordinate sigma.1 = zetaSpectralCoordinate tau.1 then
      (analyticZetaZeroMultiplicity tau : ℂ)⁻¹ else 0
    ∃ p q : ℂ → ℂ,
      AnalyticAt ℂ p (zetaSpectralCoordinate tau.1) ∧
      AnalyticAt ℂ q (zetaSpectralCoordinate tau.1) ∧
      ∀ᶠ z in 𝓝[≠] zetaSpectralCoordinate tau.1,
        suzukiXiZeroCarrier z /
            ((z - starRingEnd ℂ (zetaSpectralCoordinate rho.1)) *
              (z - zetaSpectralCoordinate sigma.1)) =
          L / (z - zetaSpectralCoordinate tau.1) + p z ∧
        suzukiXiSharpCarrier z /
            ((z - starRingEnd ℂ (zetaSpectralCoordinate rho.1)) *
              (z - zetaSpectralCoordinate sigma.1)) =
          L / (z - zetaSpectralCoordinate tau.1) + q z := by
  obtain ⟨f, g, hf, hg, hf0, hg0, he⟩ := exists_suzukiXiCarrier_pair_local_model tau
  have heF : suzukiXiZeroCarrier =ᶠ[𝓝[≠] zetaSpectralCoordinate tau.1]
      fun z ↦ (z - zetaSpectralCoordinate tau.1) * f z := he.mono fun _ h ↦ h.2.2.1
  have heG : suzukiXiSharpCarrier =ᶠ[𝓝[≠] zetaSpectralCoordinate tau.1]
      fun z ↦ (z - zetaSpectralCoordinate tau.1) * g z := he.mono fun _ h ↦ h.2.2.2
  obtain ⟨p, hp, hpe⟩ := local_two_resolvent_polar_model hf heF
    (starRingEnd ℂ (zetaSpectralCoordinate rho.1)) (zetaSpectralCoordinate sigma.1)
  obtain ⟨q, hq, hqe⟩ := local_two_resolvent_polar_model hg heG
    (starRingEnd ℂ (zetaSpectralCoordinate rho.1)) (zetaSpectralCoordinate sigma.1)
  rw [hf0] at hpe
  rw [hg0] at hqe
  exact ⟨p, q, hp, hq, hpe.and hqe⟩

/-- The coupled meromorphic form of one complete carrier Gram entry. -/
def suzukiXiCarrierGramContinuation (rho sigma : NontrivialZetaZero) (z : ℂ) : ℂ :=
  (suzukiXiZeroCarrier z - suzukiXiSharpCarrier z) /
    (2 * I * ((z - starRingEnd ℂ (zetaSpectralCoordinate rho.1)) *
      (z - zetaSpectralCoordinate sigma.1)))

/-- Away from its explicitly named denominator zeros, the mixed carrier
continuation is analytic. Together with xi-node removal, this isolates the
remaining possible poles in the two de Branges denominators. -/
theorem analyticAt_suzukiXiCarrierGramContinuation
    (rho sigma : NontrivialZetaZero) {z : ℂ}
    (hE : suzukiXiEValue z ≠ 0) (hEs : suzukiXiESharpValue z ≠ 0)
    (hrho : z ≠ starRingEnd ℂ (zetaSpectralCoordinate rho.1))
    (hsigma : z ≠ zetaSpectralCoordinate sigma.1) :
    AnalyticAt ℂ (suzukiXiCarrierGramContinuation rho sigma) z := by
  have hA := analyticAt_riemannXiSpectral z
  have hEA : AnalyticAt ℂ suzukiXiEValue z := by
    exact hA.add (analyticAt_const.mul hA.deriv)
  have hEsA : AnalyticAt ℂ suzukiXiESharpValue z := by
    exact hA.sub (analyticAt_const.mul hA.deriv)
  have hC : AnalyticAt ℂ suzukiXiZeroCarrier z := by
    unfold suzukiXiZeroCarrier suzukiXiThetaValue
    exact (analyticAt_const.mul (analyticAt_const.add (hEsA.div hEA hE))).div_const
  have hCs : AnalyticAt ℂ suzukiXiSharpCarrier z := by
    have hmodel : AnalyticAt ℂ
        (fun w ↦ -I * riemannXiSpectral w / suzukiXiESharpValue w) z :=
      (analyticAt_const.mul hA).div hEsA hEs
    apply hmodel.congr
    filter_upwards [hEsA.continuousAt.eventually_ne hEs] with w hw
    exact (suzukiXiSharpCarrier_eq_neg_i_mul_xi_div_sharp hw).symm
  unfold suzukiXiCarrierGramContinuation
  exact (hC.sub hCs).div
    (analyticAt_const.mul
      ((analyticAt_id.sub analyticAt_const).mul (analyticAt_id.sub analyticAt_const)))
    (mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero)
      (mul_ne_zero (sub_ne_zero.mpr hrho) (sub_ne_zero.mpr hsigma)))

/-- Every xi-divisor singularity of every mixed signed Gram entry is
removable. The theorem covers the full genuine divisor unconditionally. -/
theorem exists_suzukiXiCarrierGramContinuation_regularization
    (rho sigma tau : NontrivialZetaZero) :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F (zetaSpectralCoordinate tau.1) ∧
      suzukiXiCarrierGramContinuation rho sigma =ᶠ[
        𝓝[≠] zetaSpectralCoordinate tau.1] F := by
  obtain ⟨p, q, hp, hq, he⟩ := exists_suzukiXiCarrier_mixed_polar_models rho sigma tau
  refine ⟨fun z ↦ (p z - q z) / (2 * I),
    (hp.sub hq).div_const, ?_⟩
  filter_upwards [he] with z hz
  unfold suzukiXiCarrierGramContinuation
  rw [mul_comm (2 * I), ← div_div, sub_div, hz.1, hz.2]
  ring

/-- The existing genuine boundary Gram is the real-axis integral of this
coupled continuation. No denominator exceptional values are discarded
pointwise, and no contour deformation is used. -/
theorem suzukiXiBoundaryCarrierGramKernel_eq_continuation_integral
    (rho sigma : NontrivialZetaZero) :
    suzukiXiBoundaryCarrierGramKernel rho sigma =
      ∫ x : ℝ, suzukiXiCarrierGramContinuation rho sigma (x : ℂ) := by
  rw [suzukiXiBoundaryCarrierGramKernel_eq_signed_integral]
  apply integral_congr_ae
  exact Eventually.of_forall fun x ↦ by
    simp only [suzukiXiCarrierGramContinuation, suzukiXiSharpCarrier_ofReal,
      suzukiRealAxisXiZeroCarrier]

/-- The real-axis restriction of the coupled continuation is genuinely
integrable for every pair of xi nodes. -/
theorem integrable_suzukiXiCarrierGramContinuation_ofReal
    (rho sigma : NontrivialZetaZero) :
    Integrable (fun x : ℝ ↦ suzukiXiCarrierGramContinuation rho sigma (x : ℂ)) := by
  apply (integrable_suzukiXiBoundaryCarrier_signed_integrand rho sigma).congr
  exact Eventually.of_forall fun x ↦ by
    simp only [suzukiXiCarrierGramContinuation, suzukiXiSharpCarrier_ofReal,
      suzukiRealAxisXiZeroCarrier]

private theorem eventually_circleIntegral_polar_model
    {f F : ℂ → ℂ} {c L : ℂ} (hF : AnalyticAt ℂ F c)
    (he : f =ᶠ[𝓝[≠] c] fun z ↦ L / (z - c) + F z) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, CircleIntegrable f c r ∧
      (∮ z in C(c, r), f z) = (2 * Real.pi * I) * L := by
  change ∀ᶠ z in 𝓝[≠] c, f z = L / (z - c) + F z at he
  rw [eventually_nhdsWithin_iff] at he
  obtain ⟨R, hR, heR⟩ := Metric.eventually_nhds_iff.mp he
  obtain ⟨D, hD, hFD⟩ := hF.exists_ball_analyticOnNhd
  filter_upwards [Ioo_mem_nhdsGT (lt_min hR hD)] with r hr
  have hsphere : ∀ z ∈ sphere c r, z ≠ c ∧ z ∈ ball c R ∧ z ∈ ball c D := by
    intro z hz
    have hd : dist z c = r := mem_sphere.mp hz
    refine ⟨?_, ?_, ?_⟩
    · intro heq
      rw [heq, dist_self] at hd
      linarith [hr.1]
    · exact mem_ball.mpr (hd.trans_lt (lt_of_lt_of_le hr.2 (min_le_left _ _)))
    · exact mem_ball.mpr (hd.trans_lt (lt_of_lt_of_le hr.2 (min_le_right _ _)))
  have heq : EqOn f (fun z ↦ L / (z - c) + F z) (sphere c r) := by
    intro z hz
    exact heR ((hsphere z hz).2.1) (hsphere z hz).1
  have hpc : ContinuousOn (fun z : ℂ ↦ L / (z - c)) (sphere c r) :=
    continuousOn_const.div (continuous_id.sub continuous_const).continuousOn
      (fun z hz ↦ sub_ne_zero.mpr (hsphere z hz).1)
  have hpi := hpc.circleIntegrable hr.1.le
  have hfi := (hFD.continuousOn.mono (fun z hz ↦ (hsphere z hz).2.2)).circleIntegrable hr.1.le
  have hclosed : closedBall c r ⊆ ball c D := by
    intro z hz
    exact mem_ball.mpr ((mem_closedBall.mp hz).trans_lt
      (lt_of_lt_of_le hr.2 (min_le_right _ _)))
  have hdc : DiffContOnCl ℂ F (ball c r) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball c hr.1.ne']
    exact hFD.differentiableOn.mono hclosed
  refine ⟨?_, ?_⟩
  · apply (circleIntegrable_congr ?_).mpr (hpi.add hfi)
    intro z hz
    change f z = L / (z - c) + F z
    exact heq (by simpa only [abs_of_pos hr.1] using hz)
  · rw [circleIntegral.integral_congr hr.1.le heq,
      circleIntegral.integral_add hpi hfi, hdc.circleIntegral_eq_zero hr.1.le, add_zero]
    simp only [div_eq_mul_inv]
    rw [circleIntegral.integral_const_mul, circleIntegral.integral_sub_center_inv c hr.1.ne']
    ring

/-- Every sufficiently small circle sees the exact reflected-pair residue
in each separated channel, with genuine circle integrability proved. -/
theorem eventually_suzukiXiCarrier_mixed_circle_residues
    (rho sigma tau : NontrivialZetaZero) :
    let L : ℂ := if starRingEnd ℂ (zetaSpectralCoordinate rho.1) =
        zetaSpectralCoordinate tau.1 ∧
        zetaSpectralCoordinate sigma.1 = zetaSpectralCoordinate tau.1 then
      (analyticZetaZeroMultiplicity tau : ℂ)⁻¹ else 0
    ∀ᶠ r : ℝ in 𝓝[>] 0,
      CircleIntegrable (fun z ↦ suzukiXiZeroCarrier z /
        ((z - starRingEnd ℂ (zetaSpectralCoordinate rho.1)) *
          (z - zetaSpectralCoordinate sigma.1))) (zetaSpectralCoordinate tau.1) r ∧
      CircleIntegrable (fun z ↦ suzukiXiSharpCarrier z /
        ((z - starRingEnd ℂ (zetaSpectralCoordinate rho.1)) *
          (z - zetaSpectralCoordinate sigma.1))) (zetaSpectralCoordinate tau.1) r ∧
      (∮ z in C(zetaSpectralCoordinate tau.1, r), suzukiXiZeroCarrier z /
        ((z - starRingEnd ℂ (zetaSpectralCoordinate rho.1)) *
          (z - zetaSpectralCoordinate sigma.1))) = (2 * Real.pi * I) * L ∧
      (∮ z in C(zetaSpectralCoordinate tau.1, r), suzukiXiSharpCarrier z /
        ((z - starRingEnd ℂ (zetaSpectralCoordinate rho.1)) *
          (z - zetaSpectralCoordinate sigma.1))) = (2 * Real.pi * I) * L := by
  obtain ⟨p, q, hp, hq, he⟩ := exists_suzukiXiCarrier_mixed_polar_models rho sigma tau
  have hpole := eventually_circleIntegral_polar_model hp (he.mono fun _ h ↦ h.1)
  have hqpole := eventually_circleIntegral_polar_model hq (he.mono fun _ h ↦ h.2)
  filter_upwards [hpole, hqpole] with r hpr hqr
  exact ⟨hpr.1, hqr.1, hpr.2, hqr.2⟩

/-- Xi-node punctures contribute exactly zero to the complete signed Gram
contour on every sufficiently small circle, not merely in its limit. -/
theorem eventually_suzukiXiCarrierGram_circle_eq_zero
    (rho sigma tau : NontrivialZetaZero) :
    ∀ᶠ r : ℝ in 𝓝[>] 0,
      CircleIntegrable (suzukiXiCarrierGramContinuation rho sigma)
        (zetaSpectralCoordinate tau.1) r ∧
      (∮ z in C(zetaSpectralCoordinate tau.1, r),
        suzukiXiCarrierGramContinuation rho sigma z) = 0 := by
  obtain ⟨F, hF, he⟩ := exists_suzukiXiCarrierGramContinuation_regularization rho sigma tau
  have he' : suzukiXiCarrierGramContinuation rho sigma =ᶠ[
      𝓝[≠] zetaSpectralCoordinate tau.1]
      (fun z ↦ (0 : ℂ) / (z - zetaSpectralCoordinate tau.1) + F z) := by simpa using he
  simpa using eventually_circleIntegral_polar_model hF he'

end
end RiemannGaussian
