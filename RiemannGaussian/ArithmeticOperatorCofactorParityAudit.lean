/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorTwistSourceAudit
import RiemannGaussian.ArithmeticOperatorFullRamanujanAudit
import RiemannGaussian.ZetaFiniteDirichlet
import RiemannGaussian.ZetaSignedPoleControl

/-!
# Cofactor parity can retain the zero source, but its cutoff is scalar

The code is on the ordinary-integer COFACTOR, not on the Mangoldt leg.
Its two dyadic factors cancel both density residues while retaining every
actual matched zero with its multiplicity. Unlike a nonprincipal code on
the prime leg, no common nonprincipal L-zero is needed here.

The entire literal finite convolution still joins to one complex kernel
against arbitrary denominator weights. Thus this source-preserving code
is NOT an independent signed prime estimate. All proper powers, phases,
cutoffs and divisor fibers are retained in the audit.
-/

namespace RiemannGaussian.ArithmeticOperatorCofactorParityAudit
noncomputable section
open Complex Filter ArithmeticOperatorCommutatorAudit
open ArithmeticOperatorDilationAudit ArithmeticOperatorGammaTwistAudit
open ArithmeticOperatorKummerCutoff ArithmeticOperatorTwistSourceAudit
open scoped BigOperators Topology LSeries.notation

/-- The ordinary density exponent in the cofactor coordinate. -/
def densityCoordinate (y : ℝ) : ℂ := 1-I*y

/-- Exact dyadic factor, with its full complex height phase. -/
def centeredFactor (p s : ℂ) : ℂ := 1-Complex.exp ((p-s)*(Real.log 2 : ℂ))

/-- Native finite convolution code: its support is the integer set 1,2,4. -/
def coefficient (y : ℝ) (d : ℕ) : ℂ :=
  if d = 1 then 1 else if d = 2 then -(2+Complex.exp (densityCoordinate y*(Real.log 2 : ℂ)))
    else if d = 4 then 2*Complex.exp (densityCoordinate y*(Real.log 2 : ℂ)) else 0

/-- Zero-mean period-four cofactor row, with the zero endpoint fixed by
the ordinary divisor convention. -/
def cofactor (y : ℝ) : ℕ → ℂ :=
  zetaFiniteCoefficient {1,2,4} (coefficient y) ⍟ (1 : ℕ → ℂ)

/-- Exact literal operator for ANY integer denominator measure. -/
def packet (w : ℕ → ℂ) (y : ℝ) (X : ℕ) : ℂ :=
  cutoffConvolution (fun d => w d*SuzukiCarryCorrelation.primePhase y d) (cofactor y) X

/-- No quotient fiber, phase or endpoint is dropped from this kernel. -/
def kernel (y : ℝ) (X d : ℕ) : ℂ :=
  SuzukiCarryCorrelation.primePhase y d*prefixSum (cofactor y) (X/d)

/-- Entire dyadic multiplier of the genuine cofactor Dirichlet series. -/
def multiplier (y : ℝ) (s : ℂ) : ℂ :=
  centeredFactor 1 s*centeredFactor (densityCoordinate y) s

/-- Cofactor continuation. The filled value at s=1 is not used as a
limit; density cancellation below is proved on the punctured domain. -/
def cofactorResponse (y : ℝ) (s : ℂ) : ℂ := multiplier y s*riemannZeta s

/-- Original zeta coordinate; only the cofactor is shifted by -i*y. -/
def response (y : ℝ) (z : ℂ) : ℂ :=
  cofactorResponse y (z-I*y)*(-logDeriv riemannZeta z)

/-- First gate: the complete finite join holds for arbitrary arrays,
including every literal phase and every actual Mangoldt proper power. -/
theorem packet_eq_scalar (w : ℕ → ℂ) (y : ℝ) (X : ℕ) :
    packet w y X = ∑ d ∈ Finset.Icc 1 X, w d*kernel y X d := by
  rw [packet, cutoffConvolution_eq_quotient]
  exact Finset.sum_congr rfl (fun _ _ => by unfold kernel; ring)

theorem cofactor_eq_divisorObservation (y : ℝ) (n : ℕ) :
    cofactor y n = divisorObservation (zetaFiniteCoefficient {1,2,4} (coefficient y)) n := by
  rw [cofactor, LSeries.convolution_def]
  simp only [Pi.one_apply, mul_one]
  rw [Nat.sum_divisorsAntidiagonal (fun d _ =>
    zetaFiniteCoefficient {1,2,4} (coefficient y) d)]
  rfl

theorem cofactor_one (y : ℝ) : cofactor y 1 = 1 := by
  rw [cofactor_eq_divisorObservation]
  simp [divisorObservation, zetaFiniteCoefficient, coefficient]

private theorem feature_four (s : ℂ) : zetaPrimeFeature s 4 = (zetaPrimeFeature s 2)^2 := by
  simpa using zetaPrimeFeature_prime_pow s 2 2

private theorem centeredFactor_eq (p s : ℂ) :
    centeredFactor p s = 1-Complex.exp (p*(Real.log 2 : ℂ))*zetaPrimeFeature s 2 := by
  simp only [centeredFactor, zetaPrimeFeature, Complex.ofNat_log, Complex.natCast_log,
    sub_mul, Complex.exp_sub, Complex.exp_neg, div_eq_mul_inv]
  norm_num

/-- The exact finite polynomial, including its unit-modulus term. -/
theorem finite_symbol_eq_multiplier (y : ℝ) (s : ℂ) :
    zetaFiniteDirichletSeries {1,2,4} (coefficient y) s = multiplier y s := by
  classical
  unfold zetaFiniteDirichletSeries
  norm_num [Finset.sum_insert, Finset.sum_singleton, coefficient]
  rw [feature_four]
  have he : zetaPrimeFeature s 1 = 1 := by simp [zetaPrimeFeature]
  have ht : Complex.exp ((1 : ℂ)*(Real.log 2 : ℂ)) = 2 := by
    rw [one_mul, ← Complex.ofReal_exp, Real.exp_log (by norm_num : 0 < (2 : ℝ))]
    norm_num
  simp only [he]
  rw [multiplier, centeredFactor_eq, centeredFactor_eq, ht]
  simp only [Complex.ofNat_log]
  ring

/-- The cofactor Euler value has actual absolute convergence. -/
theorem cofactor_hasSum (y : ℝ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (cofactor y) s (cofactorResponse y s) := by
  have hh := (LSeriesHasSum_zetaFiniteCoefficient {1,2,4} (coefficient y) (by simp) s).convolution
    (LSeriesHasSum_one hs)
  rw [finite_symbol_eq_multiplier] at hh
  exact hh

/-- Actual Mangoldt specialization on the genuine Euler half-plane. -/
theorem packet_euler_response (y : ℝ) {s : ℂ} (hs : 1 < s.re) :
    LSeries (divisorConvolution
      (fun d => (ArithmeticFunction.vonMangoldt d : ℂ)*SuzukiCarryCorrelation.primePhase y d)
      (cofactor y)) s = response y (s+I*y) := by
  have ht : 1 < (s+I*y).re := by simpa using hs
  have hm := (LSeriesSummable_primePhase_iff
    (fun d => (ArithmeticFunction.vonMangoldt d : ℂ)) y s).mpr
    (ArithmeticFunction.LSeriesSummable_vonMangoldt ht)
  have heq : divisorConvolution
      (fun d => (ArithmeticFunction.vonMangoldt d : ℂ)*SuzukiCarryCorrelation.primePhase y d)
      (cofactor y) =
      (fun d => (ArithmeticFunction.vonMangoldt d : ℂ)*SuzukiCarryCorrelation.primePhase y d)
        ⍟ cofactor y := by
    rw [LSeries.convolution_def]
    rfl
  rw [heq]
  rw [LSeries_convolution' hm (cofactor_hasSum y hs).LSeriesSummable,
    LSeries_primePhase, ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div ht,
    (cofactor_hasSum y hs).LSeries_eq]
  have he : s+I*y-I*y = s := by ring
  simp only [response, he, logDeriv_apply, neg_div]
  ring

private theorem analytic_multiplier (y : ℝ) (s : ℂ) : AnalyticAt ℂ (multiplier y) s := by
  unfold multiplier centeredFactor
  fun_prop

private theorem centeredFactor_ne_zero {p s : ℂ} (hps : p.re ≠ s.re) :
    centeredFactor p s ≠ 0 := by
  have hh : (p-s).re*(Real.log 2) ≠ 0 := mul_ne_zero (by simpa using sub_ne_zero.mpr hps)
    (Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num))
  intro he
  have hn := congrArg norm (sub_eq_zero.mp he)
  rw [Complex.norm_exp] at hn
  have hr : ((p-s)*(Real.log 2 : ℂ)).re = (p-s).re*Real.log 2 := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [hr] at hn
  have ht : Real.exp ((p-s).re*Real.log 2) = Real.exp 0 := by
    simpa only [Real.exp_zero, norm_one] using hn.symm
  exact hh (Real.exp_injective ht)

/-- No common nonprincipal L-zero is needed: the cofactor factors are
nonzero at the matched REAL exponent of every actual zeta zero. -/
theorem cofactor_source_ne_zero (rho : NontrivialZetaZero) :
    cofactorResponse rho.1.im (rho.1.re : ℂ) ≠ 0 := by
  have hbeta := NontrivialZetaZero.re_lt_one rho
  have ha : (1 : ℂ).re ≠ (rho.1.re : ℂ).re := by simp; linarith
  have hb : (densityCoordinate rho.1.im).re ≠ (rho.1.re : ℂ).re := by
    simp [densityCoordinate]; linarith
  exact mul_ne_zero (mul_ne_zero (centeredFactor_ne_zero ha) (centeredFactor_ne_zero hb))
    (real_strip_zeta_ne_zero (NontrivialZetaZero.zero_lt_re rho) hbeta)

/-- Second gate: actual matched residue, retaining analytic multiplicity. -/
theorem tendsto_matched_source (rho : NontrivialZetaZero) :
    Tendsto (fun z : ℂ => (z-rho.1)*response rho.1.im z) (𝓝[≠] rho.1)
      (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ)*
        cofactorResponse rho.1.im (rho.1.re : ℂ))) := by
  have hb : (rho.1.re : ℂ) ≠ 1 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num at hh
    linarith [NontrivialZetaZero.re_lt_one rho]
  have ha : AnalyticAt ℂ (cofactorResponse rho.1.im) (rho.1.re : ℂ) :=
    (analytic_multiplier _ _).mul (analyticOn_riemannZeta _ hb)
  have he : rho.1-I*rho.1.im = (rho.1.re : ℂ) := by apply Complex.ext <;> simp
  have hc : ContinuousAt (fun z : ℂ => cofactorResponse rho.1.im (z-I*rho.1.im)) rho.1 := by
    rw [← he] at ha
    exact ContinuousAt.comp' (f := fun z : ℂ => z-I*rho.1.im)
      (g := cofactorResponse rho.1.im) (x := rho.1) ha.continuousAt
      (continuous_id.sub continuous_const).continuousAt
  have ht := (ArithmeticOperatorFullRamanujanAudit.tendsto_restored_zero_source rho).mul
    (hc.tendsto.mono_left nhdsWithin_le_nhds)
  rw [he] at ht
  convert ht using 1
  funext z
  unfold response
  ring

theorem matched_source_ne_zero (rho : NontrivialZetaZero) :
    -(analyticZetaZeroMultiplicity rho : ℂ)*cofactorResponse rho.1.im (rho.1.re : ℂ) ≠ 0 :=
  mul_ne_zero (ArithmeticOperatorFullRamanujanAudit.restored_source_ne_zero rho)
    (cofactor_source_ne_zero rho)

private theorem tendsto_zeta_pole :
    Tendsto (fun z : ℂ => (z-1)*(-logDeriv riemannZeta z)) (𝓝[≠] 1) (𝓝 1) := by
  have ha := (differentiable_riemannZeta₁).analyticAt (1 : ℂ)
  have hne : riemannZeta₁ (1 : ℂ) ≠ 0 := by simp [riemannZeta₁_one]
  have hl : ContinuousAt (logDeriv riemannZeta₁) (1 : ℂ) :=
    ha.deriv.continuousAt.div ha.continuousAt hne
  have hs : Tendsto (fun z : ℂ => z-1) (𝓝[≠] 1) (𝓝 0) := by
    simpa using (show Continuous (fun z : ℂ => z-1) from
      continuous_id.sub continuous_const).continuousAt.tendsto.mono_left
      (show 𝓝[≠] (1 : ℂ) ≤ 𝓝 1 from nhdsWithin_le_nhds)
  have ht := (tendsto_const_nhds (x := (1 : ℂ))).sub
    (hs.mul (hl.tendsto.mono_left nhdsWithin_le_nhds))
  simp only [zero_mul, sub_zero] at ht
  apply ht.congr'
  filter_upwards [ha.continuousAt.eventually_ne hne |>.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with z hz hz1
  have h1 : z ≠ 1 := hz1
  have hzet : riemannZeta z ≠ 0 := by
    intro he
    apply hz
    rw [riemannZeta₁_eq_sub_one_mul h1, he, mul_zero]
  rw [neg_logDeriv_riemannZeta_eq_pole_sub h1 hzet]
  field_simp

theorem multiplier_density_zero (y : ℝ) : multiplier y (densityCoordinate y) = 0 := by
  simp [multiplier, centeredFactor]

theorem multiplier_integer_zero (y : ℝ) : multiplier y 1 = 0 := by
  simp [multiplier, centeredFactor]

/-- Third gate: the original zeta pole has zero residue, after joining
the exact cofactor factors. No density-pole coefficient is discarded. -/
theorem tendsto_density_pole_zero {y : ℝ} (hy : y ≠ 0) :
    Tendsto (fun z : ℂ => (z-1)*response y z) (𝓝[≠] 1) (𝓝 0) := by
  have hp : densityCoordinate y ≠ 1 := by
    intro he
    have hh := congrArg Complex.im he
    simp [densityCoordinate] at hh
    exact hy hh
  have ha : AnalyticAt ℂ (cofactorResponse y) (densityCoordinate y) :=
    (analytic_multiplier _ _).mul (analyticOn_riemannZeta _ hp)
  have hc : ContinuousAt (fun z : ℂ => cofactorResponse y (z-I*y)) 1 := by
    exact ContinuousAt.comp' (f := fun z : ℂ => z-I*y) (g := cofactorResponse y)
      (x := 1) ha.continuousAt (continuous_id.sub continuous_const).continuousAt
  have ht := tendsto_zeta_pole.mul (hc.tendsto.mono_left nhdsWithin_le_nhds)
  have hv : cofactorResponse y (1-I*y) = 0 := by
    change multiplier y (densityCoordinate y)*riemannZeta (densityCoordinate y) = 0
    rw [multiplier_density_zero, zero_mul]
  rw [hv, mul_zero] at ht
  convert ht using 1
  funext z
  unfold response
  ring

/-- The ordinary-integer cofactor's density pole is cancelled too.
This uses the true punctured zeta residue, not its arbitrary filled value. -/
theorem tendsto_integer_density_zero {y : ℝ} (hy : y ≠ 0) :
    Tendsto (fun z : ℂ => (z-(1+I*y))*response y z)
      (𝓝[≠] (1+I*y)) (𝓝 0) := by
  have hshift : Tendsto (fun z : ℂ => z-I*y) (𝓝[≠] (1+I*y)) (𝓝[≠] 1) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using (show Continuous (fun z : ℂ => z-I*y) from
        continuous_id.sub continuous_const).continuousAt.tendsto.mono_left
        (show 𝓝[≠] (1+I*(y : ℂ)) ≤ 𝓝 (1+I*y) from nhdsWithin_le_nhds)
    · filter_upwards [self_mem_nhdsWithin] with z hz
      change z-I*y ≠ 1
      intro he
      have hn : z ≠ 1+I*y := hz
      apply hn
      linear_combination he
  have hz1 : (1 : ℂ)+I*y ≠ 1 := by
    intro he
    have hh := congrArg Complex.im he
    simp at hh
    exact hy hh
  have hzeta : riemannZeta ((1 : ℂ)+I*y) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by simp)
  have hl : ContinuousAt (fun z : ℂ => -logDeriv riemannZeta z) (1+I*y) :=
    ((analyticOn_riemannZeta _ hz1).deriv.continuousAt.div
      (analyticOn_riemannZeta _ hz1).continuousAt hzeta).neg
  have hm := ((analytic_multiplier y 1).continuousAt.tendsto.mono_left
    nhdsWithin_le_nhds).comp hshift
  have ht := (hm.mul (riemannZeta_residue_one.comp hshift)).mul
    (hl.tendsto.mono_left nhdsWithin_le_nhds)
  rw [multiplier_integer_zero, zero_mul, zero_mul] at ht
  convert ht using 1
  funext z
  simp only [Function.comp_def, response, cofactorResponse]
  ring

/-- Fourth gate: the complete signed operator is still a scalar kernel.
An all-weight bound requires its whole kernel to be zero. This is not a
claim that actual integer Gamma data can be replaced by free weights. -/
theorem packet_bound_forall_weights_iff (y : ℝ) (X : ℕ) (B : ℝ) :
    (∀ w : ℕ → ℂ, ‖packet w y X‖ ≤ B) ↔
      0 ≤ B ∧ ∀ d ∈ Finset.Icc 1 X, kernel y X d = 0 := by
  simp_rw [packet_eq_scalar]
  exact ArithmeticOperatorGramAudit.scalar_bound_forall_weights_iff _ _ _

theorem kernel_at_cutoff {X : ℕ} (hX : 0 < X) (y : ℝ) :
    kernel y X X = SuzukiCarryCorrelation.primePhase y X := by
  simp [kernel, Nat.div_self hX, prefixSum, cofactor_one]

/-- Even after both poles cancel and the matched source survives,
the finite identities cannot force an independent all-weight estimate. -/
theorem no_free_weight_bound {X : ℕ} (hX : 0 < X) (y : ℝ) (B : ℝ) :
    ¬ (∀ w : ℕ → ℂ, ‖packet w y X‖ ≤ B) := by
  intro hh
  have he := (packet_bound_forall_weights_iff y X B).mp hh |>.2 X
    (by simp; omega)
  rw [kernel_at_cutoff hX] at he
  exact Complex.exp_ne_zero _ he

end
end RiemannGaussian.ArithmeticOperatorCofactorParityAudit
