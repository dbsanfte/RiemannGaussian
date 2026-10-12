/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorGammaInverseAudit
import RiemannGaussian.ArithmeticOperatorGammaHierarchyAudit

/-!
# Mixed-height inverse Gamma source and collapse gates

The inverse has a different literal multiplicative height from the
complete forward Gamma row. On the genuine Euler half-plane its response
is a shifted zeta DERIVATIVE divided by a differently shifted zeta.
At the original selected zero, a nonzero matched residue thus requires
an additional vertically translated zeta zero. No common-zero assertion
is assumed. Even when a source survives, the entire finite inverse joins
to an arbitrary-weight scalar cofactor convolution, not a new signed bound.

All integer product fibers, proper prime powers, cutoff endpoints and
both height phases remain exact. Nonlinear inverse masks and signed
cross-column arithmetic are outside this audit.
-/

namespace RiemannGaussian.ArithmeticOperatorMixedHeightInverseAudit
noncomputable section
open Complex Filter ArithmeticOperatorKummerCutoff
open ArithmeticOperatorCommutatorAudit ArithmeticOperatorDilationAudit
open ArithmeticOperatorGammaTwistAudit ArithmeticOperatorGammaInverseAudit
open SuzukiCarryCorrelation
open scoped BigOperators Topology

/-- Möbius leg at the actual inverse height. -/
def inverseLeg (z : ℝ) (n : ℕ) : ℂ :=
  (ArithmeticFunction.moebius n : ℂ)*primePhase z n

/-- Entire Gamma forward row and mixed-height inverse, without cutoff truncation. -/
def mixedDecoded (w : ℕ → ℂ) (y z : ℝ) : ℕ → ℂ :=
  divisorConvolution (inverseLeg z) (phasedRow w y)

/-- Exact cofactor left after joining the full forward/inverse product. -/
def cofactor (y z : ℝ) : ℕ → ℂ :=
  divisorConvolution (inverseLeg z) (primePhase y)

private theorem convolution_eq (f g : ℕ → ℂ) :
    divisorConvolution f g=LSeries.convolution f g := by
  rw [LSeries.convolution_def]
  rfl

private theorem convolution_comm (f g : ℕ → ℂ) :
    divisorConvolution f g=divisorConvolution g f := by
  rw [convolution_eq,convolution_eq]
  simp only [LSeries.convolution,mul_comm]

private theorem convolution_assoc (f g h : ℕ → ℂ) :
    divisorConvolution f (divisorConvolution g h)=
      divisorConvolution (divisorConvolution f g) h := by
  simp only [convolution_eq,LSeries.convolution,ArithmeticFunction.toArithmeticFunction_eq_self,
    mul_assoc]

theorem phasedRow_eq_convolution (w : ℕ → ℂ) (y : ℝ) :
    phasedRow w y=divisorConvolution (fun d => w d*primePhase y d) (primePhase y) := by
  funext n
  unfold phasedRow divisorObservation divisorConvolution
  dsimp only
  rw [Nat.sum_divisorsAntidiagonal (fun d a => (w d*primePhase y d)*primePhase y a)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdvd := Nat.dvd_of_mem_divisors hd
  have hd0 := Nat.pos_of_mem_divisors hd
  have hn : 0<n := Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd).2
  have hprod : d*(n/d)=n := Nat.mul_div_cancel' hdvd
  have hq : 0<n/d := by nlinarith
  rw [mul_assoc,←primePhase_mul y hd0 hq,hprod,mul_comm]

/-- Exact collective join at different heights. It is valid for EVERY
array, not only actual prime coefficients or a diagnostic smooth mode. -/
theorem mixedDecoded_eq_convolution (w : ℕ → ℂ) (y z : ℝ) :
    mixedDecoded w y z=
      divisorConvolution (fun d => w d*primePhase y d) (cofactor y z) := by
  unfold mixedDecoded cofactor
  rw [phasedRow_eq_convolution,convolution_assoc,convolution_comm (inverseLeg z),
    ←convolution_assoc]

/-- Full literal quotient prefix; neither height is approximated. -/
def packet (w : ℕ → ℂ) (y z : ℝ) (X : ℕ) : ℂ :=
  prefixSum (mixedDecoded w y z) X

/-- Exact scalar kernel of the mixed-height inverse at the original
integer cutoff, with its complete quotient cofactor prefix. -/
def kernel (y z : ℝ) (X d : ℕ) : ℂ :=
  primePhase y d*prefixSum (cofactor y z) (X/d)

theorem packet_eq_scalar (w : ℕ → ℂ) (y z : ℝ) (X : ℕ) :
    packet w y z X=∑ d ∈ Finset.Icc 1 X, w d*kernel y z X d := by
  rw [packet,mixedDecoded_eq_convolution]
  change cutoffConvolution _ _ X=_
  rw [cutoffConvolution_eq_quotient]
  exact Finset.sum_congr rfl (fun _ _ => by unfold kernel; ring)

theorem cofactor_one (y z : ℝ) : cofactor y z 1=1 := by
  simp [cofactor,divisorConvolution,inverseLeg,primePhase]

theorem kernel_at_endpoint {X : ℕ} (hX : 0<X) (y z : ℝ) :
    kernel y z X X=primePhase y X := by
  simp [kernel,Nat.div_self hX,prefixSum,cofactor_one]

/-- Collapse obstruction: free Gamma-array identities cannot supply
any finite all-weight allowance, at any positive literal cutoff. -/
theorem no_free_weight_bound {X : ℕ} (hX : 0<X) (y z : ℝ) (B : ℝ) :
    ¬(∀ w : ℕ → ℂ, ‖packet w y z X‖≤B) := by
  intro hh
  simp_rw [packet_eq_scalar] at hh
  have he := (ArithmeticOperatorGramAudit.scalar_bound_forall_weights_iff _ _ _).mp hh
  have hz := he.2 X (Finset.mem_Icc.mpr ⟨hX,le_rfl⟩)
  rw [kernel_at_endpoint hX] at hz
  have hn := norm_primePhase y X
  rw [hz,norm_zero] at hn
  norm_num at hn

/-- The original matched coordinate; the forward height has been absorbed
into s, leaving the literal inverse-minus-forward height difference. -/
def response (delta : ℝ) (s : ℂ) : ℂ :=
  -deriv riemannZeta s/riemannZeta (s+I*delta)

theorem inverseLeg_summable (z : ℝ) {s : ℂ} (hs : 1<s.re) :
    LSeriesSummable (inverseLeg z) s := by
  apply (LSeriesSummable_primePhase_iff _ z s).mpr
  exact ArithmeticFunction.LSeriesSummable_moebius_iff.mpr (by simpa using hs)

theorem inverseLeg_euler (z : ℝ) {s : ℂ} (hs : 1<s.re) :
    LSeries (inverseLeg z) s=(riemannZeta (s+I*z))⁻¹ := by
  change LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)*primePhase z n) s=_
  rw [LSeries_primePhase]
  have ht : 1<(s+I*z).re := by simpa using hs
  have hprod := LSeries_one_mul_Lseries_moebius ht
  rw [LSeries_one_eq_riemannZeta ht] at hprod
  exact eq_inv_of_mul_eq_one_right hprod

/-- Genuine convergent Euler response of actual mixed-height Gamma
data. No continued series is asserted to converge in the zero strip. -/
theorem actual_euler_response (y z : ℝ) {s : ℂ} (hs : 1<s.re) :
    LSeries (mixedDecoded (fun d => (ArithmeticFunction.vonMangoldt d : ℂ)) y z) s=
      response (z-y) (s+I*y) := by
  have hrow : phasedRow (fun d => (ArithmeticFunction.vonMangoldt d : ℂ)) y=
      coupledDivisor (primePhase y) := by
    funext n
    by_cases hn : n=0
    · simp [hn,phasedRow,divisorObservation,coupledDivisor]
    · rw [actual_phasedRow,coupledDivisor_primePhase y (Nat.pos_of_ne_zero hn)]
  have hsum : LSeriesSummable (coupledDivisor (primePhase y)) s := by
    rw [←hrow]
    have he : phasedRow (fun d => (ArithmeticFunction.vonMangoldt d : ℂ)) y=
        fun n : ℕ => (Real.log n : ℂ)*primePhase y n := by
      funext n
      rw [actual_phasedRow,mul_comm]
    rw [he,LSeriesSummable_primePhase_iff]
    have hh : LSeriesSummable (LSeries.logMul (1 : ℕ → ℂ)) (s+I*y) :=
      LSeriesSummable_logMul_of_lt_re (by
        rw [LSeries.abscissaOfAbsConv_one]
        exact_mod_cast (show 1<(s+I*y).re by simpa using hs))
    have hlog : LSeries.logMul (1 : ℕ → ℂ)=fun n : ℕ => (Real.log n : ℂ) := by
      funext n
      change Complex.log (n : ℂ)*1=(Real.log n : ℂ)
      rw [mul_one,←Complex.natCast_log]
    rwa [hlog] at hh
  rw [mixedDecoded,convolution_eq,hrow,
    LSeries_convolution' (inverseLeg_summable z hs) hsum,
    inverseLeg_euler z hs,coupled_series_eq_shifted_derivative hs y]
  unfold response
  push_cast
  rw [show s+I*y+I*(z-y)=s+I*z by ring]
  ring

/-- Source gate: the ordinary selected zero does NOT suffice for a mixed
inverse. If the vertically translated denominator is nonzero, its exact
matched response is zero, with all original multiplicities retained. -/
theorem tendsto_source_zero_of_no_shifted_zero (rho : NontrivialZetaZero)
    (delta : ℝ) (hshift : riemannZeta (rho.1+I*delta)≠0)
    (hpoint : rho.1+I*delta≠1) :
    Tendsto (fun s : ℂ => (s-rho.1)*response delta s)
      (𝓝[≠] rho.1) (𝓝 0) := by
  have hmap : ContinuousAt (fun s : ℂ => s+I*delta) rho.1 := by fun_prop
  have hden : ContinuousAt (fun s : ℂ => riemannZeta (s+I*delta)) rho.1 :=
    (differentiableAt_riemannZeta hpoint).continuousAt.comp (f := fun s : ℂ => s+I*delta) hmap
  have hresp : ContinuousAt (response delta) rho.1 :=
    ((analyticAt_riemannZeta_nontrivialZero rho).deriv.continuousAt.neg).div hden hshift
  have ht : Tendsto (fun s : ℂ => s-rho.1) (𝓝[≠] rho.1) (𝓝 0) := by
    have hsub : ContinuousAt (fun s : ℂ => s-rho.1) rho.1 := by fun_prop
    simpa using hsub.tendsto.mono_left nhdsWithin_le_nhds
  simpa using ht.mul (hresp.tendsto.mono_left nhdsWithin_le_nhds)

/-- Any nonzero residue from the different-height inverse requires a
genuine translated zeta zero; this is an additional source premise,
not an independent arithmetic estimate or a common-zero conjecture. -/
theorem source_forces_shifted_zero (rho : NontrivialZetaZero) (delta : ℝ)
    (hpoint : rho.1+I*delta≠1) {v : ℂ} (hv : v≠0)
    (hsource : Tendsto (fun s : ℂ => (s-rho.1)*response delta s)
      (𝓝[≠] rho.1) (𝓝 v)) : riemannZeta (rho.1+I*delta)=0 := by
  by_contra hh
  exact hv (tendsto_nhds_unique hsource
    (tendsto_source_zero_of_no_shifted_zero rho delta hh hpoint))

/-- Regression gate: the exact same-height inverse keeps the full
original multiplicity. The mixed-height obstruction is not caused by
deleting prime powers or changing the matched-source convention. -/
theorem tendsto_same_height_source (rho : NontrivialZetaZero) :
    Tendsto (fun s : ℂ => (s-rho.1)*response 0 s)
      (𝓝[≠] rho.1) (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hh := (AnalyticAt.tendsto_sub_mul_logDeriv_analyticOrderNatAt
    (analyticAt_riemannZeta_nontrivialZero rho)
    (analyticOrderAt_riemannZeta_nontrivialZero_ne_top rho)).neg
  simpa [response,logDeriv_apply,analyticZetaZeroMultiplicity,mul_neg,neg_div] using hh

/-- Finite height codes do not escape the source gate: absent translated
denominator zeros, the whole joined response has zero matched residue. -/
theorem tendsto_finite_code_source_zero (rho : NontrivialZetaZero)
    (S : Finset ℕ) (delta : ℕ → ℝ) (coeff : ℕ → ℂ)
    (hpoint : ∀ i ∈ S, rho.1+I*delta i≠1)
    (hshift : ∀ i ∈ S, riemannZeta (rho.1+I*delta i)≠0) :
    Tendsto (fun s : ℂ => (s-rho.1)*∑ i ∈ S, coeff i*response (delta i) s)
      (𝓝[≠] rho.1) (𝓝 0) := by
  have hh := tendsto_finsetSum S (fun i hi =>
    (tendsto_source_zero_of_no_shifted_zero rho (delta i) (hshift i hi)
      (hpoint i hi)).const_mul (coeff i))
  simp only [mul_zero,Finset.sum_const_zero] at hh
  convert hh using 1
  funext s
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

theorem finite_code_source_forces_shifted_zero (rho : NontrivialZetaZero)
    (S : Finset ℕ) (delta : ℕ → ℝ) (coeff : ℕ → ℂ)
    (hpoint : ∀ i ∈ S, rho.1+I*delta i≠1) {v : ℂ} (hv : v≠0)
    (hsource : Tendsto (fun s : ℂ => (s-rho.1)*∑ i ∈ S, coeff i*response (delta i) s)
      (𝓝[≠] rho.1) (𝓝 v)) :
    ∃ i ∈ S, riemannZeta (rho.1+I*delta i)=0 := by
  classical
  by_contra hh
  have hnone : ∀ i ∈ S, riemannZeta (rho.1+I*delta i)≠0 := by
    intro i hi hz
    exact hh ⟨i,hi,hz⟩
  exact hv (tendsto_nhds_unique hsource
    (tendsto_finite_code_source_zero rho S delta coeff hpoint hnone))

/-- An actual local no-go, not an arbitrary spectral model: EVERY
sufficiently small nonzero height displacement kills the original
matched residue. No exposure, simplicity or rightmost zero is assumed. -/
theorem exists_small_shift_source_zero (rho : NontrivialZetaZero)
    (hre : rho.1.re<1) :
    ∃ epsilon : ℝ, 0<epsilon ∧ ∀ delta : ℝ, 0 < |delta| → |delta| < epsilon →
      Tendsto (fun s : ℂ => (s-rho.1)*response delta s)
        (𝓝[≠] rho.1) (𝓝 0) := by
  have hne : ∀ᶠ s : ℂ in 𝓝[≠] rho.1, riemannZeta s≠0 :=
    (analyticAt_riemannZeta_nontrivialZero rho).eventually_eq_zero_or_eventually_ne_zero
      |>.resolve_left (fun hh => analyticOrderAt_riemannZeta_nontrivialZero_ne_top rho
        (analyticOrderAt_eq_top.mpr hh))
  obtain ⟨epsilon,heps,hball⟩ := Metric.mem_nhdsWithin_iff.mp hne
  refine ⟨epsilon,heps,fun delta hdelta hsmall => ?_⟩
  have hd : dist (rho.1+I*delta) rho.1=|delta| := by
    rw [dist_eq_norm,add_sub_cancel_left,norm_mul,Complex.norm_I,one_mul,
      Complex.norm_real,Real.norm_eq_abs]
  have hdiff : rho.1+I*delta≠rho.1 := by
    intro hh
    have him := congrArg Complex.im hh
    simp only [add_im,mul_im,I_re,I_im,zero_mul,one_mul,zero_add,ofReal_re] at him
    have hz : delta=0 := by linarith
    simp [hz] at hdelta
  have hz := hball ⟨by simpa only [Metric.mem_ball,hd] using hsmall,hdiff⟩
  have hp : rho.1+I*delta≠1 := by
    intro hh
    have hreal := congrArg Complex.re hh
    simp at hreal
    linarith
  exact tendsto_source_zero_of_no_shifted_zero rho delta hz hp

/-- All finite height combinations join BEFORE estimating, with the
native physical endpoint and both phases retained in each kernel. -/
theorem finite_packet_eq_scalar (S : Finset ℕ) (coeff : ℕ → ℂ)
    (y z : ℕ → ℝ) (w : ℕ → ℂ) (X : ℕ) :
    (∑ i ∈ S, coeff i*packet w (y i) (z i) X)=
      ∑ d ∈ Finset.Icc 1 X, w d*(∑ i ∈ S, coeff i*kernel (y i) (z i) X d) := by
  simp only [packet_eq_scalar,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  exact Finset.sum_congr rfl (fun _ _ => by ring)

/-- Exact arbitrary-weight collapse criterion, also for jointly centered
height codes. Pole/source separation cannot turn it into a prime-specific
signed allowance: an all-weight allowance forces the WHOLE kernel to zero. -/
theorem finite_packet_bound_forall_weights_iff (S : Finset ℕ) (coeff : ℕ → ℂ)
    (y z : ℕ → ℝ) (X : ℕ) (B : ℝ) :
    (∀ w : ℕ → ℂ, ‖∑ i ∈ S, coeff i*packet w (y i) (z i) X‖≤B) ↔
      0≤B ∧ ∀ d ∈ Finset.Icc 1 X, (∑ i ∈ S, coeff i*kernel (y i) (z i) X d)=0 := by
  simp_rw [finite_packet_eq_scalar]
  exact ArithmeticOperatorGramAudit.scalar_bound_forall_weights_iff _ _ _

end
end RiemannGaussian.ArithmeticOperatorMixedHeightInverseAudit
