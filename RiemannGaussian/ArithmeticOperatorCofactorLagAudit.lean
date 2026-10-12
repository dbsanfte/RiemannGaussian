/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorCrtLagAudit
import RiemannGaussian.ArithmeticOperatorGammaPatternAudit
import Mathlib.NumberTheory.LSeries.Deriv

/-!
# Actual second-cofactor phases over fixed complete lag periods

The second prime-power leg and its literal quotient have the same height.
At the unique compatible lag they give the phase of the lifted integer,
not the phase of the original row. For a fixed finite collection of
positive second denominators, this discrepancy has an absolutely
convergent Dirichlet series on `Re(s)>0`. Thus it cannot change any actual
zero residue of the first twist commutator. Native cutoffs and all proper
powers in the chosen finite set are kept.

This freezes a FIXED finite, complete-lag, cofactor-phase-only rescue.
It does not estimate the remaining signed commutator or handle growing
moduli, incomplete lags or nonseparable restrictions on both columns.
-/

namespace RiemannGaussian.ArithmeticOperatorCofactorLagAudit
noncomputable section
open Complex Filter
open ArithmeticOperatorKummerCutoff ArithmeticOperatorGammaTwistAudit
open ArithmeticOperatorCrtLagAudit SuzukiCarryCorrelation
open scoped BigOperators Topology

/-- The literal next multiple selected by the complete additive lag period. -/
def lifted (e n : ℕ) : ℕ := n+(-(n : ZMod e)).val

theorem lifted_dvd {e : ℕ} [NeZero e] (n : ℕ) : e ∣ lifted e n := by
  exact (lag_dvd_iff n (-(n : ZMod e))).mpr rfl

theorem lifted_le {e : ℕ} [NeZero e] (n : ℕ) : lifted e n ≤ n+e := by
  exact Nat.add_le_add_left (ZMod.val_lt (-(n : ZMod e))).le n

/-- Exact actual cofactor phase, including the quotient convention and
the zero lag. No continuous row or complete original-row period is used. -/
theorem lag_cofactor_phase {e : ℕ} [NeZero e] {n : ℕ} (hn : 0<n) (b : ℝ) :
    (∑ h : ZMod e, if e ∣ n+h.val then
      primePhase b e*primePhase b ((n+h.val)/e) else 0)=
        primePhase b (lifted e n) := by
  classical
  simp_rw [lag_dvd_iff]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  have he : 0<e := Nat.pos_of_ne_zero (NeZero.ne e)
  have hq : 0<lifted e n/e := by
    have hd := Nat.mul_div_cancel' (lifted_dvd (e := e) n)
    have hpos : 0<lifted e n := by unfold lifted; omega
    nlinarith
  change primePhase b e*primePhase b (lifted e n/e)=primePhase b (lifted e n)
  rw [←primePhase_mul b he hq,Nat.mul_div_cancel' (lifted_dvd (e := e) n)]

/-- Every second-column prime power in the finite set is retained. -/
def partner (E : Finset ℕ) (b : ℝ) (n : ℕ) : ℂ :=
  ∑ e∈E,(ArithmeticFunction.vonMangoldt e : ℂ)*primePhase b (lifted e n)

/-- Actual total Mangoldt mass of the fixed second-column set. -/
def partnerMass (E : Finset ℕ) : ℝ := ∑ e∈E,ArithmeticFunction.vonMangoldt e

/-- Literal denominator-weighted mass, appearing only in the phase error. -/
def partnerFirstMoment (E : Finset ℕ) : ℝ :=
  ∑ e∈E,ArithmeticFunction.vonMangoldt e*(e : ℝ)

/-- The native first-column commutator and the lifted second cofactor
remain joined before any estimate. -/
def row (E : Finset ℕ) (y b : ℝ) (n : ℕ) : ℂ :=
  twistCommutator (primePhase y) n*partner E b n

/-- The old first commutator with its exact whole-label second height. -/
def reference (E : Finset ℕ) (y b : ℝ) (n : ℕ) : ℂ :=
  (partnerMass E : ℂ)*primePhase b n*twistCommutator (primePhase y) n

/-- Exact lifted-phase discrepancy, rather than an independently paid main. -/
def error (E : Finset ℕ) (y b : ℝ) (n : ℕ) : ℂ := row E y b n-reference E y b n

theorem norm_primeLeg_le (y : ℝ) (n : ℕ) :
    ‖primeLegDivisor (primePhase y) n‖≤Real.log n := by
  calc
    _ ≤ ∑ d∈n.divisors,‖(ArithmeticFunction.vonMangoldt d : ℂ)*primePhase y d‖ :=
      norm_sum_le _ _
    _ = Real.log n := by
      simp only [norm_mul,norm_primePhase,mul_one,Complex.norm_real,
        Real.norm_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := _))]
      exact ArithmeticFunction.vonMangoldt_sum

theorem norm_commutator_le (y : ℝ) {n : ℕ} (hn : 0<n) :
    ‖twistCommutator (primePhase y) n‖≤2*Real.log n := by
  rw [←primeLegDivisor_sub_coupled]
  calc
    _ ≤ ‖primeLegDivisor (primePhase y) n‖+‖coupledDivisor (primePhase y) n‖ :=
      norm_sub_le _ _
    _ ≤ Real.log n+Real.log n := by
      apply add_le_add (norm_primeLeg_le y n)
      rw [coupledDivisor_primePhase y hn,norm_mul,norm_primePhase,one_mul,
        Complex.norm_real,Real.norm_of_nonneg (Real.log_natCast_nonneg n)]
    _ = _ := by ring

/-- An estimate for the exact lifted phase only, not the unpaid prime sum. -/
theorem norm_lifted_phase_sub_le {e : ℕ} [NeZero e] {n : ℕ} (hn : 0<n) (b : ℝ) :
    ‖primePhase b (lifted e n)-primePhase b n‖≤|b| *(e : ℝ)/(n : ℝ) := by
  have h := ArithmeticOperatorGammaPatternAudit.norm_phase_shift_le
    (h := (-(n : ZMod e)).val) b hn
  exact h.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (by exact_mod_cast (ZMod.val_lt (-(n : ZMod e))).le)
      (abs_nonneg b)) (Nat.cast_nonneg n))

theorem partner_sub_reference (E : Finset ℕ) (b : ℝ) (n : ℕ) :
    partner E b n-(partnerMass E : ℂ)*primePhase b n=
      ∑ e∈E,(ArithmeticFunction.vonMangoldt e : ℂ)*
        (primePhase b (lifted e n)-primePhase b n) := by
  simp only [partner,partnerMass,Complex.ofReal_sum,Finset.sum_mul,mul_sub,
    Finset.sum_sub_distrib]

theorem norm_partner_sub_le (E : Finset ℕ) (hE : ∀ e∈E,0<e)
    (b : ℝ) {n : ℕ} (hn : 0<n) :
    ‖partner E b n-(partnerMass E : ℂ)*primePhase b n‖≤
      |b| *partnerFirstMoment E/(n : ℝ) := by
  rw [partner_sub_reference]
  calc
    _ ≤ ∑ e∈E,‖(ArithmeticFunction.vonMangoldt e : ℂ)*
        (primePhase b (lifted e n)-primePhase b n)‖ := norm_sum_le _ _
    _ ≤ ∑ e∈E,ArithmeticFunction.vonMangoldt e*(|b| *(e : ℝ)/(n : ℝ)) := by
      apply Finset.sum_le_sum
      intro e he
      let : NeZero e := ⟨(hE e he).ne'⟩
      rw [norm_mul,Complex.norm_real,
        Real.norm_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := e))]
      exact mul_le_mul_of_nonneg_left (norm_lifted_phase_sub_le hn b)
        (ArithmeticFunction.vonMangoldt_nonneg (n := e))
    _ = _ := by
      simp only [partnerFirstMoment,Finset.mul_sum,Finset.sum_div]
      apply Finset.sum_congr rfl
      intro e _
      ring

/-- The complete actual correction, with every chosen proper power,
has one extra inverse power of the row index. -/
theorem norm_error_le (E : Finset ℕ) (hE : ∀ e∈E,0<e) (y b : ℝ)
    {n : ℕ} (hn : 0<n) :
    ‖error E y b n‖≤
      (2*|b| *partnerFirstMoment E)*Real.log n/(n : ℝ) := by
  have he : error E y b n=twistCommutator (primePhase y) n*
      (partner E b n-(partnerMass E : ℂ)*primePhase b n) := by
    unfold error row reference
    ring
  rw [he,norm_mul]
  calc
    _ ≤ (2*Real.log n)*(|b| *partnerFirstMoment E/(n : ℝ)) :=
      mul_le_mul (norm_commutator_le y hn) (norm_partner_sub_le E hE b hn)
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- Signed native cutoff identity; no endpoint is extended or deleted. -/
theorem cutoff_ledger (E : Finset ℕ) (y b : ℝ) (X : ℕ) :
    (∑ n∈Finset.Icc 1 X,row E y b n)=
      (partnerMass E : ℂ)*(∑ n∈Finset.Icc 1 X,
        primePhase b n*twistCommutator (primePhase y) n)+
      ∑ n∈Finset.Icc 1 X,error E y b n := by
  have hr : (∑ n∈Finset.Icc 1 X,reference E y b n)=
      (partnerMass E : ℂ)*(∑ n∈Finset.Icc 1 X,
        primePhase b n*twistCommutator (primePhase y) n) := by
    simp only [reference,Finset.mul_sum,mul_assoc]
  simp only [error,Finset.sum_sub_distrib,hr]
  ring

private theorem rpow_div (x : ℝ) (hx : 0<x) (eps : ℝ) :
    x^eps/x=x^(eps-1) := by rw [Real.rpow_sub hx]; simp

/-- The literal lifted-phase error converges absolutely throughout the
positive half-plane, not merely on the Euler half-plane. -/
theorem error_summable (E : Finset ℕ) (hE : ∀ e∈E,0<e) (y b : ℝ)
    {s : ℂ} (hs : 0<s.re) : LSeriesSummable (error E y b) s := by
  let eps : ℝ := s.re/2
  have heps : 0<eps := by dsimp [eps]; linarith
  apply LSeriesSummable_of_le_const_mul_rpow (x := eps)
    (by dsimp [eps]; linarith)
  refine ⟨(2*|b| *partnerFirstMoment E)/eps,?_⟩
  intro n hn
  have hn0 : 0<n := Nat.pos_of_ne_zero hn
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn0
  have hC : 0≤2*|b| *partnerFirstMoment E := by
    unfold partnerFirstMoment
    positivity
  calc
    _ ≤ (2*|b| *partnerFirstMoment E)*Real.log n/(n : ℝ) := norm_error_le E hE y b hn0
    _ ≤ (2*|b| *partnerFirstMoment E)*((n : ℝ)^eps/eps)/(n : ℝ) := by
      gcongr
      exact Real.log_le_rpow_div (Nat.cast_nonneg n) heps
    _ = ((2*|b| *partnerFirstMoment E)/eps)*(n : ℝ)^(eps-1) := by
      rw [show (2*|b| *partnerFirstMoment E)*((n : ℝ)^eps/eps)/(n : ℝ)=
        ((2*|b| *partnerFirstMoment E)/eps)*((n : ℝ)^eps/(n : ℝ)) by ring,
        rpow_div _ hnR]

theorem error_abscissa_le_zero (E : Finset ℕ) (hE : ∀ e∈E,0<e) (y b : ℝ) :
    LSeries.abscissaOfAbsConv (error E y b)≤0 := by
  apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 0)
  intro x hx
  exact error_summable E hE y b (by simpa using hx)

theorem error_analyticAt (E : Finset ℕ) (hE : ∀ e∈E,0<e) (y b : ℝ)
    {s : ℂ} (hs : 0<s.re) : AnalyticAt ℂ (LSeries (error E y b)) s := by
  exact LSeries_analyticOnNhd (error E y b) s
    (lt_of_le_of_lt (error_abscissa_le_zero E hE y b) (by exact_mod_cast hs))

/-- The ACTUAL continued response in the original zero coordinate.
Only the error is represented by a series outside the Euler half-plane. -/
def response (E : Finset ℕ) (y b : ℝ) (z : ℂ) : ℂ :=
  (partnerMass E : ℂ)*ArithmeticOperatorTwistSourceAudit.response y z+
    LSeries (error E y b) (z-I*(y+b))

theorem commutator_summable (y : ℝ) {s : ℂ} (hs : 1<s.re) :
    LSeriesSummable (twistCommutator (primePhase y)) s := by
  let eps : ℝ := (s.re-1)/2
  have heps : 0<eps := by dsimp [eps]; linarith
  apply LSeriesSummable_of_le_const_mul_rpow (x := eps+1)
    (by dsimp [eps]; linarith)
  refine ⟨2/eps,?_⟩
  intro n hn
  have hn0 : 0<n := Nat.pos_of_ne_zero hn
  calc
    _ ≤ 2*Real.log n := norm_commutator_le y hn0
    _ ≤ 2*((n : ℝ)^eps/eps) := by
      gcongr
      exact Real.log_le_rpow_div (Nat.cast_nonneg n) heps
    _ = (2/eps)*(n : ℝ)^(eps+1-1) := by rw [show eps+1-1=eps by ring]; ring

theorem reference_summable (E : Finset ℕ) (y b : ℝ) {s : ℂ} (hs : 1<s.re) :
    LSeriesSummable (reference E y b) s := by
  have ht := (LSeriesSummable_primePhase_iff
    (twistCommutator (primePhase y)) b s).mpr
      (commutator_summable y (by simpa using hs : 1<(s+I*b).re))
  have hc := ht.smul (partnerMass E : ℂ)
  have href : reference E y b=(partnerMass E : ℂ) •
      (fun n => twistCommutator (primePhase y) n*primePhase b n) := by
    funext n
    simp only [reference,Pi.smul_apply,smul_eq_mul]
    ring
  rwa [←href] at hc

/-- Genuine Euler identity for the literal, fully cofactor-phased lag
packet; no original row or prime set is completed. -/
theorem row_euler (E : Finset ℕ) (hE : ∀ e∈E,0<e) (y b : ℝ)
    {s : ℂ} (hs : 1<s.re) :
    LSeriesHasSum (row E y b) s (response E y b (s+I*(y+b))) := by
  have hr := reference_summable E y b hs
  have he := error_summable E hE y b (by linarith : 0<s.re)
  have hcoeff : row E y b=reference E y b+error E y b := by
    funext n
    simp only [Pi.add_apply,error]
    ring
  refine LSeriesHasSum_iff.mpr ⟨hcoeff ▸ hr.add he,?_⟩
  rw [hcoeff,LSeries_add hr he]
  have href : reference E y b=(partnerMass E : ℂ) •
      (fun n => twistCommutator (primePhase y) n*primePhase b n) := by
    funext n
    simp only [reference,Pi.smul_apply,smul_eq_mul]
    ring
  rw [href,LSeries_smul,LSeries_primePhase,
    ArithmeticOperatorTwistSourceAudit.commutator_euler_response y
      (by simpa using hs : 1<(s+I*b).re)]
  unfold response ArithmeticOperatorTwistSourceAudit.response
  rw [show s+I*(y+b)-I*(y+b)=s by ring,
    show s+I*(y+b)-I*y=s+I*b by ring,
    show s+I*(y+b)=s+I*b+I*y by ring]

/-- The correction is analytic on the entire positive half-plane in
the zero coordinate, including both density points. -/
theorem response_sub_reference_analyticAt (E : Finset ℕ) (hE : ∀ e∈E,0<e)
    (y b : ℝ) {z : ℂ} (hz : 0<z.re) :
    AnalyticAt ℂ (fun z => response E y b z-
      (partnerMass E : ℂ)*ArithmeticOperatorTwistSourceAudit.response y z) z := by
  have hs : 0<(z-I*(y+b)).re := by simpa using hz
  have ha := (error_analyticAt E hE y b hs).comp
    (f := fun t : ℂ => t-I*(y+b)) (analyticAt_id.sub analyticAt_const)
  simpa only [response,add_sub_cancel_left,Function.comp_def] using ha

/-- All actual analytic multiplicities are retained. The lifted second
cofactor cannot add or cancel the old matched zero residue. -/
theorem actual_zero_source (E : Finset ℕ) (hE : ∀ e∈E,0<e)
    (rho : NontrivialZetaZero) (b : ℝ) :
    Tendsto (fun z => (z-rho.1)*response E rho.1.im b z) (𝓝[≠] rho.1)
      (𝓝 ((partnerMass E : ℂ)*(-(analyticZetaZeroMultiplicity rho : ℂ)*
        riemannZeta (rho.1.re : ℂ)))) := by
  have hs : 0<(rho.1-I*(rho.1.im+b)).re := by
    simpa using NontrivialZetaZero.zero_lt_re rho
  have ha := (error_analyticAt E hE rho.1.im b hs).comp
    (f := fun t : ℂ => t-I*(rho.1.im+b)) (analyticAt_id.sub analyticAt_const)
  have he := ha.continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[≠] rho.1≤𝓝 rho.1)
  have hz : Tendsto (fun z : ℂ => z-rho.1) (𝓝[≠] rho.1) (𝓝 0) := by
    simpa using (show Tendsto (fun z : ℂ => z-rho.1) (𝓝[≠] rho.1)
      (𝓝 (rho.1-rho.1)) from
        (continuous_id.sub continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have ht := ((ArithmeticOperatorTwistSourceAudit.tendsto_commutator_source rho).const_mul (partnerMass E : ℂ)).add (hz.mul he)
  simp only [zero_mul,add_zero] at ht
  convert ht using 1
  funext z
  unfold response
  simp only [Function.comp_def]
  ring

theorem actual_zero_source_ne_zero (E : Finset ℕ) {rho : NontrivialZetaZero}
    (hE : partnerMass E≠0) :
    (partnerMass E : ℂ)*(-(analyticZetaZeroMultiplicity rho : ℂ)*
      riemannZeta (rho.1.re : ℂ))≠0 :=
  mul_ne_zero (Complex.ofReal_ne_zero.mpr hE)
    (ArithmeticOperatorTwistSourceAudit.commutator_source_ne_zero rho)

/-- A positive ordinary-prime column is a nontrivial ACTUAL partner.
This does not delete any other proper powers in E. -/
theorem partnerMass_pos_of_prime (E : Finset ℕ) {p : ℕ} (hp : p.Prime) (hpE : p∈E) :
    0<partnerMass E := by
  have he : ArithmeticFunction.vonMangoldt p≤partnerMass E :=
    Finset.single_le_sum (fun d _ => ArithmeticFunction.vonMangoldt_nonneg (n := d)) hpE
  rw [ArithmeticFunction.vonMangoldt_apply_prime hp] at he
  exact (Real.log_pos (by exact_mod_cast hp.one_lt)).trans_le he

/-- The existing exact finite density code still removes BOTH density
channels, including the repeated channel's logarithmic companion. -/
theorem coded_density_responses (y : ℝ) {H : ℝ} (hH : 0<H) :
    (∑ i∈Finset.range 4,ArithmeticOperatorTwistSourceAudit.poleCode 1 (1+I*y) i*
      ArithmeticOperatorDilationAudit.powerResponse (1+I*y) ((2 : ℝ)^i*H))=0 ∧
    (∑ i∈Finset.range 4,ArithmeticOperatorTwistSourceAudit.poleCode 1 (1+I*y) i*
      (Real.log ((2 : ℝ)^i*H) : ℂ)*
      ArithmeticOperatorDilationAudit.powerResponse 1 ((2 : ℝ)^i*H))=0 :=
  ⟨ArithmeticOperatorTwistSourceAudit.coded_density_response hH 1 (1+I*y),
    ArithmeticOperatorTwistSourceAudit.coded_log_density_response hH 1 (1+I*y)⟩

theorem coded_source_nonzero (E : Finset ℕ) (hE : partnerMass E≠0)
    (rho : NontrivialZetaZero) {H : ℝ} (hH : 0<H) :
    ((partnerMass E : ℂ)*(-(analyticZetaZeroMultiplicity rho : ℂ)*
      riemannZeta (rho.1.re : ℂ)))*
      (∑ i∈Finset.range 4,ArithmeticOperatorTwistSourceAudit.poleCode 1 (1+I*rho.1.im) i*
        ArithmeticOperatorDilationAudit.powerResponse rho.1 ((2 : ℝ)^i*H))≠0 := by
  apply ArithmeticOperatorTwistSourceAudit.coded_source_nonzero hH
  · simp only [Complex.one_re]
    linarith [NontrivialZetaZero.re_lt_one rho]
  · simp only [Complex.add_re,Complex.one_re,Complex.mul_re,Complex.I_re,
      Complex.ofReal_re,Complex.I_im,Complex.ofReal_im,mul_zero,sub_zero,zero_mul]
    linarith [NontrivialZetaZero.re_lt_one rho]
  · exact actual_zero_source_ne_zero E hE

/-- Native cutoff correction is only polylogarithmic for fixed E. -/
theorem norm_cutoff_error_le (E : Finset ℕ) (hE : ∀ e∈E,0<e) (y b : ℝ)
    (X : ℕ) :
    ‖∑ n∈Finset.Icc 1 X,error E y b n‖≤
      2*|b| *partnerFirstMoment E*Real.log X*(1+Real.log X) := by
  calc
    _ ≤ ∑ n∈Finset.Icc 1 X,‖error E y b n‖ := norm_sum_le _ _
    _ ≤ ∑ n∈Finset.Icc 1 X,
        (2*|b| *partnerFirstMoment E*Real.log X)*(n : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      obtain ⟨hn0,hnX⟩ := Finset.mem_Icc.mp hn
      calc
        _ ≤ (2*|b| *partnerFirstMoment E)*Real.log n/(n : ℝ) := norm_error_le E hE y b hn0
        _ ≤ (2*|b| *partnerFirstMoment E)*Real.log X/(n : ℝ) := by
          apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
          apply mul_le_mul_of_nonneg_left
            (Real.log_le_log (by exact_mod_cast hn0 : (0 : ℝ)<n)
              (by exact_mod_cast hnX : (n : ℝ)≤X))
          unfold partnerFirstMoment
          positivity
        _ = _ := by ring
    _ = 2*|b| *partnerFirstMoment E*Real.log X*(harmonic X : ℝ) := by
      rw [←Finset.mul_sum,harmonic_eq_sum_Icc]
      simp only [Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
    _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log X) (by
      unfold partnerFirstMoment
      positivity)

/-- Explicit polynomial factor on the dyadic cutoffs, suitable for
checking a source rate rather than relying on an asymptotic slogan. -/
theorem norm_dyadic_error_le (E : Finset ℕ) (hE : ∀ e∈E,0<e) (y b : ℝ) (J : ℕ) :
    ‖∑ n∈Finset.Icc 1 (2^J),error E y b n‖≤
      2*|b| *partnerFirstMoment E*(1+Real.log 2)^2*((J+1 : ℕ) : ℝ)^2 := by
  have hlog : Real.log ((2^J : ℕ) : ℝ)=(J : ℝ)*Real.log 2 := by
    rw [Nat.cast_pow,Real.log_pow]
    norm_num
  have hl : 0≤Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  calc
    _ ≤ 2*|b| *partnerFirstMoment E*Real.log ((2^J : ℕ) : ℝ)*
        (1+Real.log ((2^J : ℕ) : ℝ)) := norm_cutoff_error_le E hE y b (2^J)
    _ ≤ _ := by
      rw [hlog]
      have ha : (J : ℝ)*Real.log 2≤((J+1 : ℕ) : ℝ)*(1+Real.log 2) := by
        push_cast
        nlinarith [Nat.cast_nonneg (α := ℝ) J]
      have hb : 1+(J : ℝ)*Real.log 2≤((J+1 : ℕ) : ℝ)*(1+Real.log 2) := by
        push_cast
        nlinarith [Nat.cast_nonneg (α := ℝ) J]
      have hprod := mul_le_mul ha hb (by positivity)
        (by positivity : 0≤((J+1 : ℕ) : ℝ)*(1+Real.log 2))
      have hC : 0≤2*|b| *partnerFirstMoment E := by unfold partnerFirstMoment; positivity
      have hh := mul_le_mul_of_nonneg_left hprod hC
      calc
        _ = (2*|b| *partnerFirstMoment E)*
            (((J : ℝ)*Real.log 2)*(1+(J : ℝ)*Real.log 2)) := by ring
        _ ≤ (2*|b| *partnerFirstMoment E)*
            ((((J+1 : ℕ) : ℝ)*(1+Real.log 2))*
              (((J+1 : ℕ) : ℝ)*(1+Real.log 2))) := hh
        _ = _ := by ring

/-- The complete second-cofactor correction is source-small at EVERY
positive dyadic power exponent. The first signed packet is not paid. -/
theorem tendsto_dyadic_error (E : Finset ℕ) (hE : ∀ e∈E,0<e) (y b : ℝ)
    {beta : ℝ} (hbeta : 0<beta) :
    Tendsto (fun J : ℕ => ((Real.exp (-(beta*Real.log 2)))^J : ℂ)*
      ∑ n∈Finset.Icc 1 (2^J),error E y b n) atTop (𝓝 0) := by
  let r : ℝ := Real.exp (-(beta*Real.log 2))
  have hr0 : 0≤r := (Real.exp_pos _).le
  have hr1 : r<1 := by
    dsimp [r]
    rw [Real.exp_lt_one_iff]
    have hl : 0<Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    nlinarith
  have hb := (ArithmeticOperatorFloorInverseAudit.tendsto_shifted_polynomial_geometric 2
    (Real.exp_pos _) hr1).const_mul (2*|b| *partnerFirstMoment E*(1+Real.log 2)^2)
  apply squeeze_zero_norm (fun J => ?_) (by simpa only [mul_zero] using hb)
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hr0]
  have h := mul_le_mul_of_nonneg_left (norm_dyadic_error_le E hE y b J)
    (pow_nonneg hr0 J)
  simpa only [r,mul_assoc,mul_comm,mul_left_comm] using h

/-- Source equivalence refers to the SAME signed native first packet;
it is not a claim that the packet converges or is independently bounded. -/
theorem tendsto_dyadic_sub_reference (E : Finset ℕ) (hE : ∀ e∈E,0<e) (y b : ℝ)
    {beta : ℝ} (hbeta : 0<beta) :
    Tendsto (fun J : ℕ => ((Real.exp (-(beta*Real.log 2)))^J : ℂ)*
      ((∑ n∈Finset.Icc 1 (2^J),row E y b n)-
        (partnerMass E : ℂ)*(∑ n∈Finset.Icc 1 (2^J),
          primePhase b n*twistCommutator (primePhase y) n))) atTop (𝓝 0) := by
  simpa only [cutoff_ledger,add_sub_cancel_left] using tendsto_dyadic_error E hE y b hbeta

/-- The analytic correction does not remove the ACTUAL zero divisor.
Any prospective holomorphy estimate still has to eliminate that zero. -/
theorem not_analyticAt_actual_zero (E : Finset ℕ) (hE : ∀ e∈E,0<e)
    (hM : partnerMass E≠0) (rho : NontrivialZetaZero) (b : ℝ) :
    ¬AnalyticAt ℂ (response E rho.1.im b) rho.1 := by
  intro hf
  have he := hf.continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[≠] rho.1≤𝓝 rho.1)
  have hz : Tendsto (fun z : ℂ => z-rho.1) (𝓝[≠] rho.1) (𝓝 0) := by
    simpa using (show Tendsto (fun z : ℂ => z-rho.1) (𝓝[≠] rho.1)
      (𝓝 (rho.1-rho.1)) from
        (continuous_id.sub continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have ht := hz.mul he
  simp only [zero_mul] at ht
  exact actual_zero_source_ne_zero E hM
    (tendsto_nhds_unique (actual_zero_source E hE rho b) ht)

/-- A free first column, for the collapse audit only. It is NOT claimed
to satisfy the unaltered actual Gamma observations. -/
def freePacket (E : Finset ℕ) (y b : ℝ) (X : ℕ) (w : ℕ → ℂ) : ℂ :=
  ∑ n∈Finset.Icc 1 X,ArithmeticOperatorTwistSourceAudit.defect w y n*partner E b n

/-- Full scalar profile after joining, keeping every quotient phase
and the selected compatible lag of every second denominator. -/
def joinedKernel (E : Finset ℕ) (y b : ℝ) (X d : ℕ) : ℂ :=
  ∑ n∈Finset.Icc 1 X,if d∣n then
    primePhase y d*(1-primePhase y (n/d))*partner E b n else 0

private theorem defect_finite (w : ℕ → ℂ) (y : ℝ) {n X : ℕ}
    (hn : 0<n) (hnX : n≤X) :
    ArithmeticOperatorTwistSourceAudit.defect w y n=
      ∑ d∈Finset.Icc 1 X,if d∣n then w d*primePhase y d*
        (1-primePhase y (n/d)) else 0 := by
  have he : (Finset.Icc 1 X).filter (fun d => d∣n)=n.divisors := by
    ext d
    simp only [Finset.mem_filter,Finset.mem_Icc,Nat.mem_divisors]
    constructor
    · rintro ⟨_,hd⟩
      exact ⟨hd,hn.ne'⟩
    · rintro ⟨hd,_⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd hn,(Nat.le_of_dvd hn hd).trans hnX⟩,hd⟩
  unfold ArithmeticOperatorTwistSourceAudit.defect
    ArithmeticOperatorCommutatorAudit.divisorConvolution
  rw [Nat.sum_divisorsAntidiagonal (fun d a => w d*primePhase y d*(1-primePhase y a)),
    ←he,Finset.sum_filter]

/-- All bookkeeping holds for arbitrary first-column data. Neither
the actual Gamma relation nor a prime-specific signed inequality follows. -/
theorem freePacket_eq_scalar (E : Finset ℕ) (y b : ℝ) (X : ℕ) (w : ℕ → ℂ) :
    freePacket E y b X w=∑ d∈Finset.Icc 1 X,w d*joinedKernel E y b X d := by
  unfold freePacket
  simp_rw [joinedKernel,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  rw [defect_finite w y (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : d∣n <;> simp [hd,mul_assoc]

theorem freePacket_actual (E : Finset ℕ) (y b : ℝ) (X : ℕ) :
    freePacket E y b X (fun d => (ArithmeticFunction.vonMangoldt d : ℂ))=
      ∑ n∈Finset.Icc 1 X,row E y b n := by
  simp only [freePacket,ArithmeticOperatorTwistSourceAudit.defect_eq_commutator,row]

/-- A bound supplied only by these free bookkeeping identities must
kill the whole joined kernel. This is not an actual-prime impossibility. -/
theorem bound_forall_free_columns_iff (E : Finset ℕ) (y b : ℝ) (X : ℕ) (B : ℝ) :
    (∀ w,‖freePacket E y b X w‖≤B) ↔
      0≤B ∧ ∀ d∈Finset.Icc 1 X,joinedKernel E y b X d=0 := by
  simp_rw [freePacket_eq_scalar]
  exact ArithmeticOperatorGramAudit.scalar_bound_forall_weights_iff _ _ _

end
end RiemannGaussian.ArithmeticOperatorCofactorLagAudit
