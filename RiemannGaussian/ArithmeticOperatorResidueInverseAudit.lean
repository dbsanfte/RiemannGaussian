/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorRamanujanInverseAudit
import RiemannGaussian.ArithmeticOperatorMoebiusCoprimeAudit
import RiemannGaussian.ZetaMoebiusWronskian
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Fixed non-divisor residue codes before the actual Gamma inverse

The actual complete logarithmic rows and actual Mobius inverse remain
literal. Every fixed periodic code has Euler response -L_Phi'/zeta.
Its source order is exactly the numerator order minus the actual zero
multiplicity. Zero mean removes density, without assuming a common
nonprincipal L-zero. This is a source/estimation audit, not a new signed
arithmetic bound or a native cutoff asymptotic.
-/

namespace RiemannGaussian.ArithmeticOperatorResidueInverseAudit
noncomputable section
open Complex Filter
open ArithmeticOperatorIncidenceFreedom ArithmeticOperatorKummerCutoff
open ArithmeticOperatorGammaTwistAudit SuzukiCarryCorrelation
open scoped BigOperators Topology LSeries.notation

/-- The actual periodic Gamma numerator, with no character restriction. -/
def numerator {q : ℕ} [NeZero q] (Phi : ZMod q → ℂ) (s : ℂ) : ℂ :=
  -deriv (ZMod.LFunction Phi) s

/-- Genuine meromorphic continuation of the fully coded actual inverse. -/
def response {q : ℕ} [NeZero q] (Phi : ZMod q → ℂ) (s : ℂ) : ℂ :=
  numerator Phi s/riemannZeta s

private theorem row_summable {q : ℕ} [NeZero q] (Phi : ZMod q → ℂ)
    {s : ℂ} (hs : 1<s.re) :
    LSeriesSummable (ArithmeticOperatorPeriodicInverseAudit.row Phi) s := by
  let c : ℕ → ℂ := fun n => Phi n
  have hb : LSeries.abscissaOfAbsConv c≤1 := by
    apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1)
    intro x hx
    exact ZMod.LSeriesSummable_of_one_lt_re Phi (by simpa using hx)
  have hc : LSeries.abscissaOfAbsConv c<s.re := lt_of_le_of_lt hb (by exact_mod_cast hs)
  have he : ArithmeticOperatorPeriodicInverseAudit.row Phi=LSeries.logMul c := by
    funext n
    simp only [ArithmeticOperatorPeriodicInverseAudit.row,LSeries.logMul,c,
      ← Complex.natCast_log]
    ring
  rw [he]
  exact LSeriesSummable_logMul_of_lt_re hc

/-- Every inverse fiber is kept. No series is asserted below Re(s)>1. -/
theorem euler_response {q : ℕ} [NeZero q] (Phi : ZMod q → ℂ)
    {s : ℂ} (hs : 1<s.re) :
    LSeries (ArithmeticOperatorPeriodicInverseAudit.decoded Phi) s=response Phi s := by
  let mu : ℕ → ℂ := fun n => (ArithmeticFunction.moebius n : ℂ)
  have he : ArithmeticOperatorPeriodicInverseAudit.decoded Phi=
      mu ⍟ ArithmeticOperatorPeriodicInverseAudit.row Phi := by
    rw [LSeries.convolution_def]
    rfl
  have hm : LSeriesSummable mu s := ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs
  have hmu : LSeries mu s=1/riemannZeta s := by
    apply (eq_div_iff (riemannZeta_ne_zero_of_one_lt_re hs)).mpr
    have h := LSeries_one_mul_Lseries_moebius hs
    rw [LSeries_one_eq_riemannZeta hs] at h
    simpa only [mul_comm] using h
  have hr : LSeries (ArithmeticOperatorPeriodicInverseAudit.row Phi) s=numerator Phi s := by
    have hh := ArithmeticOperatorPeriodicGammaAudit.euler_response Phi 0 hs
    have hw : ArithmeticOperatorPeriodicGammaAudit.wholeRow Phi 0=
        ArithmeticOperatorPeriodicInverseAudit.row Phi := by
      funext n
      simp [ArithmeticOperatorPeriodicGammaAudit.wholeRow_eq_log,
        ArithmeticOperatorPeriodicInverseAudit.row,primePhase]
    simpa only [hw,ArithmeticOperatorPeriodicGammaAudit.response,
      ofReal_zero,mul_zero,add_zero,numerator] using hh
  rw [he,LSeries_convolution' hm (row_summable Phi hs),hmu,hr,response]
  ring

/-- Both cofactor and inverse phases stay on the original whole label. -/
theorem phased_euler_response {q : ℕ} [NeZero q] (Phi : ZMod q → ℂ)
    (y : ℝ) {s : ℂ} (hs : 1<s.re) :
    LSeries (ArithmeticOperatorPeriodicInverseAudit.phasedDecoded Phi y) s=
      response Phi (s+I*y) := by
  have he : ArithmeticOperatorPeriodicInverseAudit.phasedDecoded Phi y=
      fun n => ArithmeticOperatorPeriodicInverseAudit.decoded Phi n*primePhase y n := by
    funext n
    rw [ArithmeticOperatorPeriodicInverseAudit.phasedDecoded_eq,mul_comm]
  rw [he,LSeries_primePhase,euler_response Phi (by simpa using hs)]

theorem numerator_analytic {q : ℕ} [NeZero q] (Phi : ZMod q → ℂ)
    {s : ℂ} (hs : s≠1) : AnalyticAt ℂ (numerator Phi) s :=
  (ArithmeticOperatorPeriodicGammaAudit.analyticAt_periodicL Phi hs).deriv.neg

/-- Exact order test, including all actual multiplicities. -/
theorem response_order {q : ℕ} [NeZero q] (Phi : ZMod q → ℂ)
    (rho : NontrivialZetaZero) {ell : ℕ}
    (hell : analyticOrderAt (numerator Phi) rho.1=ell) :
    meromorphicOrderAt (response Phi) rho.1=
      ((ell : ℤ)-(analyticZetaZeroMultiplicity rho : ℤ) : ℤ) := by
  change meromorphicOrderAt (numerator Phi/riemannZeta) rho.1=_
  rw [meromorphicOrderAt_div (numerator_analytic Phi rho.2.2.2).meromorphicAt
    (analyticAt_riemannZeta_nontrivialZero rho).meromorphicAt,
    (numerator_analytic Phi rho.2.2.2).meromorphicOrderAt_eq,hell,
    meromorphicOrderAt_riemannZeta_nontrivialZero]
  simp

/-- Removability is precisely numerator cancellation of the full zero
order. An analytic extension is not inferred from totalized division. -/
theorem response_removable_iff {q : ℕ} [NeZero q] (Phi : ZMod q → ℂ)
    (rho : NontrivialZetaZero) {ell : ℕ}
    (hell : analyticOrderAt (numerator Phi) rho.1=ell) :
    (∃ E : ℂ → ℂ,AnalyticAt ℂ E rho.1 ∧ response Phi=ᶠ[𝓝[≠] rho.1] E) ↔
      analyticZetaZeroMultiplicity rho≤ell := by
  have hm : MeromorphicAt (response Phi) rho.1 :=
    (numerator_analytic Phi rho.2.2.2).meromorphicAt.div
      (analyticAt_riemannZeta_nontrivialZero rho).meromorphicAt
  rw [← hm.meromorphicOrderAt_nonneg_iff,response_order Phi rho hell]
  constructor
  · intro h
    have h' : (analyticZetaZeroMultiplicity rho : ℤ)≤ell :=
      sub_nonneg.mp (WithTop.coe_le_coe.mp h)
    exact_mod_cast h'
  · intro h
    apply WithTop.coe_le_coe.mpr
    apply sub_nonneg.mpr
    exact_mod_cast h

/-- A surviving pole has an exact nonzero leading coefficient, with
order equal to actual multiplicity minus numerator cancellation. -/
theorem actual_zero_source_of_order {q : ℕ} [NeZero q] (Phi : ZMod q → ℂ)
    (rho : NontrivialZetaZero) {ell : ℕ}
    (hell : analyticOrderAt (numerator Phi) rho.1=ell)
    (hlt : ell<analyticZetaZeroMultiplicity rho) :
    ∃ v : ℂ,v≠0 ∧ Tendsto (fun s : ℂ =>
      (s-rho.1)^(analyticZetaZeroMultiplicity rho-ell)*response Phi s)
        (𝓝[≠] rho.1) (𝓝 v) := by
  have hm : MeromorphicAt (response Phi) rho.1 :=
    (numerator_analytic Phi rho.2.2.2).meromorphicAt.div
      (analyticAt_riemannZeta_nontrivialZero rho).meromorphicAt
  have ho : meromorphicOrderAt (response Phi) rho.1=
      (-((analyticZetaZeroMultiplicity rho-ell : ℕ) : ℤ) : ℤ) := by
    rw [response_order Phi rho hell]
    congr 1
    omega
  obtain ⟨g,hg,hg0,he⟩ := (meromorphicOrderAt_eq_int_iff hm).mp ho
  have heq : (fun s : ℂ => (s-rho.1)^(analyticZetaZeroMultiplicity rho-ell)*
      response Phi s)=ᶠ[𝓝[≠] rho.1] g := by
    filter_upwards [he,self_mem_nhdsWithin] with s hs (hsrho : s≠rho.1)
    rw [hs,smul_eq_mul,zpow_neg,zpow_natCast,← mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero _ (sub_ne_zero.mpr hsrho)),one_mul]
  exact ⟨g rho.1,hg0,(hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' heq.symm⟩

/-- Zero mean supplies an actual analytic numerator even at density. -/
theorem numerator_analytic_at_one {q : ℕ} [NeZero q] (Phi : ZMod q → ℂ)
    (hPhi : ∑ a : ZMod q,Phi a=0) : AnalyticAt ℂ (numerator Phi) 1 :=
  ((ZMod.differentiable_LFunction_of_sum_zero hPhi).analyticAt 1).deriv.neg

/-- The full zero-mean inverse is analytically density-free. -/
theorem density_removable {q : ℕ} [NeZero q] (Phi : ZMod q → ℂ)
    (hPhi : ∑ a : ZMod q,Phi a=0) :
    ∃ E : ℂ → ℂ,AnalyticAt ℂ E 1 ∧ response Phi=ᶠ[𝓝[≠] (1 : ℂ)] E := by
  have hA := differentiable_riemannZeta₁.analyticAt (1 : ℂ)
  have hn : riemannZeta₁ (1 : ℂ)≠0 := by simp [riemannZeta₁_one]
  refine ⟨fun s => numerator Phi s*(s-1)/riemannZeta₁ s,
    ((numerator_analytic_at_one Phi hPhi).mul
      (analyticAt_id.sub analyticAt_const)).div hA hn,?_⟩
  filter_upwards [self_mem_nhdsWithin,
    hA.continuousAt.eventually_ne hn |>.filter_mono nhdsWithin_le_nhds]
    with s (hs : s≠1) hsZ
  rw [response,riemannZeta_eq_inv_sub_mul hs]
  field_simp [sub_ne_zero.mpr hs,hsZ]

/-- A non-divisor residue perturbation of the modulus-three word. -/
def oddCode (a : ZMod 3) : ℂ := if a=1 then 1 else if a=2 then -1 else 0

/-- The original divisor code is retained only as the source anchor. -/
def baseCode (a : ZMod 3) : ℂ := if a=0 then 2 else -1

/-- These two codes distinguish residues one and two, although both
are coprime to three. Neither is a divisor-form code. -/
def residueCode (eps : ℂ) (a : ZMod 3) : ℂ := baseCode a+eps*oddCode a

theorem oddCode_mean_zero : ∑ a : ZMod 3,oddCode a=0 := by
  have h12 : (1 : ZMod 3)≠2 := by decide
  have he (a : ZMod 3) : oddCode a=
      (if a=1 then 1 else 0)-(if a=2 then 1 else 0) := by
    by_cases ha : a=1
    · simp [oddCode,ha,h12]
    · by_cases hb : a=2 <;> simp [oddCode,ha,hb,h12.symm]
  simp_rw [he]
  simp [Finset.sum_sub_distrib,Finset.sum_ite_eq']

theorem baseCode_mean_zero : ∑ a : ZMod 3,baseCode a=0 := by
  have he : baseCode=fun a : ZMod 3 => (if a=0 then 3 else 0)-1 := by
    funext a
    unfold baseCode
    split_ifs <;> norm_num
  rw [he,Finset.sum_sub_distrib]
  simp [Finset.sum_ite_eq',ZMod.card]

theorem residueCode_mean_zero (eps : ℂ) : ∑ a : ZMod 3,residueCode eps a=0 := by
  simp [residueCode,Finset.sum_add_distrib,← Finset.mul_sum,
    baseCode_mean_zero,oddCode_mean_zero]

/-- The source preflight uses fixed, bounded codes, not growing or
unrestricted amplitudes. -/
theorem residueCode_norm_le {eps : ℂ} (heps : eps∈({1,-1} : Finset ℂ))
    (a : ZMod 3) : ‖residueCode eps a‖≤2 := by
  have h01 : (0 : ZMod 3)≠1 := by decide
  have h02 : (0 : ZMod 3)≠2 := by decide
  have h10 : (1 : ZMod 3)≠0 := by decide
  have h12 : (1 : ZMod 3)≠2 := by decide
  have h20 : (2 : ZMod 3)≠0 := by decide
  have h21 : (2 : ZMod 3)≠1 := by decide
  have hcases : eps=1 ∨ eps=-1 := by simpa using heps
  rcases hcases with rfl | rfl <;>
    by_cases h0 : a=0
  all_goals first
  | subst a; norm_num [residueCode,baseCode,oddCode,h01,h02]
  | by_cases h1 : a=1
    · subst a
      norm_num [residueCode,baseCode,oddCode,h10,h12]
    · by_cases h2 : a=2
      · subst a
        norm_num [residueCode,baseCode,oddCode,h20,h21]
      · norm_num [residueCode,baseCode,oddCode,h0,h1,h2]

theorem residueCode_distinguishes_coprime (eps : ℂ) (heps : eps≠0) :
    residueCode eps 1≠residueCode eps 2 := by
  have h20 : (2 : ZMod 3)≠0 := by decide
  have h21 : (2 : ZMod 3)≠1 := by decide
  norm_num [residueCode,baseCode,oddCode,h20,h21]
  intro h
  apply heps
  linear_combination h/2

/-- Not merely a differently written divisor code: it cannot be a
function of gcd(3,n) on ordinary positive integer labels. -/
theorem residueCode_not_gcd (eps : ℂ) (heps : eps≠0) :
    ¬∃ f : ℕ → ℂ,∀ n : ℕ,residueCode eps n=f (Nat.gcd 3 n) := by
  rintro ⟨f,hf⟩
  have h1 := hf 1
  have h2 := hf 2
  norm_num only [Nat.gcd_one_right,Nat.gcd_succ,Nat.reduceMod,Nat.gcd_zero_right] at h1 h2
  exact residueCode_distinguishes_coprime eps heps (h1.trans h2.symm)

private def anchorNumerator (s : ℂ) : ℂ :=
  ArithmeticOperatorRamanujanInverseAudit.multiplier
    (3 : ℕ).divisors (ArithmeticOperatorRamanujanInverseAudit.ramanujanCoefficients 3) s*
      (-deriv riemannZeta s)+
    ArithmeticOperatorRamanujanInverseAudit.head
      (3 : ℕ).divisors (ArithmeticOperatorRamanujanInverseAudit.ramanujanCoefficients 3) s*
        riemannZeta s

private theorem base_decoded_eq :
    ArithmeticOperatorPeriodicInverseAudit.decoded baseCode=
      ArithmeticOperatorRamanujanInverseAudit.decoded
        (3 : ℕ).divisors (ArithmeticOperatorRamanujanInverseAudit.ramanujanCoefficients 3) := by
  have he : ArithmeticOperatorPeriodicInverseAudit.row baseCode=
      ArithmeticOperatorRamanujanInverseAudit.gammaCode
        (3 : ℕ).divisors (ArithmeticOperatorRamanujanInverseAudit.ramanujanCoefficients 3) := by
    funext n
    rw [ArithmeticOperatorRamanujanInverseAudit.gammaCode_ramanujan (by norm_num : 0<(3 : ℕ)),
      ArithmeticOperatorFullRamanujanAudit.ramanujanDivisor_prime Nat.prime_three]
    have hn : (n : ZMod 3)=0 ↔ 3∣n := ZMod.natCast_eq_zero_iff n 3
    by_cases hd : 3∣n <;> simp [ArithmeticOperatorPeriodicInverseAudit.row,baseCode,hd,hn]
  unfold ArithmeticOperatorPeriodicInverseAudit.decoded
  rw [he]
  rfl

private theorem numerator_base_eq {s : ℂ} (hs : s≠1) :
    numerator baseCode s=anchorNumerator s := by
  have ha : AnalyticOnNhd ℂ (numerator baseCode) ({(1 : ℂ)}ᶜ) :=
    fun z hz => numerator_analytic baseCode hz
  have hb : AnalyticOnNhd ℂ anchorNumerator ({(1 : ℂ)}ᶜ) := by
    intro z hz
    exact ((ArithmeticOperatorRamanujanInverseAudit.multiplier_analytic _ _ z).mul
      (analyticOn_riemannZeta z hz).deriv.neg).add
      ((ArithmeticOperatorRamanujanInverseAudit.head_analytic _ _ z).mul
        (analyticOn_riemannZeta z hz))
  have he : numerator baseCode=ᶠ[𝓝 (2 : ℂ)] anchorNumerator := by
    filter_upwards [isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds
      (by norm_num : (1 : ℝ)<(2 : ℂ).re)] with z hz
    have hz0 := riemannZeta_ne_zero_of_one_lt_re hz
    have hr := ArithmeticOperatorRamanujanInverseAudit.decoded_euler
      (3 : ℕ).divisors (ArithmeticOperatorRamanujanInverseAudit.ramanujanCoefficients 3)
      (fun P hP => Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hP) (by norm_num)) hz
    rw [← base_decoded_eq] at hr
    have h := (euler_response baseCode hz).symm.trans hr
    unfold response ArithmeticOperatorRamanujanInverseAudit.response logDeriv at h
    simp only [Pi.div_apply] at h
    dsimp [anchorNumerator]
    field_simp [hz0] at h ⊢
    linear_combination h
  exact ha.eqOn_of_preconnected_of_eventuallyEq hb
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
    (by norm_num : (2 : ℂ)∈{(1 : ℂ)}ᶜ) he hs

private theorem numerator_residue_eq (eps : ℂ) {s : ℂ} (hs : s≠1) :
    numerator (residueCode eps) s=numerator baseCode s+eps*numerator oddCode s := by
  have he : ZMod.LFunction (residueCode eps)=fun z =>
      ZMod.LFunction baseCode z+eps*ZMod.LFunction oddCode z := by
    funext z
    unfold ZMod.LFunction residueCode
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    ring
  have hD := ((ArithmeticOperatorPeriodicGammaAudit.analyticAt_periodicL baseCode hs).differentiableAt.hasDerivAt).add
      (((ArithmeticOperatorPeriodicGammaAudit.analyticAt_periodicL oddCode hs).differentiableAt.hasDerivAt).const_mul eps)
  change HasDerivAt (fun z => ZMod.LFunction baseCode z+eps*ZMod.LFunction oddCode z)
    (deriv (ZMod.LFunction baseCode) s+eps*deriv (ZMod.LFunction oddCode) s) s at hD
  unfold numerator
  rw [he,hD.deriv]
  ring

/-- Source-preserving conservation between two genuinely non-divisor
codes. This is joined before assessing either code. -/
theorem response_pair_eq {s : ℂ} (hs : s≠1) :
    response (residueCode 1) s+response (residueCode (-1)) s=2*response baseCode s := by
  unfold response
  rw [numerator_residue_eq 1 hs,numerator_residue_eq (-1) hs]
  ring

private theorem base_source (rho : NontrivialZetaZero) :
    Tendsto (fun s : ℂ => (s-rho.1)*response baseCode s) (𝓝[≠] rho.1)
      (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ)*
        ArithmeticOperatorRamanujanInverseAudit.multiplier
          (3 : ℕ).divisors (ArithmeticOperatorRamanujanInverseAudit.ramanujanCoefficients 3) rho.1)) := by
  have hne : ∀ᶠ s in 𝓝[≠] rho.1,riemannZeta s≠0 :=
    (analyticAt_riemannZeta_nontrivialZero rho).eventually_eq_zero_or_eventually_ne_zero
      |>.resolve_left (by simpa only [← analyticOrderAt_eq_top] using
        analyticOrderAt_riemannZeta_nontrivialZero_ne_top rho)
  have he : response baseCode=ᶠ[𝓝[≠] rho.1]
      ArithmeticOperatorRamanujanInverseAudit.response
        (3 : ℕ).divisors (ArithmeticOperatorRamanujanInverseAudit.ramanujanCoefficients 3) := by
    filter_upwards [hne,(continuous_id.continuousAt.eventually_ne rho.2.2.2).filter_mono nhdsWithin_le_nhds] with s hsZ hs1
    change s≠1 at hs1
    rw [response,numerator_base_eq hs1]
    unfold anchorNumerator ArithmeticOperatorRamanujanInverseAudit.response logDeriv
    simp only [Pi.div_apply]
    field_simp [hsZ]
  apply (ArithmeticOperatorRamanujanInverseAudit.actual_zero_source
    _ _ rho).congr'
  exact Filter.EventuallyEq.rfl.mul he.symm

/-- At least one of the TWO FIXED non-divisor codes has a genuine pole
at every actual zero. No common-L-zero, exposure or simplicity is assumed. -/
theorem exists_nondivisor_pole (rho : NontrivialZetaZero) :
    ∃ eps∈({1,-1} : Finset ℂ),meromorphicOrderAt (response (residueCode eps)) rho.1<0 := by
  have hm (eps : ℂ) : MeromorphicAt (response (residueCode eps)) rho.1 :=
    (numerator_analytic (residueCode eps) rho.2.2.2).meromorphicAt.div
      (analyticAt_riemannZeta_nontrivialZero rho).meromorphicAt
  by_contra hh
  have hplus : 0≤meromorphicOrderAt (response (residueCode 1)) rho.1 := by
    by_contra h
    exact hh ⟨1,by simp,lt_of_not_ge h⟩
  have hminus : 0≤meromorphicOrderAt (response (residueCode (-1))) rho.1 := by
    by_contra h
    exact hh ⟨-1,by simp,lt_of_not_ge h⟩
  obtain ⟨Ep,hEp,heP⟩ := (hm 1).meromorphicOrderAt_nonneg_iff.mp hplus
  obtain ⟨Em,hEm,heM⟩ := (hm (-1)).meromorphicOrderAt_nonneg_iff.mp hminus
  have hA : AnalyticAt ℂ (fun s => (Ep s+Em s)/2) rho.1 :=
    (hEp.add hEm).div_const (c := 2)
  have he : response baseCode=ᶠ[𝓝[≠] rho.1] fun s => (Ep s+Em s)/2 := by
    filter_upwards [heP,heM,(continuous_id.continuousAt.eventually_ne rho.2.2.2).filter_mono nhdsWithin_le_nhds] with s hp hm hs1
    change s≠1 at hs1
    have h := response_pair_eq hs1
    rw [hp,hm] at h
    linear_combination -h/2
  have ht0 : Tendsto (fun s : ℂ => (s-rho.1)*response baseCode s)
      (𝓝[≠] rho.1) (𝓝 0) := by
    have hz : Tendsto (fun s : ℂ => s-rho.1) (𝓝[≠] rho.1) (𝓝 0) := by
      simpa only [sub_self] using (show Tendsto (fun s : ℂ => s-rho.1)
        (𝓝[≠] rho.1) (𝓝 (rho.1-rho.1)) from
        (continuous_id.sub continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    have ht := hz.mul (hA.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    simp only [zero_mul] at ht
    exact ht.congr' (Filter.EventuallyEq.rfl.mul he.symm)
  exact ArithmeticOperatorRamanujanInverseAudit.ramanujan_actual_source_ne_zero
    Nat.prime_three.squarefree rho (tendsto_nhds_unique (base_source rho) ht0)

/-- The pole gate yields a finite numerator order strictly below the
actual multiplicity, rather than only a failure of a totalized value. -/
theorem exists_nondivisor_source_order (rho : NontrivialZetaZero) :
    ∃ eps∈({1,-1} : Finset ℂ),∃ ell : ℕ,
      ell<analyticZetaZeroMultiplicity rho ∧
        analyticOrderAt (numerator (residueCode eps)) rho.1=ell := by
  obtain ⟨eps,heps,hpole⟩ := exists_nondivisor_pole rho
  have hA := numerator_analytic (residueCode eps) rho.2.2.2
  have htop : analyticOrderAt (numerator (residueCode eps)) rho.1≠⊤ := by
    intro h
    have he : meromorphicOrderAt (response (residueCode eps)) rho.1=⊤ := by
      change meromorphicOrderAt (numerator (residueCode eps)/riemannZeta) rho.1=⊤
      rw [meromorphicOrderAt_div hA.meromorphicAt
        (analyticAt_riemannZeta_nontrivialZero rho).meromorphicAt,
        hA.meromorphicOrderAt_eq,h,ENat.map_top,
        meromorphicOrderAt_riemannZeta_nontrivialZero]
      simp
    rw [he] at hpole
    exact not_lt_of_ge le_top hpole
  obtain ⟨ell,hell⟩ := ENat.ne_top_iff_exists.mp htop
  have hell' : analyticOrderAt (numerator (residueCode eps)) rho.1=ell := hell.symm
  rw [response_order (residueCode eps) rho hell'] at hpole
  have hlt : ell<analyticZetaZeroMultiplicity rho := by
    have hi : (ell : ℤ)-(analyticZetaZeroMultiplicity rho : ℤ)<0 :=
      WithTop.coe_lt_coe.mp hpole
    exact_mod_cast sub_neg.mp hi
  exact ⟨eps,heps,ell,hlt,hell'⟩

/-- Unconditional finite-code source preflight at every actual zero,
with all multiplicities and the complete complex leading coefficient. -/
theorem exists_nondivisor_actual_source (rho : NontrivialZetaZero) :
    ∃ eps∈({1,-1} : Finset ℂ),∃ k : ℕ,0<k ∧
      k≤analyticZetaZeroMultiplicity rho ∧ ∃ v : ℂ,v≠0 ∧
        Tendsto (fun s : ℂ => (s-rho.1)^k*response (residueCode eps) s)
          (𝓝[≠] rho.1) (𝓝 v) := by
  obtain ⟨eps,heps,ell,hlt,hell⟩ := exists_nondivisor_source_order rho
  obtain ⟨v,hv,ht⟩ := actual_zero_source_of_order (residueCode eps) rho hell hlt
  exact ⟨eps,heps,analyticZetaZeroMultiplicity rho-ell,by omega,
    Nat.sub_le _ _,v,hv,ht⟩

/-- Coded holomorphy is EXACTLY the original strip nonvanishing problem.
It is not an independently established arithmetic inequality. -/
theorem pair_removable_iff_nonvanishing {s : ℂ} (hs0 : 0<s.re) (hs1 : s.re<1) :
    (∀ eps∈({1,-1} : Finset ℂ),∃ E : ℂ → ℂ,
      AnalyticAt ℂ E s ∧ response (residueCode eps)=ᶠ[𝓝[≠] s] E) ↔
        riemannZeta s≠0 := by
  have hsne : s≠1 := by intro h; simp [h] at hs1
  constructor
  · intro he hz
    let rho : NontrivialZetaZero := ⟨s,hz,by
      rintro ⟨n,hn⟩
      have h := congrArg Complex.re hn
      norm_num [Complex.mul_re] at h
      nlinarith [Nat.cast_nonneg (α := ℝ) n],hsne⟩
    obtain ⟨eps,heps,hpole⟩ := exists_nondivisor_pole rho
    obtain ⟨E,hE,hg⟩ := he eps heps
    have hm : MeromorphicAt (response (residueCode eps)) s :=
      (numerator_analytic (residueCode eps) hsne).meromorphicAt.div
        (analyticOn_riemannZeta s hsne).meromorphicAt
    exact not_lt_of_ge (hm.meromorphicOrderAt_nonneg_iff.mpr ⟨E,hE,hg⟩) hpole
  · intro hz eps _
    exact ⟨response (residueCode eps),
      (numerator_analytic (residueCode eps) hsne).div
        (analyticOn_riemannZeta s hsne) hz,Filter.EventuallyEq.rfl⟩

/-- Arbitrary input Gamma rows, solely for the collapse audit. These
inputs are not assumed to satisfy the actual integer Gamma equalities. -/
def freeNative {q : ℕ} (Phi : ZMod q → ℂ) (y : ℝ) (test g : ℕ → ℂ)
    (X : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 X,test n*primePhase y n*
    inverseRows (fun a => Phi a*g a) n

/-- Exact signed row kernel retaining the literal divided cutoff and
every correlated outer mask and phase. -/
def inverseKernel {q : ℕ} (Phi : ZMod q → ℂ) (y : ℝ) (test : ℕ → ℂ)
    (X a : ℕ) : ℂ :=
  Phi a*∑ d ∈ Finset.Icc 1 (X/a),
    (ArithmeticFunction.moebius d : ℂ)*test (a*d)*primePhase y (a*d)

/-- The ENTIRE finite inverse joins before any norms. -/
theorem freeNative_eq_scalar {q : ℕ} (Phi : ZMod q → ℂ) (y : ℝ)
    (test g : ℕ → ℂ) (X : ℕ) :
    freeNative Phi y test g X=
      ∑ a ∈ Finset.Icc 1 X,g a*inverseKernel Phi y test X a := by
  have he : freeNative Phi y test g X=
      ∑ n ∈ Finset.Icc 1 X,∑ da ∈ n.divisorsAntidiagonal,
        Phi da.1*g da.1*(ArithmeticFunction.moebius da.2 : ℂ)*
          test (da.1*da.2)*primePhase y (da.1*da.2) := by
    unfold freeNative inverseRows
    apply Finset.sum_congr rfl
    intro n _
    rw [Finset.mul_sum]
    conv_lhs => rw [← Nat.map_swap_divisorsAntidiagonal,Finset.sum_map]
    apply Finset.sum_congr rfl
    intro da hda
    have hprod := (Nat.mem_divisorsAntidiagonal.mp hda).1
    change test n*primePhase y n*((ArithmeticFunction.moebius da.2 : ℂ)*
      (Phi da.1*g da.1))=
        Phi da.1*g da.1*(ArithmeticFunction.moebius da.2 : ℂ)*
          test (da.1*da.2)*primePhase y (da.1*da.2)
    rw [hprod]
    ring
  rw [he,sum_Icc_divisorsAntidiagonal_eq_sum_divided_prefix X
    (fun a d => Phi a*g a*(ArithmeticFunction.moebius d : ℂ)*
      test (a*d)*primePhase y (a*d))]
  apply Finset.sum_congr rfl
  intro a _
  unfold inverseKernel
  rw [Finset.mul_sum,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

/-- Actual logarithmic rows are a specialization, not a free-weight
Gamma hypothesis. Every actual prime-power inverse fiber is retained. -/
theorem literal_native_eq {q : ℕ} (Phi : ZMod q → ℂ) (y : ℝ)
    (test : ℕ → ℂ) (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X,test n*
      ArithmeticOperatorPeriodicInverseAudit.phasedDecoded Phi y n)=
        ∑ a ∈ Finset.Icc 1 X,(Real.log a : ℂ)*inverseKernel Phi y test X a := by
  rw [← freeNative_eq_scalar]
  unfold freeNative
  apply Finset.sum_congr rfl
  intro n _
  rw [ArithmeticOperatorPeriodicInverseAudit.phasedDecoded_eq]
  change test n*(primePhase y n*inverseRows (fun a => Phi a*(Real.log a : ℂ)) n)=
    test n*primePhase y n*inverseRows (fun a => Phi a*(Real.log a : ℂ)) n
  ring

/-- No universal free-row allowance follows from coding/inversion.
Free rows are not actual Gamma, smooth or generalized-prime data. -/
theorem bound_forall_free_rows_iff {q : ℕ} (Phi : ZMod q → ℂ) (y : ℝ)
    (test : ℕ → ℂ) (X : ℕ) (B : ℝ) :
    (∀ g,‖freeNative Phi y test g X‖≤B) ↔
      0≤B ∧ ∀ a∈Finset.Icc 1 X,inverseKernel Phi y test X a=0 := by
  simp_rw [freeNative_eq_scalar]
  exact ArithmeticOperatorGramAudit.scalar_bound_forall_weights_iff _ _ _

/-- Actual termwise inverse debit, with every phase and proper power. -/
def fiberDebit {q : ℕ} (Phi : ZMod q → ℂ) (y : ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors,‖(ArithmeticFunction.moebius d : ℂ)*primePhase y d*
    ArithmeticOperatorPeriodicGammaAudit.wholeRow Phi y (n/d)‖

/-- Full literal debit; no residue or endpoint is deleted. -/
def fullDebit {q : ℕ} (Phi : ZMod q → ℂ) (y : ℝ) (X : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 X,fiberDebit Phi y n

theorem unit_le_fiberDebit {q : ℕ} (Phi : ZMod q → ℂ) (y : ℝ) {n : ℕ}
    (hn : 0<n) : ‖Phi n‖*Real.log n≤fiberDebit Phi y n := by
  have h1 : 1∈n.divisors := Nat.mem_divisors.mpr ⟨one_dvd n,hn.ne'⟩
  have hh := Finset.single_le_sum
    (fun d (_ : d∈n.divisors) => norm_nonneg
      ((ArithmeticFunction.moebius d : ℂ)*primePhase y d*
        ArithmeticOperatorPeriodicGammaAudit.wholeRow Phi y (n/d))) h1
  have hlog : 0≤Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  simpa only [fiberDebit,ArithmeticFunction.moebius_apply_one,Int.cast_one,
    one_mul,Nat.div_one,ArithmeticOperatorPeriodicGammaAudit.wholeRow_eq_log,
    norm_mul,norm_primePhase,mul_one,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg hlog] using hh

private theorem residueCode_three_mul (eps : ℂ) (a : ℕ) :
    residueCode eps ((3*a : ℕ) : ZMod 3)=2 := by
  have h01 : (0 : ZMod 3)≠1 := by decide
  have h02 : (0 : ZMod 3)≠2 := by decide
  have hn : ((3*a : ℕ) : ZMod 3)=0 := by
    rw [Nat.cast_mul]
    exact mul_eq_zero_of_left (by decide : (3 : ZMod 3)=0) _
  norm_num [residueCode,baseCode,oddCode,hn,h01,h02]

/-- The source-retaining non-divisor codes have an ACTUAL linear
inverse norm debit. Zero mean does not cancel any absolute unit fibers. -/
theorem fullDebit_lower (eps : ℂ) (y : ℝ) (H : ℕ) :
    (H : ℝ)*(2*Real.log 3)≤fullDebit (residueCode eps) y (3*H) := by
  let S := (Finset.Icc 1 H).image (fun a => 3*a)
  have hi : ∀ a∈Finset.Icc 1 H,∀ b∈Finset.Icc 1 H,3*a=3*b → a=b := by
    intros
    omega
  have hsub : S⊆Finset.Icc 1 (3*H) := by
    intro n hn
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hl,hu⟩ := Finset.mem_Icc.mp ha
    exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  calc
    _ = ∑ a ∈ Finset.Icc 1 H,2*Real.log 3 := by simp [Nat.card_Icc]
    _ ≤ ∑ a ∈ Finset.Icc 1 H,fiberDebit (residueCode eps) y (3*a) := by
      apply Finset.sum_le_sum
      intro a ha
      have ha1 := (Finset.mem_Icc.mp ha).1
      have hl : Real.log 3≤Real.log ((3*a : ℕ) : ℝ) :=
        Real.log_le_log (by norm_num) (by exact_mod_cast (show 3≤3*a by omega))
      have hh := unit_le_fiberDebit (residueCode eps) y (show 0<3*a by omega)
      rw [residueCode_three_mul] at hh
      norm_num only [norm_ofNat] at hh
      linarith
    _ = ∑ n∈S,fiberDebit (residueCode eps) y n :=
      (Finset.sum_image hi).symm
    _ ≤ fullDebit (residueCode eps) y (3*H) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun n _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))

/-- Absolute inverse-fiber payment diverges at every strip source
scale, even for these FIXED zero-mean non-divisor codes. -/
theorem tendsto_scaled_fullDebit_atTop {beta : ℝ} (hb : beta<1)
    (eps : ℂ) (y : ℝ) :
    Tendsto (fun J : ℕ => (Real.exp (-beta*Real.log 2))^J*
      fullDebit (residueCode eps) y (3*2^J)) atTop atTop := by
  have hr : 1<2*Real.exp (-beta*Real.log 2) := by
    have hl : 0<Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    have he : 2*Real.exp (-beta*Real.log 2)=Real.exp ((1-beta)*Real.log 2) := by
      rw [show (1-beta)*Real.log 2=Real.log 2+(-beta*Real.log 2) by ring,
        Real.exp_add,Real.exp_log (by norm_num : 0<(2 : ℝ))]
    rw [he]
    exact Real.one_lt_exp_iff.mpr (mul_pos (by linarith) hl)
  have ht := (tendsto_pow_atTop_atTop_of_one_lt hr).const_mul_atTop
    (show 0<(2 : ℝ)*Real.log (3 : ℝ) from
      mul_pos (by norm_num) (Real.log_pos (by norm_num : (1 : ℝ)<3)))
  apply tendsto_atTop_mono' atTop ?_ ht
  filter_upwards [] with J
  have hh := mul_le_mul_of_nonneg_left (fullDebit_lower eps y (2^J))
    (pow_nonneg (Real.exp_pos (-beta*Real.log 2)).le J)
  convert hh using 1
  push_cast
  rw [mul_pow]
  ring

end
end RiemannGaussian.ArithmeticOperatorResidueInverseAudit
