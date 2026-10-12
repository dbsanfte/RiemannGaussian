/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorPeriodicGammaAudit
import RiemannGaussian.ArithmeticOperatorIncidenceFreedom
import RiemannGaussian.ArithmeticOperatorCofactorParityAudit

/-!
# Periodic coding BETWEEN the complete Gamma row and its Möbius inverse

Unlike direct periodic Gamma evaluation, this word can retain an actual
zero source and cancel density. The simplest zero-mean parity code gives
EXACTLY a dyadic dilation of the original Mangoldt sequence plus its head.
It supplies no independent estimate of that prime sum.

At an unrestricted modulus larger than the physical cutoff, zero-mean
periodic codes can prescribe EVERY decoded finite profile with zero unit.
All actual Gamma rows and actual Möbius coefficients remain unchanged.
This closes free-code/finite-bookkeeping-only payment, not specifically
constrained fixed codes, amplitude budgets, or a signed prime estimate.
-/

namespace RiemannGaussian.ArithmeticOperatorPeriodicInverseAudit
noncomputable section
open Complex Filter ArithmeticOperatorKummerCutoff ArithmeticOperatorIncidenceFreedom
open ArithmeticOperatorGammaTwistAudit SuzukiCarryCorrelation
open scoped BigOperators Topology LSeries.notation ComplexConjugate

/-- Actual complete Gamma logarithm, coded before the ACTUAL inverse. -/
def row {q : ℕ} (Phi : ZMod q → ℂ) (n : ℕ) : ℂ :=
  Phi n*(Real.log n : ℂ)

/-- Actual Möbius inverse AFTER whole-label periodic Gamma coding. -/
def decoded {q : ℕ} (Phi : ZMod q → ℂ) (n : ℕ) : ℂ :=
  inverseRows (row Phi) n

/-- Both inverse and cofactor phases are retained, including proper powers. -/
def phasedDecoded {q : ℕ} (Phi : ZMod q → ℂ) (y : ℝ) (n : ℕ) : ℂ :=
  ∑ da∈n.divisorsAntidiagonal,(ArithmeticFunction.moebius da.1 : ℂ)*
    primePhase y da.1*ArithmeticOperatorPeriodicGammaAudit.wholeRow Phi y da.2

theorem phasedDecoded_eq {q : ℕ} (Phi : ZMod q → ℂ) (y : ℝ) (n : ℕ) :
    phasedDecoded Phi y n=primePhase y n*decoded Phi n := by
  rw [phasedDecoded,decoded,inverseRows,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro da hda
  rw [ArithmeticOperatorPeriodicGammaAudit.wholeRow_eq_log]
  have he := (Nat.mem_divisorsAntidiagonal.mp hda).1
  have hp : primePhase y da.1*primePhase y da.2=primePhase y n := by
    rw [←primePhase_mul y (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hda |>.bot_lt)
      (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hda |>.bot_lt),he]
  unfold row
  calc
    _ = (primePhase y da.1*primePhase y da.2)*
      ((ArithmeticFunction.moebius da.1 : ℂ)*Phi da.2*(Real.log da.2 : ℂ)) := by ring
    _ = _ := by rw [hp]; ring

private def mu (n : ℕ) : ℂ := (ArithmeticFunction.moebius n : ℂ)
private def natLog (n : ℕ) : ℂ := (Real.log n : ℂ)
private def mangoldt (n : ℕ) : ℂ := (ArithmeticFunction.vonMangoldt n : ℂ)

private theorem inverse_log : mu ⍟ natLog=mangoldt := by
  funext n
  by_cases hn : n=0
  · simp [hn,mangoldt]
  · rw [LSeries.convolution_def]
    exact (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
      (f := mangoldt) (g := natLog)).mp (fun n _ => by
        change (∑ d∈n.divisors,(ArithmeticFunction.vonMangoldt d : ℂ))=(Real.log n : ℂ)
        rw [←Complex.ofReal_sum,ArithmeticFunction.vonMangoldt_sum])
      n (Nat.pos_of_ne_zero hn)

private theorem inverse_one : mu ⍟ (1 : ℕ → ℂ)=
    zetaFiniteCoefficient {1} (fun _ => (1 : ℂ)) := by
  funext n
  by_cases hn : n=0
  · simp [hn,zetaFiniteCoefficient]
  · rw [LSeries.convolution_def]
    exact (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
      (f := zetaFiniteCoefficient {1} (fun _ => (1 : ℂ))) (g := (1 : ℕ → ℂ))).mp
      (fun m hm => by
        simp [zetaFiniteCoefficient,Finset.sum_ite_eq',Nat.mem_divisors,hm.ne'])
      n (Nat.pos_of_ne_zero hn)

private theorem convolution_assoc (a b c : ℕ → ℂ) :
    a ⍟ (b ⍟ c)=(a ⍟ b) ⍟ c := by
  simp only [LSeries.convolution,ArithmeticFunction.toArithmeticFunction_eq_self,mul_assoc]

private theorem convolution_comm (a b : ℕ → ℂ) : a ⍟ b=b ⍟ a := by
  simp only [LSeries.convolution,mul_comm]

private theorem inverse_dilation (P : ℕ) (a : ℕ → ℂ) (ha0 : a 0=0) :
    mu ⍟ zetaDilationCoefficient P a=zetaDilationCoefficient P (mu ⍟ a) := by
  rw [zetaDilationCoefficient_eq_convolution P a ha0,convolution_assoc,
    convolution_comm mu,←convolution_assoc,
    zetaDilationCoefficient_eq_convolution P (mu ⍟ a) (by simp)]

/-- Smallest zero-mean additive code: even labels minus odd labels. -/
def parityCode (a : ZMod 2) : ℂ := if a=0 then 1 else -1

theorem parityCode_mean_zero : ∑ a : ZMod 2,parityCode a=0 := by
  classical
  have he : ∀ a : ZMod 2,parityCode a=(if a=0 then 2 else 0)-1 := by
    intro a
    unfold parityCode
    split_ifs <;> norm_num
  simp_rw [he]
  simp [Finset.sum_sub_distrib,Finset.sum_ite_eq',ZMod.card]

/-- Complete Gamma code as two literal integer dilations, not a
physical-mask completion or an assertion about arbitrary prime weights. -/
theorem parity_row {n : ℕ} (hn : 0<n) :
    row parityCode n=2*zetaDilationCoefficient 2 natLog n+
      2*(Real.log 2 : ℂ)*zetaDilationCoefficient 2 (1 : ℕ → ℂ) n-natLog n := by
  have hc : (n : ZMod 2)=0 ↔ 2∣n := ZMod.natCast_eq_zero_iff n 2
  by_cases hd : 2∣n
  · have he := Nat.mul_div_cancel' hd
    have hp : 0<n/2 := by omega
    have hl : Real.log (n : ℝ)=Real.log 2+Real.log ((n/2 : ℕ) : ℝ) := by
      conv_lhs => rw [←he]
      rw [Nat.cast_mul,Real.log_mul (by norm_num) (by exact_mod_cast hp.ne')]
      norm_num
    simp only [row,parityCode,ite_eq_left (hc.mpr hd),one_mul,
      zetaDilationCoefficient,ite_eq_left hd,Pi.one_apply,natLog,hl,Complex.ofReal_add]
    ring
  · simp [row,parityCode,ite_eq_right (mt hc.mp hd),zetaDilationCoefficient,hd,natLog]

/-- Exact inverse: all source-carrying mass is the OLD prime sequence
and its dyadic dilation. Every actual proper power is still present. -/
theorem parity_decoded (n : ℕ) :
    decoded parityCode n=2*zetaDilationCoefficient 2 mangoldt n-mangoldt n+
      (if n=2 then 2*(Real.log 2 : ℂ) else 0) := by
  have he : mu ⍟ row parityCode=mu ⍟ (fun n => 2*zetaDilationCoefficient 2 natLog n+
      2*(Real.log 2 : ℂ)*zetaDilationCoefficient 2 (1 : ℕ → ℂ) n-natLog n) := by
    apply LSeries.convolution_congr (fun _ => rfl)
    intro n hn
    exact parity_row (Nat.pos_of_ne_zero hn)
  have hs : decoded parityCode=mu ⍟ row parityCode := by
    rw [LSeries.convolution_def]
    rfl
  have hdlog := congrArg (fun f : ℕ → ℂ => f n) (inverse_dilation 2 natLog (by simp [natLog]))
  have hd1 := congrArg (fun f : ℕ → ℂ => f n)
    (inverse_dilation 2 (fun n : ℕ => if n=0 then 0 else 1) (by simp))
  have h1 : mu ⍟ (fun n : ℕ => if n=0 then 0 else 1)=mu ⍟ (1 : ℕ → ℂ) := by
    apply LSeries.convolution_congr (fun _ => rfl)
    intro n hn
    simp [hn]
  have hdil : mu ⍟ zetaDilationCoefficient 2 (fun n : ℕ => if n=0 then 0 else 1)=
      mu ⍟ zetaDilationCoefficient 2 (1 : ℕ → ℂ) := by
    apply LSeries.convolution_congr (fun _ => rfl)
    intro m hm
    by_cases hd : 2∣m
    · have hp : m/2≠0 := by omega
      simp [zetaDilationCoefficient,hd,hp]
    · simp [zetaDilationCoefficient,hd]
  have hunit : (mu ⍟ zetaDilationCoefficient 2 (1 : ℕ → ℂ)) n=
      if n=2 then 1 else 0 := by
    rw [←hdil]
    rw [hd1,h1,inverse_one]
    by_cases hn : n=2
    · simp [hn,zetaDilationCoefficient,zetaFiniteCoefficient]
    · by_cases hd : 2∣n
      · have hq : n/2≠1 := by
          intro he
          have hh := Nat.mul_div_cancel' hd
          rw [he] at hh
          omega
        simp [hn,hd,hq,zetaDilationCoefficient,zetaFiniteCoefficient]
      · simp [hn,hd,zetaDilationCoefficient]
  rw [hs,he,LSeries.convolution_def]
  simp_rw [mul_sub,mul_add]
  rw [Finset.sum_sub_distrib,Finset.sum_add_distrib]
  have hdis : ∀ a : ℕ → ℂ, (∑ da∈n.divisorsAntidiagonal,mu da.1*(2*a da.2))=
      2*(mu ⍟ a) n := by
    intro a
    rw [LSeries.convolution_def,Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  rw [hdis,show (∑ da∈n.divisorsAntidiagonal,
      mu da.1*(2*(Real.log 2 : ℂ)*zetaDilationCoefficient 2 (1 : ℕ → ℂ) da.2))=
      2*(Real.log 2 : ℂ)*(mu ⍟ zetaDilationCoefficient 2 (1 : ℕ → ℂ)) n by
    rw [LSeries.convolution_def,Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => by ring)]
  rw [inverse_log] at hdlog
  rw [hdlog,hunit,show (∑ da∈n.divisorsAntidiagonal,mu da.1*natLog da.2)=mangoldt n by
    have hi := congrArg (fun f : ℕ → ℂ => f n) inverse_log
    rw [LSeries.convolution_def] at hi
    exact hi]
  split_ifs <;> ring

/-- Complete analytic response of this EXACT parity inverse. -/
def parityMultiplier (s : ℂ) : ℂ := 2*zetaPrimeFeature s 2-1

/-- Exact response including the finite head and its complete phase. -/
def parityResponse (s : ℂ) : ℂ :=
  parityMultiplier s*(-logDeriv riemannZeta s)+2*(Real.log 2 : ℂ)*zetaPrimeFeature s 2

/-- Genuine convergent Euler response, not continuation asserted as a
prime sum outside Re(s)>1. -/
theorem parity_euler_response {s : ℂ} (hs : 1<s.re) :
    LSeries (decoded parityCode) s=parityResponse s := by
  have hm := (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).LSeriesHasSum
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs] at hm
  change LSeriesHasSum mangoldt s (-deriv riemannZeta s/riemannZeta s) at hm
  have hd := LSeriesHasSum_zetaDilationCoefficient (by norm_num : 0<(2 : ℕ))
    (by simp [mangoldt] : mangoldt 0=0) hm
  have hh := LSeriesHasSum_zetaFiniteCoefficient {2}
    (fun _ => 2*(Real.log 2 : ℂ)) (by simp) s
  have ht := ((hd.smul 2).sub hm).add hh
  have he : decoded parityCode=(2 : ℂ) • zetaDilationCoefficient 2 mangoldt-mangoldt+
      zetaFiniteCoefficient {2} (fun _ => 2*(Real.log 2 : ℂ)) := by
    funext n
    simpa [zetaFiniteCoefficient,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
      using parity_decoded n
  rw [he,ht.LSeries_eq]
  simp only [zetaFiniteDirichletSeries,Finset.sum_singleton,parityResponse,
    parityMultiplier,logDeriv_apply,neg_div]
  ring

/-- Every compatible physical height remains on the TOTAL integer. -/
theorem parity_phased_euler {s : ℂ} (hs : 1<s.re) (y : ℝ) :
    LSeries (phasedDecoded parityCode y) s=parityResponse (s+I*y) := by
  have he : phasedDecoded parityCode y=fun n => decoded parityCode n*primePhase y n := by
    funext n
    rw [phasedDecoded_eq,mul_comm]
  rw [he,LSeries_primePhase,parity_euler_response (by simpa using hs)]

theorem parityMultiplier_nonzero_at_zero (rho : NontrivialZetaZero) :
    parityMultiplier rho.1≠0 := by
  have hl : 0<Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hb := NontrivialZetaZero.re_lt_one rho
  have hg : 1<Real.exp ((1-rho.1.re)*Real.log 2) :=
    Real.one_lt_exp_iff.mpr (mul_pos (by linarith) hl)
  have he : 2*Real.exp (-rho.1.re*Real.log 2)=Real.exp ((1-rho.1.re)*Real.log 2) := by
    rw [show (1-rho.1.re)*Real.log 2=Real.log 2+(-rho.1.re*Real.log 2) by ring,
      Real.exp_add,Real.exp_log (by norm_num : 0<(2 : ℝ))]
  intro hz
  have hn := congrArg norm (sub_eq_zero.mp hz)
  rw [norm_mul,norm_ofNat,norm_zetaPrimeFeature] at hn
  simp only [zetaPrimeExpWeight] at hn
  norm_num only [Nat.cast_ofNat] at hn
  rw [he] at hn
  simp only [norm_one] at hn
  linarith

/-- Actual matched source at ALL multiplicities; no exposure, common
nonprincipal L-zero, or nonlinear diagnostic-source assumption. -/
theorem parity_actual_source (rho : NontrivialZetaZero) :
    Tendsto (fun s : ℂ => (s-rho.1)*parityResponse s) (𝓝[≠] rho.1)
      (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ)*parityMultiplier rho.1)) := by
  have ha : Continuous parityMultiplier := by unfold parityMultiplier zetaPrimeFeature; fun_prop
  have hhead : Continuous (fun s : ℂ => 2*(Real.log 2 : ℂ)*zetaPrimeFeature s 2) := by
    unfold zetaPrimeFeature
    fun_prop
  have hz : Tendsto (fun s : ℂ => s-rho.1) (𝓝[≠] rho.1) (𝓝 0) := by
    simpa only [sub_self] using (show Tendsto (fun s : ℂ => s-rho.1)
      (𝓝[≠] rho.1) (𝓝 (rho.1-rho.1)) from
      (continuous_id.sub continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have ht := ((ha.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).mul
    (ArithmeticOperatorFullRamanujanAudit.tendsto_restored_zero_source rho)).add
    (hz.mul (hhead.continuousAt.tendsto.mono_left nhdsWithin_le_nhds))
  simp only [zero_mul,add_zero] at ht
  convert ht using 1
  · funext s
    unfold parityResponse
    ring
  · congr 1
    ring

theorem parity_actual_source_nonzero (rho : NontrivialZetaZero) :
    -(analyticZetaZeroMultiplicity rho : ℂ)*parityMultiplier rho.1≠0 :=
  mul_ne_zero (ArithmeticOperatorFullRamanujanAudit.restored_source_ne_zero rho)
    (parityMultiplier_nonzero_at_zero rho)

private theorem pole_source : Tendsto (fun s : ℂ => (s-1)*(-logDeriv riemannZeta s))
    (𝓝[≠] (1 : ℂ)) (𝓝 1) := by
  have ha := differentiable_riemannZeta₁.analyticAt (1 : ℂ)
  have hn : riemannZeta₁ (1 : ℂ)≠0 := by simp [riemannZeta₁_one]
  have hc : ContinuousAt (logDeriv riemannZeta₁) (1 : ℂ) :=
    ha.deriv.continuousAt.div ha.continuousAt hn
  have hz : Tendsto (fun s : ℂ => s-1) (𝓝[≠] (1 : ℂ)) (𝓝 0) := by
    simpa only [sub_self] using (show Tendsto (fun s : ℂ => s-1)
      (𝓝[≠] (1 : ℂ)) (𝓝 ((1 : ℂ)-1)) from
      (continuous_id.sub continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have ht := tendsto_const_nhds (x := (1 : ℂ)) |>.sub
    (hz.mul (hc.tendsto.mono_left nhdsWithin_le_nhds))
  simp only [zero_mul,sub_zero] at ht
  apply ht.congr'
  filter_upwards [ha.continuousAt.eventually_ne hn |>.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with s hs hs1
  have hzeta : riemannZeta s≠0 := by
    intro he
    apply hs
    rw [riemannZeta₁_eq_sub_one_mul hs1,he,mul_zero]
  rw [neg_logDeriv_riemannZeta_eq_pole_sub hs1 hzeta]
  field_simp [sub_ne_zero.mpr hs1]

theorem parityMultiplier_one : parityMultiplier 1=0 := by
  simp [parityMultiplier,zetaPrimeFeature,Complex.exp_neg,
    Complex.exp_log (by norm_num : (2 : ℂ)≠0)]

/-- The density residue cancels WITHOUT cancelling the actual zero.
No independent literal prime estimate is inferred from this source test. -/
theorem parity_density_source_zero :
    Tendsto (fun s : ℂ => (s-1)*parityResponse s) (𝓝[≠] (1 : ℂ)) (𝓝 0) := by
  have ha : Continuous parityMultiplier := by unfold parityMultiplier zetaPrimeFeature; fun_prop
  have hh : Continuous (fun s : ℂ => 2*(Real.log 2 : ℂ)*zetaPrimeFeature s 2) := by
    unfold zetaPrimeFeature
    fun_prop
  have hz : Tendsto (fun s : ℂ => s-1) (𝓝[≠] (1 : ℂ)) (𝓝 0) := by
    simpa only [sub_self] using (show Tendsto (fun s : ℂ => s-1)
      (𝓝[≠] (1 : ℂ)) (𝓝 ((1 : ℂ)-1)) from
      (continuous_id.sub continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have ht := ((ha.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).mul pole_source).add
    (hz.mul (hh.continuousAt.tendsto.mono_left nhdsWithin_le_nhds))
  simp only [parityMultiplier_one,zero_mul,zero_add] at ht
  apply ht.congr
  intro s
  unfold parityResponse
  ring

/-- Zero-mean completion of ANY prefix. The unused residue zero is
outside the physical prefix and absorbs the exact code mean. -/
def prefixCode (X : ℕ) (g : ℕ → ℂ) : ZMod (X+2) → ℂ := fun a =>
  (if 1≤a.val ∧ a.val≤X then g a.val/(Real.log a.val : ℂ) else 0)-
  (if a=0 then ∑ b : ZMod (X+2),
    if 1≤b.val ∧ b.val≤X then g b.val/(Real.log b.val : ℂ) else 0 else 0)

theorem prefixCode_mean_zero (X : ℕ) (g : ℕ → ℂ) :
    ∑ a : ZMod (X+2),prefixCode X g a=0 := by
  classical
  unfold prefixCode
  rw [Finset.sum_sub_distrib]
  simp [Finset.sum_ite_eq']

/-- Every nonunit prescribed Gamma row is coded exactly, with no
coefficient-budget bound imposed or silently assumed. -/
theorem prefixCode_row {X n : ℕ} (g : ℕ → ℂ) (hn : 0<n) (hX : n≤X) (hg : g 1=0) :
    row (prefixCode X g) n=g n := by
  have hv : (n : ZMod (X+2)).val=n := ZMod.val_natCast_of_lt (by omega)
  have hne : (n : ZMod (X+2))≠0 := by
    intro he
    have hh := congrArg ZMod.val he
    rw [hv,ZMod.val_zero] at hh
    omega
  rw [row,prefixCode,ite_eq_right hne,sub_zero,hv,ite_eq_left ⟨hn,hX⟩]
  by_cases h1 : n=1
  · simp [h1,hg]
  · exact div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr
      (ne_of_gt (Real.log_pos (by exact_mod_cast (show 1<n from by omega)))))

/-- Actual Gamma data and actual Möbius inverse plus arbitrary zero-mean
growing codes still permit EVERY finite decoded profile with zero unit.
This does not claim those profiles themselves satisfy actual Gamma data. -/
theorem exists_zero_mean_code_for_prefix (X : ℕ) (w : ℕ → ℂ) (hw : w 1=0) :
    ∃ Phi : ZMod (X+2) → ℂ,(∑ a : ZMod (X+2),Phi a=0) ∧
      ∀ n∈Finset.Icc 1 X,decoded Phi n=w n := by
  let g := divisorObservation w
  have hg : g 1=0 := by simp [g,divisorObservation,hw]
  refine ⟨prefixCode X g,prefixCode_mean_zero X g,?_⟩
  intro n hn
  obtain ⟨hn0,hnX⟩ := Finset.mem_Icc.mp hn
  have hi := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := w) (g := g)).mp (fun _ _ => rfl) n hn0
  rw [decoded,inverseRows]
  rw [←hi]
  apply Finset.sum_congr rfl
  intro da hda
  have hp : 0<da.2 := Nat.right_ne_zero_of_mem_divisorsAntidiagonal hda |>.bot_lt
  have hd : da.2≤n := Nat.le_of_dvd hn0 (Nat.dvd_of_mem_divisors
    (Nat.snd_mem_divisors_of_mem_antidiagonal hda))
  rw [prefixCode_row g hp (hd.trans hnX) hg]

/-- The joined phased quadratic has EVERY finite vector available;
modular/Gamma bookkeeping alone adds no PSD restriction on these codes. -/
theorem coded_quadratic_nonnegative_iff (X : ℕ) (K : ℕ → ℕ → ℂ) (y : ℝ) :
    (∀ Phi : ZMod (X+2) → ℂ,(∑ a : ZMod (X+2),Phi a=0) →
      0≤(∑ n∈Finset.Icc 2 X,∑ m∈Finset.Icc 2 X,
        K n m*phasedDecoded Phi y n*conj (phasedDecoded Phi y m)).re) ↔
    ∀ w : ℕ → ℂ,0≤(∑ n∈Finset.Icc 2 X,∑ m∈Finset.Icc 2 X,
      K n m*(primePhase y n*w n)*conj (primePhase y m*w m)).re := by
  classical
  constructor
  · intro hh w
    let v := fun n : ℕ => if n=1 then 0 else w n
    obtain ⟨Phi,hPhi,hmatch⟩ := exists_zero_mean_code_for_prefix X v (by simp [v])
    have he : ∀ n∈Finset.Icc 2 X,phasedDecoded Phi y n=primePhase y n*w n := by
      intro n hn
      have hn' := Finset.mem_Icc.mp hn
      rw [phasedDecoded_eq,hmatch n (Finset.mem_Icc.mpr ⟨by omega,hn'.2⟩)]
      simp only [v,ite_eq_right (show n≠1 by omega)]
    have hsum : (∑ n∈Finset.Icc 2 X,∑ m∈Finset.Icc 2 X,
        K n m*phasedDecoded Phi y n*conj (phasedDecoded Phi y m))=
        ∑ n∈Finset.Icc 2 X,∑ m∈Finset.Icc 2 X,
        K n m*(primePhase y n*w n)*conj (primePhase y m*w m) := by
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro m hm
      rw [he n hn,he m hm]
    rw [←hsum]
    exact hh Phi hPhi
  · intro hh Phi _
    simpa only [phasedDecoded_eq] using hh (decoded Phi)

/-- Actual unaltered Gamma/Möbius data alone do NOT bound unrestricted
zero-mean periodic-code amplitudes at even the first nonunit endpoint. -/
theorem no_uniform_coded_allowance {X : ℕ} (hX : 2≤X) (y : ℝ) (B : ℝ) :
    ∃ Phi : ZMod (X+2) → ℂ,(∑ a : ZMod (X+2),Phi a=0) ∧
      B<‖phasedDecoded Phi y 2‖ := by
  let w := fun n : ℕ => if n=2 then (|B|+1 : ℝ) else 0
  obtain ⟨Phi,hPhi,he⟩ := exists_zero_mean_code_for_prefix X
    (fun n => (w n : ℂ)) (by simp [w])
  refine ⟨Phi,hPhi,?_⟩
  rw [phasedDecoded_eq,he 2 (Finset.mem_Icc.mpr ⟨by norm_num,hX⟩),norm_mul,norm_primePhase]
  simp only [w,ite_eq_left rfl,one_mul,Complex.norm_real,Real.norm_eq_abs]
  rw [abs_of_pos (by positivity : 0 < |B|+1)]
  linarith [le_abs_self B]

end
end RiemannGaussian.ArithmeticOperatorPeriodicInverseAudit
