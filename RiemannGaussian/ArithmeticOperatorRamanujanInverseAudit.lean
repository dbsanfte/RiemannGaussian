/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorPeriodicInverseAudit
import RiemannGaussian.ArithmeticOperatorCompositeRamanujanFreedom
import RiemannGaussian.ArithmeticOperatorCrtLagAudit
import RiemannGaussian.ZetaCoprimeEulerPhase
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Structured divisor codes between the actual Gamma row and actual Möbius inverse

Unlike unrestricted-code freedom, this fixes a literal divisor/Ramanujan
code. Every actual Gamma value, every actual Möbius coefficient, proper
prime power, phase and cutoff endpoint is retained. Exact inversion gives
only finite dilations of the original Mangoldt sequence plus an explicit
finite head. For nonunit squarefree Ramanujan moduli the genuine zero
source survives every multiplicity while the density pole is removable.

This freezes estimation from this fixed structured operator word alone;
the original signed dilated prime sum is unpaid. Non-divisor residue codes,
growing complexity, correlated incomplete masks and actual nonlinear
arithmetic constraints are not covered.
-/

namespace RiemannGaussian.ArithmeticOperatorRamanujanInverseAudit
noncomputable section
open Complex Filter
open ArithmeticOperatorIncidenceFreedom ArithmeticOperatorRamanujanAudit
open ArithmeticOperatorKummerCutoff
open ArithmeticOperatorGammaTwistAudit SuzukiCarryCorrelation
open scoped BigOperators Topology LSeries.notation

private def mu (n : ℕ) : ℂ := (ArithmeticFunction.moebius n : ℂ)
private def natLog (n : ℕ) : ℂ := (Real.log n : ℂ)
private def mangoldt (n : ℕ) : ℂ := (ArithmeticFunction.vonMangoldt n : ℂ)
private def oneRow (n : ℕ) : ℂ := if n=0 then 0 else 1

private theorem convolution_assoc (a b c : ℕ → ℂ) :
    a ⍟ (b ⍟ c)=(a ⍟ b) ⍟ c := by
  simp only [LSeries.convolution,ArithmeticFunction.toArithmeticFunction_eq_self,mul_assoc]

private theorem convolution_comm (a b : ℕ → ℂ) : a ⍟ b=b ⍟ a := by
  simp only [LSeries.convolution,mul_comm]

private theorem inverse_log : mu ⍟ natLog=mangoldt := by
  funext n
  by_cases hn : n=0
  · simp [hn,mangoldt]
  · rw [LSeries.convolution_def]
    exact (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
      (f := mangoldt) (g := natLog)).mp (fun m _ => by
        change (∑ d∈m.divisors,(ArithmeticFunction.vonMangoldt d : ℂ))=(Real.log m : ℂ)
        rw [←Complex.ofReal_sum,ArithmeticFunction.vonMangoldt_sum])
      n (Nat.pos_of_ne_zero hn)

private theorem inverse_one : mu ⍟ oneRow=zetaFiniteCoefficient {1} (fun _ => 1) := by
  have hm : toArithmeticFunction mu=(ArithmeticFunction.moebius : ArithmeticFunction ℂ) := by
    ext n
    by_cases hn : n=0 <;> simp [mu,toArithmeticFunction,hn]
  have ho : toArithmeticFunction oneRow=(ArithmeticFunction.zeta : ArithmeticFunction ℂ) := by
    ext n
    simp [oneRow,toArithmeticFunction]
  rw [LSeries.convolution,hm,ho,ArithmeticFunction.coe_moebius_mul_coe_zeta]
  funext n
  simp [zetaFiniteCoefficient,ArithmeticFunction.one_apply]

/-- Dilation commutes with the full actual inverse on every positive fiber.
The zero coefficient is discharged rather than completed away. -/
theorem inverseRows_dilation (P : ℕ) (a : ℕ → ℂ) (ha0 : a 0=0) :
    inverseRows (zetaDilationCoefficient P a)=
      zetaDilationCoefficient P (inverseRows a) := by
  have he (g : ℕ → ℂ) : inverseRows g=mu ⍟ g := by rw [LSeries.convolution_def]; rfl
  simp_rw [he]
  rw [zetaDilationCoefficient_eq_convolution P a ha0,convolution_assoc,
    convolution_comm mu,←convolution_assoc,
    zetaDilationCoefficient_eq_convolution P (mu ⍟ a) (by simp)]

/-- One literal divisibility mask on the actual integer logarithm. -/
def maskedLog (P n : ℕ) : ℂ := if P ∣ n then (Real.log n : ℂ) else 0

private theorem maskedLog_split {P : ℕ} (hP : 0<P) (n : ℕ) :
    maskedLog P n=zetaDilationCoefficient P natLog n+
      (Real.log P : ℂ)*zetaDilationCoefficient P oneRow n := by
  by_cases hn : n=0
  · simp [hn,maskedLog,zetaDilationCoefficient,natLog,oneRow]
  by_cases hd : P ∣ n
  · have hq0 : 0<n/P := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd) hP
    have hl : Real.log (n : ℝ)=Real.log P+Real.log ((n/P : ℕ) : ℝ) := by
      conv_lhs => rw [←Nat.mul_div_cancel' hd]
      rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hP.ne')
        (by exact_mod_cast hq0.ne')]
    simp [maskedLog,zetaDilationCoefficient,hd,natLog,oneRow,hq0.ne',hl,
      Complex.ofReal_add,add_comm]
  · simp [maskedLog,zetaDilationCoefficient,hd]

/-- Exact arithmetic classification of a masked Gamma inverse. It gives
the old Mangoldt dilation plus its literal single-label head, not a new
prime correlation or an independent inequality. -/
theorem inverseRows_maskedLog {P : ℕ} (hP : 0<P) (n : ℕ) :
    inverseRows (maskedLog P) n=zetaDilationCoefficient P mangoldt n+
      (if n=P then (Real.log P : ℂ) else 0) := by
  have he : maskedLog P=fun n => zetaDilationCoefficient P natLog n+
      (Real.log P : ℂ)*zetaDilationCoefficient P oneRow n :=
    funext (maskedLog_split hP)
  have hi : inverseRows natLog=mangoldt := by rw [show inverseRows natLog=mu ⍟ natLog by
    rw [LSeries.convolution_def]; rfl,inverse_log]
  have ho : inverseRows oneRow=zetaFiniteCoefficient {1} (fun _ => 1) := by
    rw [show inverseRows oneRow=mu ⍟ oneRow by rw [LSeries.convolution_def]; rfl,inverse_one]
  rw [he,inverseRows]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  have hlin : (∑ da∈n.divisorsAntidiagonal,
      (ArithmeticFunction.moebius da.1 : ℂ)*
        ((Real.log P : ℂ)*zetaDilationCoefficient P oneRow da.2)) =
      (Real.log P : ℂ)*(∑ da∈n.divisorsAntidiagonal,
        (ArithmeticFunction.moebius da.1 : ℂ)*zetaDilationCoefficient P oneRow da.2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  rw [hlin]
  change inverseRows (zetaDilationCoefficient P natLog) n+
    (Real.log P : ℂ)*inverseRows (zetaDilationCoefficient P oneRow) n= _
  rw [inverseRows_dilation P natLog (by simp [natLog]),hi,
    inverseRows_dilation P oneRow (by simp [oneRow]),ho]
  by_cases hd : P ∣ n
  · have heq : n/P=1 ↔ n=P := by
      constructor
      · intro h
        have hh := Nat.mul_div_cancel' hd
        rw [h,mul_one] at hh
        exact hh.symm
      · rintro rfl
        exact Nat.div_self hP
    simp [zetaDilationCoefficient,hd,zetaFiniteCoefficient,heq]
  · have hnP : n≠P := by rintro rfl; exact hd dvd_rfl
    simp [zetaDilationCoefficient,hd,hnP]

/-- A fixed finite divisor code; the coefficients can be correlated or
complex, but no physical row or cofactor is deleted. -/
def gammaCode (D : Finset ℕ) (c : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ P∈D,c P*maskedLog P n

/-- Nonconstant divisor-structured lag code, fixed before joining the
native row. Ramanujan codes are a specialization, not arbitrary profiles. -/
def residueCode (q : ℕ) (c : ℕ → ℂ) (h : ZMod q) : ℂ :=
  ∑ P∈q.divisors,c P*(if P ∣ h.val then (1 : ℂ) else 0)

/-- Exact bridge from the native nonconstant CRT lag code to the coded
actual Gamma logarithm. Every selected residue and divisor remains literal. -/
theorem coded_lag_gamma {q : ℕ} [NeZero q] (n : ℕ) (c : ℕ → ℂ) :
    (∑ h : ZMod q,residueCode q c h*
      (if q ∣ n+h.val then (1 : ℂ) else 0))*(Real.log n : ℂ)=
        gammaCode q.divisors c n := by
  classical
  rw [ArithmeticOperatorCrtLagAudit.coded_lag_indicator]
  unfold residueCode gammaCode maskedLog
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro P hP
  have hnq : q ∣ n+(-(n : ZMod q)).val :=
    (ArithmeticOperatorCrtLagAudit.lag_dvd_iff n _).mpr rfl
  have hd := (Nat.dvd_of_mem_divisors hP).trans hnq
  have he : P ∣ (-(n : ZMod q)).val ↔ P ∣ n := by
    constructor
    · intro h
      simpa using Nat.dvd_sub hd h
    · intro h
      simpa using Nat.dvd_sub hd h
  by_cases hn : P ∣ n
  · simp [hn,he.mpr hn]
  · have hv : ¬P ∣ (-(n : ZMod q)).val := fun h => hn (he.mp h)
    simp [hn,hv]

/-- Actual Möbius inversion after the code. -/
def decoded (D : Finset ℕ) (c : ℕ → ℂ) : ℕ → ℂ := inverseRows (gammaCode D c)

/-- All counts, proper powers and finite heads are joined exactly. -/
theorem decoded_eq_dilations (D : Finset ℕ) (c : ℕ → ℂ)
    (hD : ∀ P∈D,0<P) (n : ℕ) :
    decoded D c n=∑ P∈D,c P*(zetaDilationCoefficient P mangoldt n+
      if n=P then (Real.log P : ℂ) else 0) := by
  unfold decoded inverseRows gammaCode
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro P hP
  symm
  rw [←inverseRows_maskedLog (hD P hP),inverseRows,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

/-- Entire finite dilation multiplier; all its signs remain joined. -/
def multiplier (D : Finset ℕ) (c : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑ P∈D,c P*zetaPrimeFeature s P

/-- Entire finite head from the literal logarithmic product rule. -/
def head (D : Finset ℕ) (c : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑ P∈D,c P*(Real.log P : ℂ)*zetaPrimeFeature s P

/-- The only singular channel is the OLD logarithmic zeta derivative. -/
def response (D : Finset ℕ) (c : ℕ → ℂ) (s : ℂ) : ℂ :=
  multiplier D c s*(-logDeriv riemannZeta s)+head D c s

/-- Genuine Euler identity with the actual complete finite head and
all original proper-prime-power coefficients retained. -/
theorem decoded_euler (D : Finset ℕ) (c : ℕ → ℂ) (hD : ∀ P∈D,0<P)
    {s : ℂ} (hs : 1<s.re) : LSeries (decoded D c) s=response D c s := by
  have hm := (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).LSeriesHasSum
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs] at hm
  change LSeriesHasSum mangoldt s (-deriv riemannZeta s/riemannZeta s) at hm
  have hc : decoded D c=∑ P∈D,c P • (zetaDilationCoefficient P mangoldt+
      zetaFiniteCoefficient {P} (fun _ => (Real.log P : ℂ))) := by
    funext n
    rw [decoded_eq_dilations D c hD]
    simp only [Pi.smul_apply,smul_eq_mul,Pi.add_apply,Finset.sum_apply,
      zetaFiniteCoefficient,Finset.mem_singleton]
  have hp (P : ℕ) (hP : P∈D) :=
    ((LSeriesHasSum_zetaDilationCoefficient (hD P hP) (by simp [mangoldt]) hm).add
      (LSeriesHasSum_zetaFiniteCoefficient {P} (fun _ => (Real.log P : ℂ))
        (by simpa using (hD P hP).ne) s)).smul (c P)
  rw [hc,LSeries_sum (fun P hP => (hp P hP).LSeriesSummable)]
  have he : ∀ P∈D,LSeries (c P • (zetaDilationCoefficient P mangoldt+
      zetaFiniteCoefficient {P} (fun _ => (Real.log P : ℂ)))) s=
        c P*(zetaPrimeFeature s P*(-logDeriv riemannZeta s)+
          (Real.log P : ℂ)*zetaPrimeFeature s P) := by
    intro P hP
    rw [(hp P hP).LSeries_eq]
    simp only [zetaFiniteDirichletSeries,Finset.sum_singleton,logDeriv_apply,neg_div]
  trans ∑ P∈D,c P*(zetaPrimeFeature s P*(-logDeriv riemannZeta s)+
    (Real.log P : ℂ)*zetaPrimeFeature s P)
  · exact Finset.sum_congr rfl he
  · unfold response multiplier head
    rw [Finset.sum_mul,←Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun _ _ => by ring)

/-- Complete cofactor-compatible phase before the ACTUAL inverse. -/
def phasedDecoded (D : Finset ℕ) (c : ℕ → ℂ) (y : ℝ) (n : ℕ) : ℂ :=
  ∑ da∈n.divisorsAntidiagonal,(ArithmeticFunction.moebius da.1 : ℂ)*
    primePhase y da.1*(primePhase y da.2*gammaCode D c da.2)

theorem phasedDecoded_eq (D : Finset ℕ) (c : ℕ → ℂ) (y : ℝ) (n : ℕ) :
    phasedDecoded D c y n=primePhase y n*decoded D c n := by
  rw [phasedDecoded,decoded,inverseRows,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro da hda
  have he := (Nat.mem_divisorsAntidiagonal.mp hda).1
  have hp : primePhase y da.1*primePhase y da.2=primePhase y n := by
    rw [←primePhase_mul y (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hda |>.bot_lt)
      (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hda |>.bot_lt),he]
  calc
    _ = (primePhase y da.1*primePhase y da.2)*
      ((ArithmeticFunction.moebius da.1 : ℂ)*gammaCode D c da.2) := by ring
    _ = _ := by rw [hp]

/-- Exact literal cutoff, arbitrary correlated row weight and full
phase. The finite head has no hidden or completed endpoint. -/
theorem native_mask_eq (D : Finset ℕ) (c : ℕ → ℂ) (hD : ∀ P∈D,0<P)
    (X : ℕ) (y : ℝ) (weight : ℕ → ℂ) :
    (∑ n∈Finset.Icc 1 X,weight n*phasedDecoded D c y n)=
      ∑ P∈D,c P*((∑ n∈Finset.Icc 1 X,
        weight n*primePhase y n*zetaDilationCoefficient P mangoldt n)+
          if P≤X then weight P*primePhase y P*(Real.log P : ℂ) else 0) := by
  classical
  simp_rw [phasedDecoded_eq,decoded_eq_dilations D c hD,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro P hP
  have hhead : (∑ n∈Finset.Icc 1 X,
      weight n*primePhase y n*(if n=P then (Real.log P : ℂ) else 0)) =
        if P≤X then weight P*primePhase y P*(Real.log P : ℂ) else 0 := by
    simp_rw [mul_ite,mul_zero]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_Icc,show 1≤P by exact hD P hP,true_and]
  rw [mul_add,Finset.mul_sum]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  have he (n : ℕ) : weight n*(primePhase y n*(c P*zetaDilationCoefficient P mangoldt n))=
      c P*(weight n*primePhase y n*zetaDilationCoefficient P mangoldt n) := by ring
  have hf (n : ℕ) : weight n*(primePhase y n*(c P*(if n=P then (Real.log P : ℂ) else 0)))=
      c P*(weight n*primePhase y n*(if n=P then (Real.log P : ℂ) else 0)) := by ring
  simp_rw [he,hf]
  rw [←Finset.mul_sum,←Finset.mul_sum,hhead]

/-- Full phase on the genuine Euler domain; continuation is not called
a convergent literal prime series outside that domain. -/
theorem phasedDecoded_euler (D : Finset ℕ) (c : ℕ → ℂ) (hD : ∀ P∈D,0<P)
    {s : ℂ} (hs : 1<s.re) (y : ℝ) :
    LSeries (phasedDecoded D c y) s=response D c (s+I*y) := by
  have he : phasedDecoded D c y=fun n => decoded D c n*primePhase y n := by
    funext n
    rw [phasedDecoded_eq,mul_comm]
  rw [he,LSeries_primePhase,decoded_euler D c hD (by simpa using hs)]

theorem multiplier_analytic (D : Finset ℕ) (c : ℕ → ℂ) (s : ℂ) :
    AnalyticAt ℂ (multiplier D c) s := by
  unfold multiplier zetaPrimeFeature
  fun_prop

theorem head_analytic (D : Finset ℕ) (c : ℕ → ℂ) (s : ℂ) :
    AnalyticAt ℂ (head D c) s := by
  unfold head zetaPrimeFeature
  fun_prop

/-- Every surviving singularity is the selected OLD zero, with actual
multiplicity and the entire signed dilation multiplier. -/
theorem actual_zero_source (D : Finset ℕ) (c : ℕ → ℂ) (rho : NontrivialZetaZero) :
    Tendsto (fun s => (s-rho.1)*response D c s) (𝓝[≠] rho.1)
      (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ)*multiplier D c rho.1)) := by
  have hz : Tendsto (fun s : ℂ => s-rho.1) (𝓝[≠] rho.1) (𝓝 0) := by
    simpa using (show Tendsto (fun s : ℂ => s-rho.1) (𝓝[≠] rho.1) (𝓝 (rho.1-rho.1)) from
      (continuous_id.sub continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have ht := (((multiplier_analytic D c rho.1).continuousAt.tendsto.mono_left
    nhdsWithin_le_nhds).mul (ArithmeticOperatorFullRamanujanAudit.tendsto_restored_zero_source rho)).add
      (hz.mul ((head_analytic D c rho.1).continuousAt.tendsto.mono_left nhdsWithin_le_nhds))
  simp only [zero_mul,add_zero] at ht
  convert ht using 1
  · funext s
    unfold response
    ring
  · congr 1
    ring

/-- The literal divisor-form Ramanujan coefficients, fixed before any
estimate; this is not a tuned free profile. -/
def ramanujanCoefficients (q P : ℕ) : ℂ :=
  (P : ℂ)*(ArithmeticFunction.moebius (q/P) : ℂ)

/-- Exact identification with the actual Ramanujan-coded Gamma row. -/
theorem gammaCode_ramanujan {q : ℕ} (hq : 0<q) (n : ℕ) :
    gammaCode q.divisors (ramanujanCoefficients q) n=
      (ramanujanDivisor q n : ℂ)*(Real.log n : ℂ) := by
  classical
  have he : q.divisors.filter (fun P => P ∣ n)=(Nat.gcd q n).divisors := by
    ext P
    simp only [Finset.mem_filter,Nat.mem_divisors,Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨⟨hP,_⟩,hn⟩
      exact ⟨⟨hP,hn⟩,(Nat.gcd_pos_of_pos_left n hq).ne'⟩
    · rintro ⟨⟨hP,hn⟩,_⟩
      exact ⟨⟨hP,hq.ne'⟩,hn⟩
  unfold gammaCode maskedLog
  simp_rw [mul_ite,mul_zero]
  rw [←Finset.sum_filter,he,←Finset.sum_mul]
  congr 1
  simp only [ramanujanDivisor,Int.cast_sum,Int.cast_mul,Int.cast_natCast,
    ramanujanCoefficients]

private theorem feature_one {P : ℕ} (hP : 0<P) :
    zetaPrimeFeature 1 P=(P : ℂ)⁻¹ := by
  have he : Complex.exp ((Real.log P : ℝ) : ℂ)=(P : ℂ) := by
    rw [←Complex.ofReal_exp,Real.exp_log (by exact_mod_cast hP)]
    norm_cast
  simp only [zetaPrimeFeature,one_mul,Complex.exp_neg,he]

private theorem feature_add (s t : ℂ) (P : ℕ) :
    zetaPrimeFeature s P*zetaPrimeFeature t P=zetaPrimeFeature (s+t) P := by
  unfold zetaPrimeFeature
  rw [←Complex.exp_add]
  congr 1
  ring

private theorem reflected_feature {q P : ℕ} (hq : 0<q) (hP : P∈q.divisors) (s : ℂ) :
    (P : ℂ)*zetaPrimeFeature s P=
      (q : ℂ)*zetaPrimeFeature s q*zetaPrimeFeature (1-s) (q/P) := by
  have hP0 := Nat.pos_of_mem_divisors hP
  have hd := Nat.dvd_of_mem_divisors hP
  have ha0 : 0<q/P := Nat.div_pos (Nat.le_of_dvd hq hd) hP0
  have hqeq := Nat.mul_div_cancel' hd
  have hf := feature_add s (1-s) (q/P)
  rw [show s+(1-s)=1 by ring,feature_one ha0] at hf
  have hqC : (q : ℂ)=(P : ℂ)*((q/P : ℕ) : ℂ) := by exact_mod_cast hqeq.symm
  have hqF : zetaPrimeFeature s q=zetaPrimeFeature s P*zetaPrimeFeature s (q/P) := by
    conv_lhs => rw [←hqeq]
    exact CoprimeEulerPhase.feature_mul s hP0 ha0
  symm
  rw [hqC,hqF]
  calc
    _ = ((P : ℂ)*zetaPrimeFeature s P)*
      ((q/P : ℕ) : ℂ)*(zetaPrimeFeature s (q/P)*zetaPrimeFeature (1-s) (q/P)) := by ring
    _ = _ := by rw [hf]; simp [ha0.ne']

/-- Exact all-divisor multiplier including every complementary divisor.
This is the fixed code's full source, not a norm or prime-class allowance. -/
theorem ramanujan_multiplier_eq {q : ℕ} (hq : 0<q) (s : ℂ) :
    multiplier q.divisors (ramanujanCoefficients q) s=
      (q : ℂ)*zetaPrimeFeature s q*zetaCoprimeEulerFactor q (1-s) := by
  unfold multiplier ramanujanCoefficients
  have he (P : ℕ) (hP : P∈q.divisors) :
      (P : ℂ)*(ArithmeticFunction.moebius (q/P) : ℂ)*zetaPrimeFeature s P=
        ((q : ℂ)*zetaPrimeFeature s q)*
          ((ArithmeticFunction.moebius (q/P) : ℂ)*zetaPrimeFeature (1-s) (q/P)) := by
    rw [mul_right_comm,reflected_feature hq hP]
    ring
  have hh := Finset.sum_congr rfl he
  rw [hh,←Finset.mul_sum]
  congr 1
  unfold zetaCoprimeEulerFactor zetaFiniteDirichletSeries
  rw [←Nat.sum_divisorsAntidiagonal (fun P a =>
    (ArithmeticFunction.moebius a : ℂ)*zetaPrimeFeature (1-s) a),
    Nat.sum_divisorsAntidiagonal' (fun P a =>
      (ArithmeticFunction.moebius a : ℂ)*zetaPrimeFeature (1-s) a)]

/-- Every nonunit squarefree modulus keeps EVERY actual off-line source.
The factor cannot vanish because each complementary Euler factor has
prime-feature norm strictly below one. -/
theorem ramanujan_multiplier_ne_zero {q : ℕ} (hq : Squarefree q)
    {s : ℂ} (hs : s.re<1) :
    multiplier q.divisors (ramanujanCoefficients q) s≠0 := by
  rw [ramanujan_multiplier_eq (Nat.pos_of_ne_zero hq.ne_zero),
    CoprimeEulerPhase.coprimeEuler_eq_product hq]
  apply mul_ne_zero
  · exact mul_ne_zero (Nat.cast_ne_zero.mpr hq.ne_zero) (Complex.exp_ne_zero _)
  · apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    have hl : 0<Real.log (p : ℝ) :=
      Real.log_pos (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt)
    have hnorm : ‖zetaPrimeFeature (1-s) p‖<1 := by
      rw [norm_zetaPrimeFeature,zetaPrimeExpWeight]
      exact Real.exp_lt_one_iff.mpr (by simp only [Complex.sub_re,Complex.one_re]; nlinarith)
    intro hz
    have hn := congrArg norm (sub_eq_zero.mp hz)
    simp only [norm_one] at hn
    linarith

theorem ramanujan_actual_source_ne_zero {q : ℕ} (hq : Squarefree q)
    (rho : NontrivialZetaZero) :
    -(analyticZetaZeroMultiplicity rho : ℂ)*
      multiplier q.divisors (ramanujanCoefficients q) rho.1≠0 :=
  mul_ne_zero (ArithmeticOperatorFullRamanujanAudit.restored_source_ne_zero rho)
    (ramanujan_multiplier_ne_zero hq (NontrivialZetaZero.re_lt_one rho))

/-- Nonunit Ramanujan coding kills the exact pole multiplier, not the
matched zero multiplier. -/
theorem ramanujan_multiplier_one {q : ℕ} (hq : 0<q) (hq1 : q≠1) :
    multiplier q.divisors (ramanujanCoefficients q) 1=0 := by
  rw [ramanujan_multiplier_eq hq,feature_one hq]
  have hsum : (∑ d∈q.divisors,(ArithmeticFunction.moebius d : ℂ))=0 := by
    have h := congrArg (fun f : ArithmeticFunction ℂ => f q)
      (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℂ))
    rw [ArithmeticFunction.coe_mul_zeta_apply] at h
    simpa only [ArithmeticFunction.one_apply,ite_eq_right hq1,ArithmeticFunction.intCoe_apply] using h
  simp [zetaCoprimeEulerFactor,zetaFiniteDirichletSeries,zetaPrimeFeature,hsum]

/-- An actual analytic pole-cleared germ, including every regular
cross-term and finite head. No density residue is silently left behind. -/
theorem response_analytic_at_pole (D : Finset ℕ) (c : ℕ → ℂ)
    (hcenter : multiplier D c 1=0) :
    ∃ E : ℂ → ℂ, AnalyticAt ℂ E 1 ∧ response D c =ᶠ[𝓝[≠] (1 : ℂ)] E := by
  let H : ℂ → ℂ := logDeriv riemannZeta₁
  have hH : AnalyticAt ℂ H 1 := by
    exact ((differentiable_riemannZeta₁).analyticAt 1).deriv.div
      ((differentiable_riemannZeta₁).analyticAt 1) (by simp)
  have hM := multiplier_analytic D c (1 : ℂ)
  have hJ : AnalyticAt ℂ (dslope (multiplier D c) 1) 1 := by
    obtain ⟨p,hp⟩ := hM
    exact ⟨p.fslope,hp.has_fpower_series_dslope_fslope⟩
  have hne : ∀ᶠ s in 𝓝 (1 : ℂ),riemannZeta₁ s≠0 :=
    (differentiable_riemannZeta₁ 1).continuousAt.eventually_ne (by simp)
  refine ⟨fun s => dslope (multiplier D c) 1 s-multiplier D c s*H s+head D c s,
    (hJ.sub (hM.mul hH)).add (head_analytic D c 1),?_⟩
  filter_upwards [hne.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin]
    with s hs (hs1 : s≠1)
  have hz : riemannZeta s≠0 := by
    rw [riemannZeta_eq_inv_sub_mul hs1]
    exact mul_ne_zero (inv_ne_zero (sub_ne_zero.mpr hs1)) hs
  rw [response,neg_logDeriv_riemannZeta_eq_pole_sub hs1 hz,
    dslope_of_ne _ hs1,slope_def_field,hcenter]
  dsimp [H]
  ring

/-- At an actual zero a surviving fixed code is NOT analytic. Hence a
holomorphy/decay rescue of this response requires genuinely new input,
not another consequence of its exact Gamma/Möbius operator word. -/
theorem not_analyticAt_response_of_source (D : Finset ℕ) (c : ℕ → ℂ)
    (rho : NontrivialZetaZero) (hM : multiplier D c rho.1≠0) :
    ¬AnalyticAt ℂ (response D c) rho.1 := by
  intro ha
  have hz : Tendsto (fun s : ℂ => s-rho.1) (𝓝[≠] rho.1) (𝓝 0) := by
    simpa using (show Tendsto (fun s : ℂ => s-rho.1) (𝓝[≠] rho.1) (𝓝 (rho.1-rho.1)) from
      (continuous_id.sub continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hh := hz.mul (ha.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  simp only [zero_mul] at hh
  have he := tendsto_nhds_unique (actual_zero_source D c rho) hh
  exact mul_ne_zero (ArithmeticOperatorFullRamanujanAudit.restored_source_ne_zero rho) hM he

/-- Every squarefree Ramanujan word detects the same old divisor. The
literal dilated prime estimate needed to remove it remains independent. -/
theorem ramanujan_not_analyticAt_actual_zero {q : ℕ} (hq : Squarefree q)
    (rho : NontrivialZetaZero) :
    ¬AnalyticAt ℂ (response q.divisors (ramanujanCoefficients q)) rho.1 :=
  not_analyticAt_response_of_source _ _ rho
    (ramanujan_multiplier_ne_zero hq (NontrivialZetaZero.re_lt_one rho))

/-- The coded holomorphy criterion is exactly the old zero-free problem
on the strip. The operator word by itself supplies no independent signed
prime estimate. No exposure or simplicity assumption is needed. -/
theorem ramanujan_analytic_iff_nonvanishing {q : ℕ} (hq : Squarefree q)
    {s : ℂ} (hs0 : 0<s.re) (hs1 : s.re<1) :
    AnalyticAt ℂ (response q.divisors (ramanujanCoefficients q)) s ↔
      riemannZeta s≠0 := by
  have hsne : s≠1 := by intro h; simp [h] at hs1
  constructor
  · intro ha hz
    let rho : NontrivialZetaZero := ⟨s,hz,by
      rintro ⟨n,hn⟩
      have hh := congrArg Complex.re hn
      norm_num [Complex.mul_re] at hh
      nlinarith [Nat.cast_nonneg (α := ℝ) n],hsne⟩
    exact ramanujan_not_analyticAt_actual_zero hq rho ha
  · intro hz
    have hZ := analyticOn_riemannZeta s (by simpa using hsne)
    exact ((multiplier_analytic _ _ s).mul (hZ.deriv.div hZ hz).neg).add
      (head_analytic _ _ s)

/-- Free-column version of the SAME fixed Ramanujan word. Actual Gamma
equalities are required only at the actual specialization below. -/
def freeDecoded (p : ℕ) (w : ℕ → ℂ) : ℕ → ℂ :=
  inverseRows (fun n => (ramanujanDivisor p n : ℂ)*divisorObservation w n)

private theorem ramanujan_prime_ne_zero {p : ℕ} (hp : p.Prime) (n : ℕ) :
    (ramanujanDivisor p n : ℂ)≠0 := by
  rw [ArithmeticOperatorFullRamanujanAudit.ramanujanDivisor_prime hp]
  split_ifs
  · push_cast
    exact sub_ne_zero.mpr (by exact_mod_cast hp.ne_one)
  · norm_num

private theorem inverseRows_observation (g : ℕ → ℂ) {n : ℕ} (hn : 0<n) :
    inverseRows (divisorObservation g) n=g n :=
  (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := g) (g := divisorObservation g)).mp (fun _ _ => rfl) n hn

/-- Even one FIXED prime-modulus Ramanujan code leaves free input columns
surjective. This is not a control satisfying all actual Gamma data. -/
theorem exists_free_input_with_any_profile {p : ℕ} (hp : p.Prime) (g : ℕ → ℂ) :
    ∃ w : ℕ → ℂ,∀ n>0,freeDecoded p w n=g n := by
  let target : ℕ → ℂ := fun n => divisorObservation g n/(ramanujanDivisor p n : ℂ)
  refine ⟨inverseRows target,?_⟩
  intro n hn
  unfold freeDecoded inverseRows
  have he (da : ℕ × ℕ) (hda : da∈n.divisorsAntidiagonal) :
      (ramanujanDivisor p da.2 : ℂ)*divisorObservation (inverseRows target) da.2=
        divisorObservation g da.2 := by
    rw [observation_inverseRows target (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hda |>.bot_lt)]
    dsimp [target]
    exact mul_div_cancel₀ _ (ramanujan_prime_ne_zero hp da.2)
  have hh : (∑ da∈n.divisorsAntidiagonal,(ArithmeticFunction.moebius da.1 : ℂ)*
      ((ramanujanDivisor p da.2 : ℂ)*divisorObservation (inverseRows target) da.2))=
        inverseRows (divisorObservation g) n := by
    unfold inverseRows
    apply Finset.sum_congr rfl
    intro da hda
    have hi := he da hda
    unfold inverseRows at hi
    rw [hi]
  exact hh.trans (inverseRows_observation g hn)

/-- At the actual weights the free word is precisely the classified
Gamma inverse. No altered Möbius or prime coefficient is inserted. -/
theorem freeDecoded_actual {p : ℕ} (hp : p.Prime) :
    freeDecoded p (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))=
      decoded p.divisors (ramanujanCoefficients p) := by
  unfold freeDecoded decoded
  congr 1
  funext n
  rw [gammaCode_ramanujan hp.pos,divisorObservation_vonMangoldt]

end
end RiemannGaussian.ArithmeticOperatorRamanujanInverseAudit
