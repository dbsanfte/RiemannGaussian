/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorGammaTwistAudit
import RiemannGaussian.ArithmeticOperatorFloorInverseAudit
import RiemannGaussian.ZetaRieszPrimeCompletionPhase
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Complete prime-power binomial unit rows: source gate

Actual binomial residues, rather than only their valuations, are retained.
For the aligned row p^r-1, they form the exact two-letter parity alphabet.
Centering that alphabet leaves only an inverse-denominator endpoint. This
does not classify unaligned common rows or cross-prime upper digit residues.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped BigOperators Classical Topology
namespace RiemannGaussian.ArithmeticOperatorLucasUnitAudit
open Complex Filter ArithmeticOperatorGammaTwistAudit SuzukiCarryCorrelation

/-- Every residue in an actual aligned prime-power row, including its unit endpoints. -/
def unitRow (p r k : ℕ) : ZMod p := ((p^r-1).choose k : ℕ)

/-- Exact unit information beyond Kummer valuations; no row is approximated. -/
theorem unitRow_eq_sign {p : ℕ} (hp : p.Prime) (r : ℕ) {k : ℕ} (hk : k<p^r) :
    unitRow p r k=(-1 : ZMod p)^k := by
  induction k with
  | zero => simp [unitRow]
  | succ k ih =>
    have hpw : 0<p^r := Nat.pow_pos hp.pos
    have hdiv := hp.dvd_choose_pow (by omega : k+1≠0) (by omega : k+1≠p^r)
    have hz : (((p^r).choose (k+1) : ℕ) : ZMod p)=0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hdiv
    have he : (p^r).choose (k+1)=
        (p^r-1).choose k+(p^r-1).choose (k+1) := by
      nth_rw 1 [show p^r=p^r-1+1 by omega]
      exact Nat.choose_succ_succ _ _
    rw [he,Nat.cast_add] at hz
    have hprev := ih (by omega)
    unfold unitRow at hprev ⊢
    rw [hprev] at hz
    rw [pow_succ]
    linear_combination hz

/-- Full residue code, not merely a multiplicative character. -/
def rowTrace (p r : ℕ) (f : ZMod p → ℂ) : ℂ :=
  (∑ k∈Finset.range (p^r),f (unitRow p r k))/((p^r : ℕ) : ℂ)

/-- The two-letter mean retained by the complete unit alphabet. -/
def alphabetMean {p : ℕ} (f : ZMod p → ℂ) : ℂ := (f 1+f (-1))/2

/-- All powers of a sign, with literal finite row length. -/
def signSum {p : ℕ} (n : ℕ) (f : ZMod p → ℂ) : ℂ :=
  ∑ k∈Finset.range n,f ((-1 : ZMod p)^k)

theorem signSum_even {p : ℕ} (H : ℕ) (f : ZMod p → ℂ) :
    signSum (2*H) f=(H : ℂ)*(f 1+f (-1)) := by
  induction H with
  | zero => simp [signSum]
  | succ H ih =>
    rw [show 2*(H+1)=2*H+1+1 by omega,signSum,Finset.sum_range_succ,
      Finset.sum_range_succ]
    change signSum (2*H) f+f ((-1 : ZMod p)^(2*H))+
      f ((-1 : ZMod p)^(2*H+1))=((H+1 : ℕ) : ℂ)*(f 1+f (-1))
    rw [ih,pow_add,pow_mul]
    norm_num
    ring

theorem signSum_odd {p : ℕ} (H : ℕ) (f : ZMod p → ℂ) :
    signSum (2*H+1) f=(H : ℂ)*(f 1+f (-1))+f 1 := by
  rw [signSum,Finset.sum_range_succ]
  change signSum (2*H) f+f ((-1 : ZMod p)^(2*H))=_
  rw [signSum_even,pow_mul]
  norm_num

/-- The exact endpoint left by the full residue trace, including the even-prime case. -/
theorem rowTrace_eq {p : ℕ} (hp : p.Prime) (r : ℕ) (f : ZMod p → ℂ) :
    rowTrace p r f=alphabetMean f+
      if p^r%2=1 then (f 1-f (-1))/(2*((p^r : ℕ) : ℂ)) else 0 := by
  have hs : (∑ k∈Finset.range (p^r),f (unitRow p r k))=signSum (p^r) f := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [unitRow_eq_sign hp r (Finset.mem_range.mp hk)]
  have hshape := Nat.mod_add_div (p^r) 2
  have hmod := Nat.mod_lt (p^r) (by norm_num : (0 : ℕ)<2)
  unfold rowTrace
  rw [hs]
  by_cases ho : p^r%2=1
  · rw [ite_eq_left ho,show p^r=2*(p^r/2)+1 by omega,signSum_odd]
    have hn : ((2*(p^r/2)+1 : ℕ) : ℂ)≠0 := by
      exact_mod_cast (by omega : 2*(p^r/2)+1≠0)
    unfold alphabetMean
    field_simp [hn]
    push_cast
    ring
  · rw [ite_eq_right ho,show p^r=2*(p^r/2) by omega,signSum_even]
    have hn : ((p^r/2 : ℕ) : ℂ)≠0 := by
      have hpow := Nat.pow_pos hp.pos (n := r)
      have h : p^r/2≠0 := by omega
      exact_mod_cast h
    unfold alphabetMean
    push_cast
    field_simp [hn]
    ring

/-- Uniformly bounded complete unit codes leave only an inverse-length endpoint. -/
theorem norm_rowTrace_sub_mean {p : ℕ} (hp : p.Prime) (r : ℕ)
    (f : ZMod p → ℂ) (hf : ∀ x,‖f x‖≤1) :
    ‖rowTrace p r f-alphabetMean f‖≤((p^r : ℕ) : ℝ)⁻¹ := by
  rw [rowTrace_eq hp]
  by_cases ho : p^r%2=1
  · rw [ite_eq_left ho,add_sub_cancel_left,norm_div]
    have hd : ‖(2*((p^r : ℕ) : ℂ))‖=2*((p^r : ℕ) : ℝ) := by
      rw [norm_mul,Complex.norm_natCast]
      norm_num
    rw [hd]
    have hn : ‖f 1-f (-1)‖≤2 :=
      (norm_sub_le _ _).trans (by linarith [hf 1,hf (-1)])
    calc
      _ ≤ 2/(2*((p^r : ℕ) : ℝ)) := div_le_div_of_nonneg_right hn (by positivity)
      _ = _ := by field_simp
  · rw [ite_eq_right ho,add_zero,sub_self,norm_zero]
    positivity

/-- Same literal row shape at a generic integer label; no prime-power replacement is made. -/
def labelTrace (n : ℕ) (f : ZMod n.minFac → ℂ) : ℂ :=
  (∑ k∈Finset.range n,f (((n-1).choose k : ℕ) : ZMod n.minFac))/(n : ℂ)

theorem labelTrace_primePow_bound {n : ℕ} (hn : IsPrimePow n)
    (f : ZMod n.minFac → ℂ) (hf : ∀ x,‖f x‖≤1) :
    ‖labelTrace n f-alphabetMean f‖≤(n : ℝ)⁻¹ := by
  obtain ⟨r,_,_,he⟩ := (isPrimePow_nat_iff_bounded_log_minFac _).mp hn
  have hp := Nat.minFac_prime hn.ne_one
  have htrace : labelTrace n f=rowTrace n.minFac r f := by
    unfold labelTrace rowTrace unitRow
    rw [←he]
  rw [htrace]
  simpa only [←he] using norm_rowTrace_sub_mean hp r f hf

/-- Additional residue information after alphabet centering; full prime-power phase retained. -/
def centeredPacket (X : ℕ) (y : ℝ) (code : ∀ n : ℕ,ZMod n.minFac → ℂ) : ℂ :=
  ∑ n∈Finset.Icc 1 X,(ArithmeticFunction.vonMangoldt n : ℂ)*primePhase y n*
    (labelTrace n (code n)-alphabetMean (code n))

/-- The joined residue packet is source-small at every positive power scale. -/
theorem norm_centeredPacket_le (X : ℕ) (y : ℝ)
    (code : ∀ n : ℕ,ZMod n.minFac → ℂ)
    (hc : ∀ n∈Finset.Icc 1 X,∀ x,‖code n x‖≤1) :
    ‖centeredPacket X y code‖≤Real.log X*(1+Real.log X) := by
  have hterm (n : ℕ) (hn : n∈Finset.Icc 1 X) :
      ‖(ArithmeticFunction.vonMangoldt n : ℂ)*primePhase y n*
        (labelTrace n (code n)-alphabetMean (code n))‖≤
        Real.log X*(n : ℝ)⁻¹ := by
    obtain ⟨hn0,hnX⟩ := Finset.mem_Icc.mp hn
    by_cases hz : ArithmeticFunction.vonMangoldt n=0
    · simp only [hz,Complex.ofReal_zero,zero_mul,norm_zero]
      positivity
    have hpp : IsPrimePow n := by
      by_contra h
      exact hz (ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr h)
    rw [norm_mul,norm_mul,Complex.norm_real,
      Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,norm_primePhase,mul_one]
    have hl : ArithmeticFunction.vonMangoldt n≤Real.log X :=
      ArithmeticFunction.vonMangoldt_le_log.trans
        (Real.log_le_log (by exact_mod_cast hn0) (by exact_mod_cast hnX))
    exact mul_le_mul hl (labelTrace_primePow_bound hpp (code n) (hc n hn))
      (norm_nonneg _) (Real.log_natCast_nonneg X)
  unfold centeredPacket
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ n∈Finset.Icc 1 X,Real.log X*(n : ℝ)⁻¹ := Finset.sum_le_sum hterm
    _ = Real.log X*(harmonic X : ℝ) := by
      rw [←Finset.mul_sum,harmonic_eq_sum_Icc]
      simp only [Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
    _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log X) (Real.log_natCast_nonneg X)

/-- Explicit all-order budget with arbitrary moving residue and height masks. -/
theorem norm_dyadic_centeredPacket_le (J : ℕ) (y : ℝ)
    (code : ∀ n : ℕ,ZMod n.minFac → ℂ)
    (hc : ∀ n∈Finset.Icc 1 (2^J),∀ x,‖code n x‖≤1) :
    ‖centeredPacket (2^J) y code‖≤(1+Real.log 2)^2*((J+1 : ℕ) : ℝ)^2 := by
  apply (norm_centeredPacket_le _ _ _ hc).trans
  have hl : 0≤Real.log (2 : ℝ) := (Real.log_pos (by norm_num : (1 : ℝ)<2)).le
  simp only [Nat.cast_pow,Nat.cast_ofNat,Real.log_pow]
  push_cast
  have hJ : 0≤(J : ℝ) := Nat.cast_nonneg J
  have hprod : (J : ℝ)*Real.log 2≤(1+Real.log 2)*(J+1) := by nlinarith
  have hprod1 : 1+(J : ℝ)*Real.log 2≤(1+Real.log 2)*(J+1) := by nlinarith
  calc
    _ ≤ ((1+Real.log 2)*(J+1))*((1+Real.log 2)*(J+1)) :=
      mul_le_mul hprod hprod1 (by positivity) (by positivity)
    _ = _ := by ring

/-- No bounded centered complete unit code can see a positive-power zero source, even when moving. -/
theorem tendsto_scaled_centeredPacket (y : ℕ → ℝ)
    (code : ∀ _J n : ℕ,ZMod n.minFac → ℂ)
    (hc : ∀ J n,n∈Finset.Icc 1 (2^J) → ∀ x,‖code J n x‖≤1)
    {beta : ℝ} (hb : 0<beta) :
    Tendsto (fun J : ℕ => ((Real.exp (-beta*Real.log 2)^J : ℝ) : ℂ)*
      centeredPacket (2^J) (y J) (code J)) atTop (𝓝 0) := by
  let a := Real.exp (-beta*Real.log 2)
  have ha : 0<a := Real.exp_pos _
  have ha1 : a<1 := Real.exp_lt_one_iff.mpr
    (mul_neg_of_neg_of_pos (neg_neg_of_pos hb) (Real.log_pos (by norm_num)))
  have ht := (ArithmeticOperatorFloorInverseAudit.tendsto_shifted_polynomial_geometric
    2 ha ha1).const_mul ((1+Real.log 2)^2)
  apply squeeze_zero_norm (fun J => ?_) (by simpa only [mul_zero] using ht)
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (pow_nonneg ha.le _)]
  calc
    _ ≤ a^J*((1+Real.log 2)^2*((J+1 : ℕ) : ℝ)^2) :=
      mul_le_mul_of_nonneg_left (norm_dyadic_centeredPacket_le J _ _ (hc J)) (pow_nonneg ha.le _)
    _ = _ := by ring

/-- Complete residue coding before centering, with a fully arbitrary signed outer array. -/
def fullPacket (X : ℕ) (w : ℕ → ℂ) (code : ∀ n : ℕ,ZMod n.minFac → ℂ) : ℂ :=
  ∑ n∈Finset.Icc 1 X,w n*labelTrace n (code n)

/-- The uncancelled two-letter scalar profile; no primality estimate is hidden here. -/
def bulkPacket (X : ℕ) (w : ℕ → ℂ) (code : ∀ n : ℕ,ZMod n.minFac → ℂ) : ℂ :=
  ∑ n∈Finset.Icc 1 X,w n*alphabetMean (code n)

theorem fullPacket_actual_eq (X : ℕ) (y : ℝ) (code : ∀ n : ℕ,ZMod n.minFac → ℂ) :
    fullPacket X (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)*primePhase y n) code=
      bulkPacket X (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)*primePhase y n) code+
        centeredPacket X y code := by
  unfold fullPacket bulkPacket centeredPacket
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  ring

theorem alphabetMean_const {p : ℕ} (c : ℂ) : alphabetMean (p := p) (fun _ => c)=c := by
  unfold alphabetMean
  ring

theorem labelTrace_const {n : ℕ} (hn : 0<n) (c : ℂ) :
    labelTrace n (fun _ => c)=c := by
  unfold labelTrace
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  have hnz : (n : ℂ)≠0 := by exact_mod_cast hn.ne'
  field_simp

/-- Arbitrary scalar profiles remain realizable; uncentered free residue coding adds no constraint. -/
theorem fullPacket_constCode (X : ℕ) (w f : ℕ → ℂ) :
    fullPacket X w (fun n _ => f n)=∑ n∈Finset.Icc 1 X,w n*f n := by
  unfold fullPacket
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 := (Finset.mem_Icc.mp hn).1
  rw [labelTrace_const (by omega : 0<n)]

/-- The constant full unit trace keeps the actual ordinary-prime factorial transform. -/
def constantUnitMoment (k : ℕ) (s : ℂ) : ℂ :=
  ∑' n,if n.Prime then (ArithmeticFunction.vonMangoldt n : ℂ)*
    labelTrace n (fun _ => 1)*zetaPrimeLogKernel k s n else 0

theorem constantUnitMoment_eq (k : ℕ) (s : ℂ) :
    constantUnitMoment k s=zetaOrdinaryPrimeLogMoment k s := by
  unfold constantUnitMoment zetaOrdinaryPrimeLogMoment
  apply tsum_congr
  intro n
  by_cases hn : n.Prime
  · rw [ite_eq_left hn,ite_eq_left hn,labelTrace_const hn.pos,mul_one]
  · rw [ite_eq_right hn,ite_eq_right hn]

/-- Uncentered coding retains every exposed actual zero and its multiplicity, without gaining a bound. -/
theorem constantUnit_actual_exposed_source (rho : NontrivialZetaZero)
    (hrho : 1/2<rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero,tau≠rho →
      3/2-rho.1.re<‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖) :
    Tendsto (fun k : ℕ => ((3/2-rho.1.re : ℝ) : ℂ)^(k+1)*
      constantUnitMoment k (3/2+Complex.I*(rho.1.im : ℂ))) atTop
      (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  simp only [constantUnitMoment_eq]
  exact ZetaRieszPrimeCompletionPhase.tendsto_ordinary_prime_source rho hrho hexposed

/-- A common unaligned row retains a genuine upper-digit binomial residue modulo this prime. -/
theorem commonRow_first_digit {p a : ℕ} (hp : p.Prime) (ha : 0<a) (k : ℕ) :
    (((p*a-1).choose k : ℕ) : ZMod p)=
      (-1 : ZMod p)^(k%p)*(((a-1).choose (k/p) : ℕ) : ZMod p) := by
  have : Fact p.Prime := ⟨hp⟩
  have hp0 := hp.pos
  have haeq : a=a-1+1 := by omega
  have hsplit : p*a-1=p*(a-1)+(p-1) := by
    nth_rw 1 [haeq]
    rw [Nat.mul_add,Nat.mul_one]
    omega
  have hrem : (p*a-1)%p=p-1 := by
    rw [hsplit,Nat.add_comm,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (by omega)]
  have hquot : (p*a-1)/p=a-1 := by
    rw [hsplit,Nat.add_comm,Nat.add_mul_div_left _ _ hp.pos,
      Nat.div_eq_of_lt (by omega),zero_add]
  have hc := (ZMod.natCast_eq_natCast_iff _ _ _).mpr
    (Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := p*a-1) (k := k) (p := p))
  rw [hrem,hquot,Nat.cast_mul] at hc
  have hs : (((p-1).choose (k%p) : ℕ) : ZMod p)=(-1 : ZMod p)^(k%p) := by
    simpa only [unitRow,pow_one] using
      unitRow_eq_sign hp 1 (by simpa using Nat.mod_lt k hp.pos)
  rw [hs] at hc
  exact hc

/-- Dropping the cofactor residue is already false for two genuine distinct primes. -/
theorem crossPrime_upper_factor_essential :
    (((3*5-1).choose 6 : ℕ) : ZMod 3)=0 ∧
      (-1 : ZMod 3)^(6%3)=1 ∧
      (((3*5-1).choose 6 : ℕ) : ZMod 3)≠(-1 : ZMod 3)^(6%3) := by
  decide

end RiemannGaussian.ArithmeticOperatorLucasUnitAudit

#lint+ in RiemannGaussian.ArithmeticOperatorLucasUnitAudit

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut reports : Array Json := #[]
  for (n,ci) in env.constants.toList do
    if env.isImportedConst n then continue
    declarations := declarations + 1
    if ci.isAxiom then throwError "Project-defined axiom: {n}"
    let axs ← Lean.collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in {n}: {ax}"
    if ci.isTheorem then theorems := theorems + 1
    reports := reports.push (Json.mkObj [("declaration",toJson n.toString),
      ("isTheorem",toJson ci.isTheorem),("axioms",toJson (axs.map Name.toString))])
  unless declarations > 0 do throwError "Empty Lucas unit audit."
  logInfo m!"Lucas unit audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-lucas-unit"
  IO.FS.writeFile ".lake/arithmetic-operator-lucas-unit/axioms.json"
    (Json.mkObj [("scope",toJson "complete aligned unit traces and common-row upper-digit audit"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
