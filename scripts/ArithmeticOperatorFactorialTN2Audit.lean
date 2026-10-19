/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorTwistedBulkAudit
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Full factorial-ratio adjacent TN2 forces a monotone divisor profile

The literal floor-factorial prefix and divisor profile are joined exactly.
Every adjacent minor has the sign of two successive divisor profiles.
The actual matched-phase REAL deformation has negative minors beyond every
head at every nonzero height: a negative weight at p² forces a profile
descent. This is not a source-annihilation claim or a rejection of uses of
untwisted total positivity. No monotone-multiplicative rigidity is imported.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option warningAsError true
noncomputable section
open scoped BigOperators
namespace OpenAIReview.FactorialTN2
open RiemannGaussian

/-- Exact divisor increment of a real prime-power observation. -/
def profile (w : ℕ → ℝ) (n : ℕ) : ℝ := ∑ d∈n.divisors,w d

/-- Integrated divisor observations, with both integer endpoints retained. -/
def logPrefix (w : ℕ → ℝ) (N : ℕ) : ℝ := ∑ n∈Finset.Icc 1 N,profile w n

/-- Positive exponential factorial sequence. -/
def sequence (w : ℕ → ℝ) (N : ℕ) : ℝ := Real.exp (logPrefix w N)

/-- The full positive factorial-ratio kernel. -/
def kernel (w : ℕ → ℝ) (a b : ℕ) : ℝ :=
  sequence w (a+b)/(sequence w a*sequence w b)

/-- A literal adjacent two-by-two minor of the full kernel. -/
def adjacentMinor (w : ℕ → ℝ) (a b : ℕ) : ℝ :=
  kernel w a b*kernel w (a+1) (b+1)-kernel w a (b+1)*kernel w (a+1) b

/-- The real part of the actual denominator-phase deformation. -/
def phaseWeight (y : ℝ) (d : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt d*Real.cos (y*Real.log d)

/-- The actual complex prime-power phase remains in every floor layer. -/
def complexPrefix (y : ℝ) (N : ℕ) : ℂ :=
  ∑ d∈Finset.Icc 1 N,((N/d : ℕ) : ℂ)*
    ((ArithmeticFunction.vonMangoldt d : ℂ)*SuzukiCarryCorrelation.primePhase y d)

/-- Exponentiate the phased log-factorial ratio before taking its modulus. -/
def phaseKernel (y : ℝ) (a b : ℕ) : ℂ :=
  Complex.exp (complexPrefix y (a+b)-complexPrefix y a-complexPrefix y b)

/-- The integrated profile is exactly the literal integer floor prefix. -/
theorem logPrefix_eq_floor (w : ℕ → ℝ) (N : ℕ) :
    logPrefix w N=∑ d∈Finset.Icc 1 N,(N/d : ℕ)*w d := by
  have hs:=sum_Icc_divisorsAntidiagonal_eq_sum_divided_prefix N
    (fun d _ => (w d : ℂ))
  have hc (n : ℕ) : (∑ p∈n.divisorsAntidiagonal,(w p.1 : ℂ))=(profile w n : ℂ) := by
    rw [Nat.sum_divisorsAntidiagonal (fun d _ => (w d : ℂ))]
    simp [profile]
  simp_rw [hc] at hs
  simp only [Finset.sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul] at hs
  unfold logPrefix
  exact_mod_cast hs

/-- Every sequence entry is strictly positive, for arbitrary real weights. -/
theorem sequence_pos (w : ℕ → ℝ) (N : ℕ) : 0<sequence w N := Real.exp_pos _

/-- The exact quotient jump is the exponential divisor profile. -/
theorem sequence_succ (w : ℕ → ℝ) (N : ℕ) :
    sequence w (N+1)=sequence w N*Real.exp (profile w (N+1)) := by
  unfold sequence logPrefix
  rw [Finset.sum_Icc_succ_top (by omega),Real.exp_add]

/-- The real deformation is the real part of the ACTUAL complex floor sum. -/
theorem complexPrefix_re (y : ℝ) (N : ℕ) :
    (complexPrefix y N).re=logPrefix (phaseWeight y) N := by
  rw [logPrefix_eq_floor]
  unfold complexPrefix
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [phaseWeight,SuzukiCarryCorrelation.primePhase,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,Complex.natCast_re,Complex.natCast_im,
    Complex.exp_re,Complex.neg_re,Complex.neg_im,Complex.mul_im,
    Complex.I_re,Complex.I_im,mul_zero,zero_mul,one_mul,zero_add,
    sub_zero,neg_zero,neg_mul,Real.exp_zero,Real.cos_neg]

/-- The positive kernel under audit is literally the modulus of the
phase-preserving exponentiated factorial ratio. It retains height dependence. -/
theorem norm_phaseKernel (y : ℝ) (a b : ℕ) :
    ‖phaseKernel y a b‖=kernel (phaseWeight y) a b := by
  simp only [phaseKernel,Complex.norm_exp,Complex.sub_re,complexPrefix_re,kernel,sequence]
  rw [show logPrefix (phaseWeight y) (a+b)-logPrefix (phaseWeight y) a-
      logPrefix (phaseWeight y) b=logPrefix (phaseWeight y) (a+b)-
      (logPrefix (phaseWeight y) a+logPrefix (phaseWeight y) b) by ring,
    Real.exp_sub,Real.exp_add]

/-- Untwisted actual prime-power data still give the literal factorial. -/
theorem sequence_mangoldt (N : ℕ) : sequence ArithmeticFunction.vonMangoldt N=N.factorial := by
  unfold sequence
  rw [logPrefix_eq_floor]
  change Real.exp (SuzukiIntegerCarry.factorialObservation ArithmeticFunction.vonMangoldt N)=_
  rw [SuzukiIntegerCarry.factorialObservation_vonMangoldt,Real.exp_log (by positivity)]

/-- The untwisted exact integer divisor profile is log n, not a free model. -/
theorem profile_mangoldt (n : ℕ) : profile ArithmeticFunction.vonMangoldt n=Real.log n := by
  exact ArithmeticFunction.vonMangoldt_sum

/-- Exact positive-factor decomposition of the adjacent minor. -/
theorem adjacentMinor_factorization (w : ℕ → ℝ) (a b : ℕ) :
    adjacentMinor w a b=
      (sequence w (a+b)^2*Real.exp (profile w (a+b+1))/
        (sequence w a*sequence w (a+1)*sequence w b*sequence w (b+1)))*
      (Real.exp (profile w (a+b+2))-Real.exp (profile w (a+b+1))) := by
  have ha:sequence w a≠0 := (sequence_pos w a).ne'
  have ha1:sequence w (a+1)≠0 := (sequence_pos w (a+1)).ne'
  have hb:sequence w b≠0 := (sequence_pos w b).ne'
  have hb1:sequence w (b+1)≠0 := (sequence_pos w (b+1)).ne'
  unfold adjacentMinor kernel
  rw [show a+1+(b+1)=a+b+2 by omega,show a+(b+1)=a+b+1 by omega,
    show a+1+b=a+b+1 by omega]
  rw [show a+b+2=(a+b+1)+1 by omega,sequence_succ w (a+b+1),sequence_succ w (a+b)]
  field_simp

/-- Adjacent TN2 is EXACTLY successive monotonicity of the actual profile. -/
theorem adjacentMinor_nonneg_iff (w : ℕ → ℝ) (a b : ℕ) :
    0≤adjacentMinor w a b ↔ profile w (a+b+1)≤profile w (a+b+2) := by
  rw [adjacentMinor_factorization]
  have hc : 0<sequence w (a+b)^2*Real.exp (profile w (a+b+1))/
      (sequence w a*sequence w (a+1)*sequence w b*sequence w (b+1)) := by
    have h1:=sequence_pos w (a+b)
    have h2:=sequence_pos w a
    have h3:=sequence_pos w (a+1)
    have h4:=sequence_pos w b
    have h5:=sequence_pos w (b+1)
    positivity
  rw [mul_nonneg_iff_of_pos_left hc,sub_nonneg,Real.exp_le_exp]

/-- The strict negative-minor criterion keeps both physical indices. -/
theorem adjacentMinor_neg_iff (w : ℕ → ℝ) (a b : ℕ) :
    adjacentMinor w a b<0 ↔ profile w (a+b+2)<profile w (a+b+1) := by
  simpa only [not_le] using not_congr (adjacentMinor_nonneg_iff w a b)

/-- All adjacent untwisted factorial minors remain nonnegative. The
failure proved below concerns the matched-phase extension. -/
theorem adjacentMinor_mangoldt_nonneg (a b : ℕ) :
    0≤adjacentMinor ArithmeticFunction.vonMangoldt a b := by
  rw [adjacentMinor_nonneg_iff,profile_mangoldt,profile_mangoldt]
  apply Real.log_le_log
  · exact_mod_cast (by omega : 0<a+b+1)
  · exact_mod_cast (by omega : a+b+1≤a+b+2)

/-- The exact prime-square jump retains the proper-power coefficient. -/
theorem profile_prime_square_sub {p : ℕ} (hp : p.Prime) (w : ℕ → ℝ) :
    profile w (p^2)-profile w p=w (p^2) := by
  have h1 : profile w p=w 1+w p := by simp [profile,hp.divisors,hp.ne_one.symm]
  rw [h1]
  simp only [profile,Nat.sum_divisors_prime_pow hp,Finset.sum_range_succ,
    Finset.sum_range_zero,pow_zero,pow_one,zero_add]
  ring

/-- A profile drop after a cutoff forces a successive descent after it.
This step is ordinary order logic, not an assumed arithmetic estimate. -/
theorem exists_profile_descent (w : ℕ → ℝ) (T p q : ℕ)
    (hTp : T≤p) (hpq : p≤q) (hdrop : profile w q<profile w p) :
    ∃ n : ℕ,T≤n ∧ profile w (n+1)<profile w n := by
  by_contra hnot
  have hs : ∀ n≥T,profile w n≤profile w (n+1) := by
    intro n hn
    by_contra hh
    exact hnot ⟨n,hn,lt_of_not_ge hh⟩
  have hm:=monotoneOn_nat_Ici_of_le_succ hs
  have hle:=hm hTp (hTp.trans hpq) hpq
  exact (not_le_of_gt hdrop) hle

/-- One negative proper-power weight gives a negative minor with BOTH
row and column indices beyond the prescribed physical head. -/
theorem exists_negativeMinor_of_prime_square {p : ℕ} (hp : p.Prime)
    (w : ℕ → ℝ) (H : ℕ) (hpH : 2*H+3≤p) (hw : w (p^2)<0) :
    ∃ a b : ℕ,H<a ∧ H<b ∧ adjacentMinor w a b<0 := by
  have hdrop : profile w (p^2)<profile w p := by
    have he:=profile_prime_square_sub hp w
    linarith
  have hpp : p≤p^2 := by have h:=hp.two_le; nlinarith
  obtain ⟨n,hn,hd⟩:=exists_profile_descent w (2*H+3) p (p^2) hpH hpp hdrop
  refine ⟨H+1,n-(H+2),by omega,by omega,?_⟩
  apply (adjacentMinor_neg_iff _ _ _).mpr
  convert hd using 1 <;> congr 1 <;> omega

/-- The square order has its own literal doubled phase, not a base-prime
phase silently reused at every valuation order. -/
theorem phaseWeight_prime_square {p : ℕ} (hp : p.Prime) (y : ℝ) :
    phaseWeight y (p^2)=Real.log p*Real.cos ((2*y)*Real.log p) := by
  simp only [phaseWeight,ArithmeticFunction.vonMangoldt_apply_pow (by decide : (2 : ℕ)≠0),
    ArithmeticFunction.vonMangoldt_apply_prime hp,Nat.cast_pow,Real.log_pow]
  congr 2
  ring

/-- Actual prime-square phase weights are negative beyond every head,
using the repository's unconditional prime-window theorem. -/
theorem exists_negative_phase_square (y : ℝ) (hy : y≠0) (T : ℕ) :
    ∃ p : ℕ,T<p ∧ p.Prime ∧ phaseWeight y (p^2)<0 := by
  have hy2 : 2*y≠0 := mul_ne_zero (by norm_num) hy
  obtain ⟨p,hpT,hp,hn⟩:=ArithmeticOperatorTwistedBulkAudit.exists_negative_prime_diagonal_above hy2 T
  rw [ArithmeticOperatorTwistedBulkAudit.prime_diagonal_re hp] at hn
  exact ⟨p,hpT,hp,by rwa [phaseWeight_prime_square hp]⟩

/-- No finite head deletion makes the positive modulus-type factorial
deformation adjacent-TN2 at any actual nonzero height. -/
theorem exists_negative_phaseMinor (y : ℝ) (hy : y≠0) (H : ℕ) :
    ∃ a b : ℕ,H<a ∧ H<b ∧ adjacentMinor (phaseWeight y) a b<0 := by
  obtain ⟨p,hpH,hp,hw⟩:=exists_negative_phase_square y hy (2*H+3)
  exact exists_negativeMinor_of_prime_square hp (phaseWeight y) H hpH.le hw

/-- Even taking entry moduli cannot restore full factorial TN2: this
literal modulus matrix has negative ordered minors beyond every head. -/
theorem exists_negative_modulus_minor (y : ℝ) (hy : y≠0) (H : ℕ) :
    ∃ a b : ℕ,H<a ∧ H<b ∧
      ‖phaseKernel y a b‖*‖phaseKernel y (a+1) (b+1)‖-
        ‖phaseKernel y a (b+1)‖*‖phaseKernel y (a+1) b‖<0 := by
  obtain ⟨a,b,ha,hb,hm⟩:=exists_negative_phaseMinor y hy H
  exact ⟨a,b,ha,hb,by simpa only [norm_phaseKernel,adjacentMinor] using hm⟩

end OpenAIReview.FactorialTN2

#lint+ in OpenAIReview.FactorialTN2

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut reports : Array Json := #[]
  for (n,ci) in env.constants.toList do
    if env.isImportedConst n then continue
    declarations := declarations+1
    if ci.isAxiom then throwError "Project-defined axiom: {n}"
    let axs ← Lean.collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in {n}: {ax}"
    if ci.isTheorem then theorems := theorems+1
    reports := reports.push (Json.mkObj [("declaration",toJson n.toString),
      ("isTheorem",toJson ci.isTheorem),("axioms",toJson (axs.map Name.toString))])
  unless declarations>0 do throwError "Empty factorial-TN2 audit."
  logInfo m!"Factorial-TN2 audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-factorial-total-positive-gate"
  IO.FS.writeFile ".lake/arithmetic-operator-factorial-total-positive-gate/axioms.json"
    (Json.mkObj [("scope",toJson "exact factorial-profile/minor criterion and cofinal actual nonzero-height failure; no source annihilation or RH estimate"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
