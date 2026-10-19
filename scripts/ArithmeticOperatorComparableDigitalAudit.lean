/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import scripts.ArithmeticOperatorDigitalCarryAudit
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# The comparable binary/ternary completion gate

Both codes use literal factorial valuations. The common CRT completion
period of positive retained windows is at least three times the physical
cutoff X=H^2 when K>=H/2. Thus an O(period) completion allowance cannot be
source-small. This is NOT a lower bound on the actual signed discrepancy
or a no-go for a direct Beatty/correlation estimate. The exact first
nonaligned overlap is nonzero, so separate block means cannot be multiplied.
-/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
open scoped BigOperators
open Filter
namespace OpenAIReview.ComparableDigital

/-- The literal ternary digit sum. -/
def ternaryDigits (n : ℕ) : ℕ := (Nat.digits 3 n).sum

/-- Legendre identifies the code with actual integer factorial data. -/
theorem ternaryDigits_eq_factorial (n : ℕ) :
    ternaryDigits n=n-2*n.factorial.factorization 3 := by
  have h:=Nat.sub_one_mul_factorization_factorial (n:=n) (by norm_num : Nat.Prime 3)
  have hle:=Nat.digit_sum_le 3 n
  norm_num only at h
  unfold ternaryDigits
  omega

/-- A proper ternary phase, unlike the degenerate parity of ternary digits. -/
def ternaryCode (z : ℂ) (n : ℕ) : ℂ := z^ternaryDigits n

/-- This is an equality of the original arithmetic code, not a free sequence. -/
theorem ternaryCode_eq_factorial (z : ℂ) (n : ℕ) :
    ternaryCode z n=z^(n-2*n.factorial.factorization 3) := by
  rw [ternaryCode,ternaryDigits_eq_factorial]

/-- The two high windows are kept at their independently prescribed scales. -/
def mixedCode (z : ℂ) (a b n : ℕ) : ℂ :=
  (DigitalCarry.highCode a n : ℂ)*ternaryCode z (n/3^b)

/-- Finite high windows used in the standard completion argument. -/
def windowCode (z : ℂ) (a b ell m n : ℕ) : ℂ :=
  (DigitalCarry.epsilon ((n/2^a)%(2^ell)) : ℂ)*
    ternaryCode z ((n/3^b)%(3^m))

/-- On its untruncated physical range the finite window is exactly the
original two-factor factorial code. -/
theorem windowCode_eq_mixedCode (z : ℂ) {a b ell m n : ℕ}
    (hn : n<2^(a+ell)) (hn' : n<3^(b+m)) :
    windowCode z a b ell m n=mixedCode z a b n := by
  have h2 : n/2^a<2^ell := by
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos a)).mpr
    simpa [pow_add,Nat.mul_comm] using hn
  have h3 : n/3^b<3^m := by
    apply (Nat.div_lt_iff_lt_mul (by positivity : 0<3^b)).mpr
    simpa [pow_add,Nat.mul_comm] using hn'
  simp [windowCode,mixedCode,DigitalCarry.highCode,Nat.mod_eq_of_lt h2,
    Nat.mod_eq_of_lt h3]

/-- The binary high window has the stated native period. -/
theorem binary_window_period (a ell n : ℕ) :
    ((n+2^(a+ell))/2^a)%(2^ell)=(n/2^a)%(2^ell) := by
  rw [pow_add,Nat.add_mul_div_left _ _ (Nat.two_pow_pos a),Nat.add_mod_right]

/-- The ternary high window has its independent native period. -/
theorem ternary_window_period (b m n : ℕ) :
    ((n+3^(b+m))/3^b)%(3^m)=(n/3^b)%(3^m) := by
  rw [pow_add,Nat.add_mul_div_left _ _ (by positivity : 0<3^b),Nat.add_mod_right]

/-- Common period used by ordinary CRT completion of lambda/mu retained
high digits. It is not asserted to be the least period of the product. -/
def crtPeriod (a b ell m : ℕ) : ℕ := Nat.lcm (2^(a+ell)) (3^(b+m))

/-- Coprime radix powers give the exact completion period. -/
theorem crtPeriod_eq (a b ell m : ℕ) :
    crtPeriod a b ell m=2^(a+ell)*3^(b+m) := by
  apply Nat.Coprime.lcm_eq_mul
  exact Nat.Coprime.pow_left _ (Nat.Coprime.pow_right _ (by norm_num : Nat.Coprime 2 3))

/-- Even one retained digit in each radix exceeds the critical physical
length. This concerns the CRT allowance, not the signed sum itself. -/
theorem crtPeriod_ge_three_square {a b ell m : ℕ}
    (hscale : 2^a≤2*3^b) (hell : 0<ell) (hm : 0<m) :
    3*(2^a)^2≤crtPeriod a b ell m := by
  rw [crtPeriod_eq,pow_add,pow_add]
  have he : 2≤2^ell := by
    exact (show (2 : ℕ)^1≤2^ell from Nat.pow_le_pow_right (by norm_num) hell)
  have hf : 3≤3^m := by
    exact (show (3 : ℕ)^1≤3^m from Nat.pow_le_pow_right (by norm_num) hm)
  calc
    3*(2^a)^2 ≤ 6*2^a*3^b := by
      have h:=Nat.mul_le_mul_left (3*2^a) hscale
      nlinarith [h]
    _ = (2^a*2)*(3^b*3) := by ring
    _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_left _ he) (Nat.mul_le_mul_left _ hf)

/-- The normalized whole-period error budget stays at least three. -/
theorem crtPeriod_ratio_ge_three {a b ell m : ℕ}
    (hscale : 2^a≤2*3^b) (hell : 0<ell) (hm : 0<m) :
    (3 : ℝ)≤(crtPeriod a b ell m : ℝ)/((2^a : ℕ) : ℝ)^2 := by
  have hH : (0 : ℝ)<(2^a : ℕ) := by exact_mod_cast Nat.two_pow_pos a
  apply (le_div_iff₀ (sq_pos_of_pos hH)).mpr
  exact_mod_cast crtPeriod_ge_three_square hscale hell hm

/-- Growing digit windows cannot make this particular completion budget
o(X), regardless of how their depths are chosen. -/
theorem not_tendsto_crtPeriod_ratio_zero (a b ell m : ℕ → ℕ)
    (hscale : ∀ j,2^(a j)≤2*3^(b j)) (hell : ∀ j,0<ell j) (hm : ∀ j,0<m j) :
    ¬Tendsto (fun j => (crtPeriod (a j) (b j) (ell j) (m j) : ℝ)/
      ((2^(a j) : ℕ) : ℝ)^2) atTop (nhds 0) := by
  intro ht
  have h : (3 : ℝ)≤0 := ge_of_tendsto ht (Filter.Eventually.of_forall (fun j =>
    crtPeriod_ratio_ge_three (hscale j) (hell j) (hm j)))
  norm_num at h

/-- The native first overlap has weight 3,-1,-2 in the ternary sectors. -/
theorem first_overlap (z : ℂ) :
    (∑ n∈Finset.range 8,mixedCode z 2 1 n)=3-z-2*z^2 := by
  norm_num [mixedCode,DigitalCarry.highCode,DigitalCarry.epsilon,
    DigitalCarry.digitSum,ternaryCode,ternaryDigits,Finset.sum_range_succ]
  ring

/-- Summing each separate digit period to zero is invalid on the joined
physical overlap: the exact answer is 5+z for a proper cubic root. -/
theorem first_overlap_eq {z : ℂ} (hz : z^2+z+1=0) :
    (∑ n∈Finset.range 8,mixedCode z 2 1 n)=5+z := by
  rw [first_overlap]
  linear_combination -2*hz

/-- This overlap is genuinely nonzero; no floating lower bound is used. -/
theorem first_overlap_ne_zero {z : ℂ} (hz : z^2+z+1=0) :
    (∑ n∈Finset.range 8,mixedCode z 2 1 n)≠0 := by
  rw [first_overlap_eq hz]
  intro h
  have he : z= -5 := by linear_combination h
  rw [he] at hz
  norm_num at hz

/-- The literal complex phase used by the ternary factorial code. -/
def omega : ℂ := Complex.exp (2*Real.pi*Complex.I/3)

/-- Its polynomial relation follows from the exact primitive-root theorem. -/
theorem omega_cubic : omega^2+omega+1=0 := by
  have h:= (Complex.isPrimitiveRoot_exp 3 (by norm_num)).geom_sum_eq_zero (by norm_num)
  simpa [omega,Finset.sum_range_succ,add_comm,add_left_comm,add_assoc] using h

/-- The arithmetic nonaligned overlap is nonzero at the actual phase. -/
theorem native_first_overlap_ne_zero :
    (∑ n∈Finset.range 8,mixedCode omega 2 1 n)≠0 :=
  first_overlap_ne_zero omega_cubic

end OpenAIReview.ComparableDigital

#lint+ in OpenAIReview.ComparableDigital

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
  unless declarations>0 do throwError "Empty comparable-digital audit."
  logInfo m!"Comparable-digital audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-comparable-digital-formal"
  IO.FS.writeFile ".lake/arithmetic-operator-comparable-digital-formal/axioms.json"
    (Json.mkObj [("scope",toJson "actual factorial codes, nonzero finite overlap and failed whole-period allowance; no signed-discrepancy lower bound or comparable-source theorem"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
