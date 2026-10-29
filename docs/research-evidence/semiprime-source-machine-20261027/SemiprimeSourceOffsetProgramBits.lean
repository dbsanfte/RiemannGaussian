/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceProgramBits
import RiemannGaussian.SemiprimeSourceOffsetHeight

/-! # Physical addressed instructions for the original finite source offset
The twelve literal instructions use only four-bit addresses. Their Safe
invariant is derived from ORIGINAL scale bounds and actual offset scratch,
not an advised intermediate fit. This does not replace the whole source caller.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace RiemannGaussian.SemiprimeSourceOffsetProgramBits
open scoped BigOperators
open SemiprimeRationalBits SemiprimeBitArithmetic
open SemiprimeSourceProgramBits SemiprimeSourceMemoryBits
open SemiprimeJetArrayHeight SemiprimeSourceOffsetHeight

/-- Literal four-bit addresses used by this fixed program. -/
def addr : ℕ → List Bool
  | 0 => [false,false,false,false]
  | 1 => [true,false,false,false]
  | 3 => [true,true,false,false]
  | 4 => [false,false,true,false]
  | 5 => [true,false,true,false]
  | 6 => [false,true,true,false]
  | 9 => [true,false,false,true]
  | 10 => [false,true,false,true]
  | 11 => [true,true,false,true]
  | 13 => [true,false,true,true]
  | _ => [false,false,false,false]

/-- Actual newest-first register program for y²M²/U+x²Qn²/r. -/
def code : List Instruction :=
  [⟨.mul,addr 1,addr 1⟩,⟨.mul,addr 0,addr 3⟩,⟨.mul,addr 0,addr 4⟩,
   ⟨.inv,addr 9,addr 9⟩,⟨.mul,addr 1,addr 0⟩,⟨.mul,addr 5,addr 5⟩,
   ⟨.mul,addr 0,addr 11⟩,⟨.mul,addr 0,addr 10⟩,⟨.mul,addr 0,addr 11⟩,
   ⟨.inv,addr 13,addr 13⟩,⟨.mul,addr 1,addr 0⟩,⟨.add,addr 6,addr 0⟩]

/-- Original semantic input registers; runtime inputs remain physical words. -/
def initialValues (M n r Q U : ℕ) (x y : ℚ) : List ℚ := [x,y,M,n,r,Q,U]

/-- The fixed program has exactly twelve original instructions. -/
theorem code_length : code.length=12 := rfl

/-- Every actual operand address is a literal four-bit string. -/
theorem code_addresses : ∀ i∈code,i.left.length≤4 ∧ i.right.length≤4 := by
  intro i hi
  simp only [code,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

/-- The mathematical evaluation of the SAME instruction list ends at the original offset. -/
theorem evaluate_head (M n r Q U : ℕ) (x y : ℚ) :
    (evaluate code (initialValues M n r Q U x y)).headD 0=
      y*y*(M:ℚ)*(M:ℚ)/(U:ℚ)+x*x*(Q:ℚ)*(n:ℚ)*(n:ℚ)/(r:ℚ) := by
  simp [evaluate,code,Instruction.value,Operation.value,addr,initialValues,bitValue,bitNat,div_eq_mul_inv]

/-- A scalar cap derived from original data suffices for physical truncation guards. -/
theorem fits_of_cap (q : ℚ) (H : ℕ) (hden : q.den≤H) (hnum : q.num.natAbs≤H) : Fits q (H+1) := by
  have h : H<2^(H+1) := by have hh := Nat.lt_two_pow_self (n:=H+1); omega
  exact ⟨hnum.trans_lt h,hden.trans_lt h⟩

/-- The only extra intermediates are reciprocal positive original natural dimensions. -/
theorem inverse_fits (C H : ℕ) (hC : 0<C) (hCH : C≤H) : Fits ((C:ℚ)⁻¹) (H+1) := by
  have hrep : Representation ((C:ℚ)⁻¹) C 1 := ⟨1,by simp [one_div],by simp⟩
  have h := representation_reduced_bound hC hrep
  exact fits_of_cap _ H (h.1.trans hCH) (h.2.trans (by omega))

/-- All twelve physical outputs fit from the ORIGINAL offset scratch theorem. -/
theorem code_safe (d B M n r Q : ℕ) (x y : ℚ) (hd : 0<d) (hr : 0<r)
    (hx : Representation x d B) (hy : Representation y d B) :
    Safe (height d B M n r Q (r^(2*Q))+1) code
      (initialValues M n r Q (r^(2*Q)) x y) := by
  let U := r^(2*Q)
  let H := height d B M n r Q U
  have hU : 0<U := pow_pos hr _
  have hs (q : ℚ) (hq : q∈scratch M n r Q U x y) : Fits q (H+1) :=
    fits_of_cap q H (scratch_bound d B M n r Q U x y hd hr hU hx hy q hq).1
      (scratch_bound d B M n r Q U x y hd hr hU hx hy q hq).2
  have hiU : Fits ((U:ℚ)⁻¹) (H+1) := inverse_fits U H hU (by unfold H height; omega)
  have hir : Fits ((r:ℚ)⁻¹) (H+1) := inverse_fits r H hr (by unfold H height; omega)
  change Safe (H+1) code (initialValues M n r Q U x y)
  simp only [code,Safe,Instruction.value,Operation.value,addr,initialValues,bitValue,bitNat,
    Bool.false_eq_true,ite_false,ite_true,List.getElem?_cons_zero,List.getElem?_cons_succ,
    Option.getD_some]
  repeat' first
    | exact hiU
    | exact hir
    | (apply hs; simp [scratch,div_eq_mul_inv])
    | apply And.intro
    | trivial

/-- Exact original register-bank size. -/
theorem initial_length (M n r Q U : ℕ) (x y : ℚ) :
    (initialValues M n r Q U x y).length=7 := rfl

/-- The actual physical first-register projection agrees with the semantic list projection. -/
theorem head_word_value (memory : List RationalWord) :
    (memory.headD zeroWord).value=(memory.map RationalWord.value).headD 0 := by
  cases memory with
  | nil => norm_num [zeroWord,RationalWord.value,SemiprimeBitIndexClipping.SignedWord.value,bitValue,bitNat]
  | cons w ws => rfl

/-- Public width derived from original scale data, not from an execution answer. -/
def width (d B M n r Q : ℕ) : ℕ := height d B M n r Q (r^(2*Q))+1

/-- The actual physical instruction run returns the original source offset and keeps
all word/scanned-memory costs. Initial word acquisition is explicitly separate. -/
theorem run_offset (d B M n r Q : ℕ) (x y : ℚ) (hd : 0<d) (hr : 0<r)
    (hx : Representation x d B) (hy : Representation y d B)
    (memory : List RationalWord) (hv : ∀ w∈memory,w.Valid)
    (hvalue : memory.map RationalWord.value=initialValues M n r Q (r^(2*Q)) x y)
    (hwidth : ∀ w∈memory,Width w (width d B M n r Q)) :
    let result := run (List.replicate (width d B M n r Q) false) code memory
    (result.memory.headD zeroWord).value=(SemiprimeMaterializedSourceWords.offsetRun M n r Q x y).value ∧
      (∀ w∈result.memory,w.Valid) ∧
      (∀ w∈result.memory,Width w (width d B M n r Q)) ∧
      result.memory.length=19 ∧
      result.clock ≤ 12*(stepBudget 19 (width d B M n r Q) 4+3)+1 := by
  let template := List.replicate (width d B M n r Q) false
  have hf : Safe template.length code (memory.map RationalWord.value) := by
    rw [hvalue,List.length_replicate]
    exact code_safe d B M n r Q x y hd hr hx hy
  have hc := run_correct template code memory hv hf
  have hw := run_width template code memory (by simpa only [template,List.length_replicate] using hwidth)
  have hm : memory.length=7 := by
    have h := congrArg List.length hvalue
    simpa only [List.length_map,initial_length] using h
  have hclock := run_clock template code memory 4
    (by simp only [template,List.length_replicate,width]; omega) (by decide)
    code_addresses (by simpa only [template,List.length_replicate] using hwidth)
  refine ⟨?_,hc.2,?_,?_,?_⟩
  · rw [head_word_value,hc.1,hvalue,evaluate_head]
    simp only [SemiprimeMaterializedSourceWords.offsetRun,SemiprimeMaterializedSourceWords.powNatRun_value]
  · simpa only [template,List.length_replicate] using hw
  · rw [run_length,hm,code_length]
  · simpa only [template,List.length_replicate,code_length,hm] using hclock

/-- Scheduled ORIGINAL scales discharge the fit invariant internally. -/
theorem caller_safe {I E : Type} {n r Q : ℕ} [NeZero r]
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) E r Q) (lam : ℕ) (hlam : 0<lam) :
    let x := (1/((r*lam:ℕ):ℚ))*(en.incidences.values.length:ℚ)/(en.types.values.length:ℚ)
    let y := (n:ℚ)/(2*(r:ℚ))
    Safe (width (r*lam*r^(2*Q)*(2*r))
      (en.incidences.values.length*(2*r)+n*(r*lam)*r^(2*Q)) en.incidences.values.length n r Q)
      code (initialValues en.incidences.values.length n r Q (r^(2*Q)) x y) := by
  have hs := caller_scale_representations en lam hlam
  have hr := NeZero.pos r
  exact code_safe _ _ _ n r Q _ _ (by positivity) (NeZero.pos r) hs.1 hs.2

end RiemannGaussian.SemiprimeSourceOffsetProgramBits
