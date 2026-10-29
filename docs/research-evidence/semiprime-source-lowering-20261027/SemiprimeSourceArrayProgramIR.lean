/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceProgramBits
import RiemannGaussian.SemiprimeSourceCodeArrays

/-! # Stable-register scalar blocks for cached source coefficient arrays
Stable IDs are compiler metadata. Their physical newest-first addresses are
lowered separately; semantic environments below are proof specifications only.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RiemannGaussian.SemiprimeSourceArrayProgramIR
open scoped BigOperators
open SemiprimeRationalBits

/-- Scalar operation with compiler-generated stable register IDs. -/
structure Instruction where
  /-- Existing rational arithmetic operation. -/
  operation : Operation
  /-- First stable register ID. -/
  left : ℕ
  /-- Second stable register ID. -/
  right : ℕ

/-- Mathematical value of one generated stable-register operation. -/
def Instruction.value (i : Instruction) (env : ℕ → ℚ) : ℚ :=
  i.operation.value (env i.left) (env i.right)

/-- Proof semantics of the generated code, assigning successive fresh IDs. -/
def evaluate : List Instruction → ℕ → (ℕ → ℚ) → (ℕ → ℚ)
  | [],_,env => env
  | i::code,next,env => evaluate code (next+1) (Function.update env next (i.value env))

/-- Every source ID is strictly older than the current allocation frontier. -/
def WellFormed : ℕ → List Instruction → Prop
  | _,[] => True
  | next,i::code => i.left<next ∧ i.right<next ∧ WellFormed (next+1) code

/-- Concatenating well-formed code shifts only the fresh frontier. -/
theorem wellFormed_append (a b : List Instruction) (next : ℕ) :
    WellFormed next (a++b) ↔ WellFormed next a ∧ WellFormed (next+a.length) b := by
  induction a generalizing next with
  | nil => simp [WellFormed]
  | cons i a ih =>
    simp only [List.cons_append,WellFormed,ih,List.length_cons]
    have h : next+1+a.length=next+(a.length+1) := by omega
    rw [h]
    tauto

/-- Concatenating generated blocks preserves the exact fresh-register frontier. -/
theorem evaluate_append (a b : List Instruction) (next : ℕ) (env : ℕ → ℚ) :
    evaluate (a++b) next env=evaluate b (next+a.length) (evaluate a next env) := by
  induction a generalizing next env with
  | nil => simp [evaluate]
  | cons i a ih =>
    simp only [List.cons_append,evaluate,ih,List.length_cons]
    congr 1
    omega

/-- No generated block overwrites an earlier stable register. -/
theorem evaluate_old (code : List Instruction) (next k : ℕ) (env : ℕ → ℚ) (hk : k<next) :
    evaluate code next env k=env k := by
  induction code generalizing next env with
  | nil => rfl
  | cons i code ih =>
    rw [evaluate,ih (next+1) _ (by omega)]
    exact Function.update_of_ne (by omega : k≠next) _ _

/-- Exact last-register value of one emitted instruction. -/
theorem evaluate_single_new (i : Instruction) (next : ℕ) (env : ℕ → ℚ) :
    evaluate [i] next env next=i.value env := by simp [evaluate]

/-- The zeroId initial register or latest generated dot accumulator. -/
def accumulator (zeroId start len : ℕ) : ℕ := if len=0 then zeroId else start+2*len-1

/-- Two real operations per convolution term, retaining both product and sum. -/
def dotCode (zeroId start k : ℕ) (a b : ℕ → ℕ) : ℕ → List Instruction
  | 0 => []
  | len+1 =>
      dotCode zeroId start k a b len ++
        [⟨.mul,a len,b (k-len)⟩,⟨.add,start+2*len,accumulator zeroId start len⟩]

/-- Actual scalar instruction count of a generated dot prefix. -/
theorem dotCode_length (zeroId start k : ℕ) (a b : ℕ → ℕ) (len : ℕ) :
    (dotCode zeroId start k a b len).length=2*len := by
  induction len with
  | zero => rfl
  | succ len ih => simp only [dotCode,List.length_append,ih,List.length_cons,List.length_nil];omega

/-- The dot result ID is always below the resulting frontier. -/
theorem accumulator_lt (zeroId start len : ℕ) (hz : zeroId<start) :
    accumulator zeroId start len<start+2*len := by
  unfold accumulator
  split_ifs <;> omega

/-- Every actual dot block computes its precise original finite convolution prefix. -/
theorem dotCode_correct (zeroId start k len : ℕ) (a b : ℕ → ℕ) (env : ℕ → ℚ)
    (hz : zeroId<start) (he : env zeroId=0)
    (ha : ∀ i<len,a i<start) (hb : ∀ i<len,b (k-i)<start) :
    evaluate (dotCode zeroId start k a b len) start env (accumulator zeroId start len)=
      ∑ i∈Finset.range len,env (a i)*env (b (k-i)) := by
  induction len with
  | zero => simp [dotCode,evaluate,accumulator,he]
  | succ len ih =>
    have hprev := ih (fun i hi => ha i (by omega)) (fun i hi => hb i (by omega))
    rw [dotCode,evaluate_append,dotCode_length]
    let e := evaluate (dotCode zeroId start k a b len) start env
    have hA : e (a len)=env (a len) := evaluate_old _ start _ env (ha len (by omega))
    have hB : e (b (k-len))=env (b (k-len)) := evaluate_old _ start _ env (hb len (by omega))
    have hacc := accumulator_lt zeroId start len hz
    have hresult : accumulator zeroId start (len+1)=start+2*len+1 := by rw [accumulator,ite_eq_right (by omega)]; omega
    rw [hresult]
    simp only [evaluate,Instruction.value,Operation.value,Function.update_same]
    rw [Function.update_of_ne (by omega : accumulator zeroId start len≠start+2*len)]
    change e (a len)*e (b (k-len))+e (accumulator zeroId start len)=_
    change e (accumulator zeroId start len)=_ at hprev
    rw [hA,hB,hprev,Finset.sum_range_succ]
    ring

/-- Every source of the actual dot block is initialized, including zero-length dots. -/
theorem dotCode_wellFormed (zeroId start k len : ℕ) (a b : ℕ → ℕ)
    (hz : zeroId<start) (ha : ∀ i<len,a i<start) (hb : ∀ i<len,b (k-i)<start) :
    WellFormed start (dotCode zeroId start k a b len) := by
  induction len with
  | zero => trivial
  | succ len ih =>
    rw [dotCode,wellFormed_append,dotCode_length]
    refine ⟨ih (fun i hi => ha i (by omega)) (fun i hi => hb i (by omega)),?_⟩
    have hA := ha len (by omega)
    have hB := hb len (by omega)
    have hacc := accumulator_lt zeroId start len hz
    simp only [WellFormed]
    exact ⟨by omega,by omega,by omega,by omega,trivial⟩

end RiemannGaussian.SemiprimeSourceArrayProgramIR
