/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetReadExecution
import RiemannGaussian.SemiprimeD1StackVertexProductPolynomial
import RiemannGaussian.SemiprimeD1StackAssignmentOrder
/-! # Exact padded ordinal-bank values, common width and byte inventory
These are specifications of the actual tally-controlled Body/Increment loop,
not an executed native range getter or a supplied ID list.
-/
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace RiemannGaussian.SemiprimeD1OrdinalBankSpec
open SemiprimeBitArithmetic (bitValue)
open SemiprimeD1StackAssignmentOrder (assignments remaining)
open SemiprimeD1TensorTapeCodec (vectorBits)

/-- Mathematical sequence of EXACTLY M repeated wrapped-counter states. -/
def words (M : ℕ) : List (List Bool) := assignments M (List.replicate M false)
/-- Proof-side actual selected padded word; the physical caller uses StackJetRead. -/
def idAt (M i : ℕ) : List Bool := ((words M)[i]?).getD []
/-- Physically allocated zero has numeric value zero, including zero width. -/
theorem zero_value (M : ℕ) : bitValue (List.replicate M false)=0 := by
  induction M with
  | zero => rfl
  | succ M ih => simp [List.replicate_succ,SemiprimeBitArithmetic.bitValue,SemiprimeBitArithmetic.bitNat,ih]
/-- The M-controlled loop never reaches binary capacity, even on its final increment. -/
theorem strict_capacity (M : ℕ) : M<2^M := by
  induction M with
  | zero => decide
  | succ M ih =>
    rw [pow_succ]
    have hp : (0:ℕ)<2^M := by positivity
    omega
/-- Exactly the acquired tally length, not 2^M assignments, is generated. -/
theorem length (M : ℕ) : (words M).length=M := SemiprimeD1StackAssignmentOrder.assignments_length _ _
/-- Exact ascending original ordinal order. -/
theorem values (M : ℕ) : (words M).map bitValue=List.range M := by
  have hn : M≤remaining (List.replicate M false) := by
    rw [SemiprimeD1StackAssignmentOrder.zero_remaining]
    exact (strict_capacity M).le
  simpa [words,zero_value,←List.range_eq_range'] using SemiprimeD1StackAssignmentOrder.assignments_values M (List.replicate M false) hn
/-- Every generated binary ID retains the SAME acquired width, not compact width. -/
theorem word_length (M : ℕ) (word : List Bool) (hw : word∈words M) : word.length=M := by
  simpa using SemiprimeD1StackAssignmentOrder.assignments_width M (List.replicate M false) word hw
/-- Actual nth ID's binary value is its canonical ordinal. -/
theorem id_value (M i : ℕ) (hi : i<M) : bitValue (idAt M i)=i := by
  have hir : i<(words M).length := by simpa only [length] using hi
  have h:=congrArg (fun xs:List ℕ=>(xs[i]?).getD 0) (values M)
  simpa [idAt,List.getElem?_map,List.getElem?_eq_getElem hir,List.getElem?_range hi] using h
/-- The actual nth payload has exactly the physically acquired common width. -/
theorem id_length (M i : ℕ) (hi : i<M) : (idAt M i).length=M := by
  have hir : i<(words M).length := by simpa only [length] using hi
  rw [idAt,List.getElem?_eq_getElem hir,Option.getD_some]
  exact word_length M _ (List.getElem_mem hir)
/-- Padded IDs are injective by their actual numeric values, NOT by compactness. -/
theorem id_eq_iff (M i j : ℕ) (hi : i<M) (hj : j<M) : idAt M i=idAt M j ↔ i=j := by
  constructor
  · intro h
    have hv:=congrArg bitValue h
    simpa only [id_value M i hi,id_value M j hj] using hv
  · intro h; subst j; rfl
/-- All ordinals are covered, including ordinal zero's all-false payload. -/
theorem id_mem (M i : ℕ) (hi : i<M) : idAt M i∈words M := by
  have hir : i<(words M).length := by simpa only [length] using hi
  rw [idAt,List.getElem?_eq_getElem hir,Option.getD_some]
  exact List.getElem_mem hir
/-- Actual output words have no duplicates despite their retained high zeros. -/
theorem nodup (M : ℕ) : (words M).Nodup := by
  apply List.Nodup.of_map (f:=bitValue)
  rw [values]
  exact List.nodup_range
/-- Every physically logged counter has a false overflow flag on its subsequent
actual Increment call; M<2^M licenses this, not an overflow/count answer. -/
theorem no_overflow (M : ℕ) (word : List Bool) (hw : word∈words M) :
    SemiprimeD1StackIncrement.overflow word=false := by
  have hv : bitValue word<M := by
    have hmem : bitValue word∈(words M).map bitValue := List.mem_map.mpr ⟨word,hw,rfl⟩
    rw [values] at hmem
    exact List.mem_range.mp hmem
  have hlen:=word_length M word hw
  have hb:=SemiprimeD1StackIncrement.value_balance word
  cases ho:SemiprimeD1StackIncrement.overflow word with
  | false => rfl
  | true =>
    rw [ho,hlen] at hb
    simp only [SemiprimeBitArithmetic.bitNat,ite_true] at hb
    have hc:=strict_capacity M
    omega
/-- Exact framed payload inventory of a repeated fixed-width counter prefix. -/
theorem assignment_bytes (n : ℕ) (word : List Bool) :
    (vectorBits (assignments n word)).length=2*n*word.length+2*n+1 := by
  induction n generalizing word with
  | zero => simp [assignments,vectorBits]
  | succ n ih =>
    simp only [assignments,vectorBits,List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length,ih,
      SemiprimeD1StackIncrement.wrapped_length]
    nlinarith
/-- Exact whole-bank bytes are quadratic in its ACTUALLY acquired tally length. -/
theorem bank_bytes (M : ℕ) : (vectorBits (words M)).length=2*M*M+2*M+1 := by
  simpa [words] using assignment_bytes M (List.replicate M false)
/-- Any actual scope sublist of this producer has the same honest quadratic
byte cap, without a supplied arbitrary-ID width or compactness assumption. -/
theorem sublist_bytes (M : ℕ) (ws : List (List Bool)) (hsub : ws.Sublist (words M)) :
    (vectorBits ws).length≤2*M*M+2*M+1 := by
  have hl : ws.length≤M := by simpa only [length] using hsub.length_le
  have hw : ∀w∈ws,w.length≤M := fun w h=> (word_length M w (hsub.subset h)).le
  have hb:=SemiprimeD1StackVertexProductPolynomial.vector_length ws M hw
  nlinarith

end RiemannGaussian.SemiprimeD1OrdinalBankSpec
