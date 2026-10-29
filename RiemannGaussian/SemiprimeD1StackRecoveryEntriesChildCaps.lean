/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryEntriesEncoding
/-! # Semantic child-cache byte caps independent of recursive child runtime
Only actual child count/rank/precision and actual coefficient-word length caps
enter these estimates. No polynomial of a subtree clock is substituted.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackRecoveryEntriesChildCaps
open SemiprimeD1StackRecoveryEntriesEncoding
open SemiprimeD1TensorTapeCodec (vectorBits)
/-- Actual coefficient bytes are bounded by physical coefficient count and semantic precision. -/
theorem payload_sum (words:List (List Bool)) (P:Nat) (hp:∀word∈words,word.length ≤P):
    (words.map List.length).sum ≤words.length*P:=by
  induction words with
  | nil=>simp only [List.map_nil,List.sum_nil,List.length_nil,Nat.zero_mul,Nat.le_refl]
  | cons word words ih=>
    have h:=hp word (List.mem_cons_self)
    have ht:=ih (fun w hw=>hp w (List.mem_cons_of_mem word hw))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega
/-- Actual encoded child row has a count/rank/precision cap, without any child-clock premise. -/
theorem vector_length (words:List (List Bool)) (R P:Nat) (hr:words.length ≤R)
    (hp:∀word∈words,word.length ≤P):(vectorBits words).length ≤2*R*(P+1)+1:=by
  have h:=payload_sum words P hp
  have hm:=Nat.mul_le_mul_right P hr
  rw [SemiprimeD1TensorTapeCodec.vectorBits_length]
  nlinarith only [h,hm,hr]
/-- Whole nested physical child tape has a fixed polynomial semantic bound in count, old rank and working precision. -/
theorem child_tape_length (children:List (List (List Bool))) (Q R P:Nat) (hq:children.length ≤Q)
    (hr:∀row∈children,row.length ≤R) (hp:∀row∈children,∀word∈row,word.length ≤P):
    (childTape children).length ≤4*Q*R*(P+1)+4*Q+1:=by
  have h:=vector_length (children.map vectorBits) Q (2*R*(P+1)+1) (by simpa only [List.length_map] using hq) (by
    intro encoded he
    obtain ⟨row,hrow,rfl⟩:=List.mem_map.mp he
    exact vector_length row R P (hr row hrow) (hp row hrow))
  change (childTape children).length ≤_ at h
  nlinarith only [h]
/-- Every actual selected/default coefficient derives its width only from the semantic child precision cap. -/
theorem selected_child_length (children:List (List (List Bool))) (node index:List Bool) (P:Nat)
    (hp:∀row∈children,∀word∈row,word.length ≤P):
    (selectedChild children node index).length ≤P:=by
  unfold selectedChild
  cases hn:children[SemiprimeBitArithmetic.bitValue node]? with
  | none=>simp
  | some row=>
    simp only [Option.getD_some]
    cases hi:row[SemiprimeBitArithmetic.bitValue index]? with
    | none=>simp
    | some word=>exact hp row (List.mem_of_getElem? hn) word (List.mem_of_getElem? hi)
end RiemannGaussian.SemiprimeD1StackRecoveryEntriesChildCaps
