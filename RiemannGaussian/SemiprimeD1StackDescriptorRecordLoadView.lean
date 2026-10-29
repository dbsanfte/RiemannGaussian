/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackDescriptorRecord
/-! # Exact proof views of the physically loaded checker template -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackDescriptorRecordLoadView
open SemiprimeD1StackDescriptorRecord
variable {K L : Type} [DecidableEq K] (s : T.Static K L) (sourceMap : K→Option (Fin 6))
/-- Change only the actual checker template, retaining every other physical role. -/
def replaceTemplate (d : Stack K→List Bool) (template : K→List Bool) : Stack K→List Bool
  | .inl (.inl (.inr (.inl k)))=>template k
  | k=>d k
/-- Prefix of literal template positions already physically drained and loaded. -/
def loadPrefix (d : Stack K→List Bool) (n : Nat) : Stack K→List Bool :=
  replaceTemplate d (fun k=>if k∈s.roles.take n then selected sourceMap (fun i=>d (source i)) k else d (templateStack k))
/-- Every actual template field loaded from its selected physical source or empty. -/
def loaded (d : Stack K→List Bool) : Stack K→List Bool :=
  replaceTemplate d (selected sourceMap (fun i=>d (source i)))
/-- No template field is preloaded before the real loader executes. -/
theorem loadPrefix_zero (d : Stack K→List Bool) : loadPrefix s sourceMap d 0=d := by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rfl
      · rcases k with k|k
        · simp only [loadPrefix,replaceTemplate,List.take_zero,List.not_mem_nil,ite_false,templateStack,
            recordStack,R.tableStack,T.template]
        · rfl
    · rfl
  · rfl
/-- The compile-time inventory covers every physical template field. -/
theorem loadPrefix_full (d : Stack K→List Bool) : loadPrefix s sourceMap d s.roles.length=loaded sourceMap d := by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rfl
      · rcases k with k|k
        · simp only [loadPrefix,replaceTemplate,List.take_length,s.complete k,ite_true,loaded]
        · rfl
    · rfl
  · rfl
/-- One actual target write advances exactly one literal template position. -/
theorem loadPrefix_step (d : Stack K→List Bool) (p : Fin s.roles.length) :
    Function.update (loadPrefix s sourceMap d p.val) (templateStack (T.role s p))
      (selected sourceMap (fun i=>d (source i)) (T.role s p))=loadPrefix s sourceMap d (p.val+1) := by
  funext q
  rcases q with q|q
  · rcases q with q|q
    · rcases q with q|q
      · rw [Function.update_of_ne (by intro he;cases he)];rfl
      · rcases q with k|q
        · by_cases he:k=s.roles[p.val]
          · subst k
            change Function.update _ (templateStack s.roles[p.val]) _ (templateStack s.roles[p.val])=_
            rw [Function.update_self]
            simp only [loadPrefix,replaceTemplate,List.take_succ_eq_append_getElem p.isLt,List.mem_append,
              List.mem_cons,List.not_mem_nil,or_false,or_true,ite_true,T.role,templateStack,recordStack,R.tableStack,T.template]
          · have hn:templateStack k≠templateStack (T.role s p):=by
              intro h
              exact he (Sum.inl.inj (Sum.inr.inj (Sum.inl.inj (Sum.inl.inj h))))
            change Function.update _ (templateStack (T.role s p)) _ (templateStack k)=_
            rw [Function.update_of_ne hn]
            simp only [loadPrefix,replaceTemplate,List.take_succ_eq_append_getElem p.isLt,List.mem_append,
              List.mem_cons,List.not_mem_nil,or_false,he,or_false,templateStack,recordStack,R.tableStack,T.template]
        · rw [Function.update_of_ne (by intro he;cases he)];rfl
    · rw [Function.update_of_ne (by intro he;cases he)];rfl
  · rw [Function.update_of_ne (by intro he;cases he)];rfl
/-- Actual old words and physical descriptor fields are all charged. -/
def inventory [Fintype K] (d : Stack K→List Bool) : Nat :=∑k:Stack K,(d k).length
omit [DecidableEq K] in
/-- One physical word never exceeds the full actual input inventory. -/
theorem cell_le [Fintype K] (d : Stack K→List Bool) (k : Stack K) : (d k).length≤ inventory d := by
  unfold inventory
  exact Finset.single_le_sum (f:=fun k:Stack K=>(d k).length) (fun _ _=>Nat.zero_le _) (Finset.mem_univ k)
omit [DecidableEq K] in
/-- A source-selected field is bounded by the actual supplied six-word inventory. -/
theorem selected_le [Fintype K] (d : Stack K→List Bool) (k : K) :
    (selected sourceMap (fun i=>d (source i)) k).length≤ inventory d := by
  unfold selected
  cases sourceMap k with
  | none=>exact Nat.zero_le _
  | some i=>exact cell_le d (source i)
/-- Loaded and not-yet-loaded target words have the same actual inventory bound. -/
theorem prefix_cell_le [Fintype K] (d : Stack K→List Bool) (n : Nat) (k : K) :
    (loadPrefix s sourceMap d n (templateStack k)).length≤ inventory d := by
  change (if k∈s.roles.take n then selected sourceMap (fun i=>d (source i)) k else d (templateStack k)).length≤_
  split
  · exact selected_le sourceMap d k
  · exact cell_le d (templateStack k)
end RiemannGaussian.SemiprimeD1StackDescriptorRecordLoadView
