/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetBlocksFields
/-! # Complete actual rank-marker coefficient scan, including source EOF padding
Every processed field/default is physically framed. The unchanged reader EOF
remains available for all subsequent rank markers and later block iterations.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackJetBlocksInner
open SemiprimeD1StackJetBlocks SemiprimeD1StackJetBlocksPrimitives
open SemiprimeD1StackJetBlocksView SemiprimeD1StackJetBlocksEncoding SemiprimeD1StackJetBlocksFields
open SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits)
local notation "ctl" => Label.local
/-- Exact actual primitive clock for a complete rank-marker loop, including its final empty-counter pop. -/
def innerClock :Nat→List (List Bool)→Nat
  | 0,_=>1
  | r+1,[]=>16+innerClock r []
  | r+1,word::words=>19*word.length+25+innerClock r words
/-- Entire actual rank-marker loop emits EXACTthe original sequential/default coefficient words. -/
theorem inner_run (context:X.Stack→List Bool) (coefficients blocks todo hist history:List Bool)
    (r:Nat) (words:List (List Bool)) :
    Runs program (innerClock r words) (ctl .inner)
      (data context coefficients blocks todo (vectorBits words) (List.replicate r true) [] hist [] history)
      (ctl .rowSeed) (data context coefficients blocks todo (vectorBits (words.drop r)) [] []
        ((Codec.payload (padded r words)).reverse++hist) [] history) :=by
  induction r generalizing words hist with
  | zero=>
    apply one_base program (ctl .inner) (ctl .rowSeed)
      (.pop (aux .rankTodo) (ctl .rowSeed) (ctl .abort) (ctl .peek)) _ _ rfl
    · rfl
    · funext k;rcases k with k|k
      · rfl
      · cases k <;> rfl
  | succ r ih=>
    cases words with
    | nil=>
      have h0:=empty_slot context coefficients blocks todo hist history r
      have h1:=ih ((Codec.chunk []).reverse++hist) []
      have h:=join h0 h1
      simpa only [innerClock,padded,List.headD_nil,List.tail_nil,Codec.payload,List.foldr_cons,
        List.reverse_append,List.append_assoc,List.drop_nil] using h
    | cons word words=>
      have h0:=real_slot context coefficients blocks todo hist history word words r
      have h1:=ih ((Codec.chunk word).reverse++hist) words
      have h:=join h0 h1
      simpa only [innerClock,padded,List.headD_cons,List.tail_cons,Codec.payload,List.foldr_cons,
        List.reverse_append,List.append_assoc,List.drop_succ_cons] using h
/-- Sum of actual physical word payload lengths; empty default coefficients contribute no numeric bits. -/
def wordMass (words:List (List Bool)) :Nat :=(words.map List.length).sum
/-- Actual stream padding has exactly the byte mass of the real consumed prefix, without copying or reading later fields. -/
theorem padded_mass (r:Nat) (words:List (List Bool)) :wordMass (padded r words)=wordMass (words.take r) :=by
  induction r generalizing words with
  | zero=>rfl
  | succ r ih=>
    cases words with
    | nil=>simpa only [padded,List.headD_nil,List.tail_nil,wordMass,List.map_cons,List.sum_cons,List.length_nil,Nat.zero_add,List.take_nil] using ih []
    | cons word words=>
      simp only [padded,List.headD_cons,List.tail_cons,List.take_succ_cons,wordMass,List.map_cons,List.sum_cons]
      exact congrArg (word.length+·) (ih words)
/-- Source EOF padding does not create coefficient bit mass. -/
theorem padded_mass_le (r:Nat) (words:List (List Bool)) :wordMass (padded r words)≤wordMass words :=by
  rw [padded_mass]
  have h:=List.take_append_drop r words
  have hm:=congrArg wordMass h
  simp only [wordMass,List.map_append,List.sum_append] at hm
  unfold wordMass
  omega
/-- Own actual inner-loop time is linear in the REALread coefficient bytes and actual rank markers. -/
theorem innerClock_le (r:Nat) (words:List (List Bool)) :
    innerClock r words≤20*wordMass (padded r words)+25*r+1 :=by
  induction r generalizing words with
  | zero=>rfl
  | succ r ih=>
    cases words with
    | nil=>
      have h:=ih []
      simp only [innerClock,padded,List.headD_nil,List.tail_nil,wordMass,List.map_cons,List.sum_cons,List.length_nil,Nat.zero_add] at h ⊢
      omega
    | cons word words=>
      have h:=ih words
      simp only [innerClock,padded,List.headD_cons,List.tail_cons,wordMass,List.map_cons,List.sum_cons] at h ⊢
      omega
end RiemannGaussian.SemiprimeD1StackJetBlocksInner
