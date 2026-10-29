/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceIncidenceEdgeFinish
/-! # Complete real one-edge classification for every physically acquired prefix -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceIncidenceEdges
open SemiprimeD1StackSourceIncidence SemiprimeD1StackSourceIncidencePrimitives
open SemiprimeD1StackSourceIncidenceView SemiprimeD1StackSourceIncidenceCalls
open SemiprimeD1StackSourceIncidenceLookup SemiprimeD1StackSourceIncidenceEdgeFinish
open SemiprimeD1StackProcedureTrace SemiprimeD1StackSourceIncidenceSpec
open SemiprimeBitArithmetic (bitValue)
/-- Own upper clock for every literal classifier branch; IDs here are proof interpretations of actual reads. -/
def edgeClock (ids:List (List Bool)) (left right:List Bool) :Nat :=
  200*(left.length+right.length+(readID ids left).length+(readID ids right).length+1)+
    500*(left.length+right.length+2)*((Env.dictionary ids).length+1)
/-- Actual complete classifier: key loop test, paid lookup(s), physical found flags, saved fixed IDs,
real numeric ID comparison, cleanup and two-byte status emission. No verdict/remaining list is supplied. -/
theorem edge_run (ids:List (List Bool)) (chosen pfx:List Bool) (words:Aux→List Bool) (kind:Edge)
    (hc:words .copyScratch=[]) (hs:words .eqScratch=[]) :
    ∃q≤edgeClock ids (endpoint words false kind) (endpoint words true kind),
      Runs program q (.edgeStart kind) (view ids chosen pfx words [] [] [] [] [] []) .edgeReturn
        (view ids chosen pfx words [] [] []
          [possible (edge ids (endpoint words false kind) (endpoint words true kind)),
            drop (edge ids (endpoint words false kind) (endpoint words true kind))] [] []) :=by
  let left:=endpoint words false kind
  let right:=endpoint words true kind
  let leftID:=readID ids left
  let rightID:=readID ids right
  have hkeys:=keys_run ids chosen pfx words kind hc hs
  change Runs program ((5*left.length+4)+(5*right.length+4)+
    (SemiprimeD1StackWordEqualExecution.executionTime left right+1)) _ _ _
    (view ids chosen pfx words [] [] [] [decide (bitValue left=bitValue right)] [] []) at hkeys
  have hpop:=pop_run (.keysEqual kind) .abort (.copyQuery kind false) (.status .stable) (aux .eqOutput)
    (view ids chosen pfx words [] [] [] [decide (bitValue left=bitValue right)] [] [])
    [decide (bitValue left=bitValue right)] rfl rfl
  change Runs program 1 _ _ _ (Function.update
    (view ids chosen pfx words [] [] [] [decide (bitValue left=bitValue right)] [] []) (aux .eqOutput) []) at hpop
  rw [update_comparison] at hpop
  have hkeyTime:=SemiprimeD1StackWordEqualExecution.executionTime_le left right
  by_cases hloop:bitValue left=bitValue right
  · simp only [hloop,decide_true,SemiprimeD1StackBytecode.choose,List.head?_cons] at hkeys hpop
    have h:=join (join hkeys hpop) (status_run ids chosen pfx words .stable)
    have he:edge ids left right=.stable:=by simp only [edge,hloop,ite_true]
    refine ⟨_,?_,by
      change Runs program _ _ _ _ (view ids chosen pfx words [] [] []
        [possible (edge ids left right),drop (edge ids left right)] [] [])
      simpa only [he,possible,drop] using h⟩
    unfold edgeClock
    dsimp only [left,right] at hkeyTime
    nlinarith only [hkeyTime]
  · simp only [hloop,decide_false,SemiprimeD1StackBytecode.choose,List.head?_cons] at hkeys hpop
    obtain ⟨t,ht,hfirst⟩:=lookup_stage ids chosen pfx words kind false [] [] hc
    by_cases hl:bitValue left < ids.length
    · change Runs program t _ _ _ (view ids chosen pfx words left [] [] [] [decide (bitValue left < ids.length)]
        (if bitValue left < ids.length then leftID else [])) at hfirst
      simp only [hl,decide_true,ite_true] at hfirst
      have hf:=found_pop ids chosen pfx words kind false true left [] [] leftID
      have hs0:=save_first ids chosen pfx words kind left [] leftID hc
      have hc0:=cleanup ids chosen pfx words kind false true left leftID [] leftID
      have hj0:=jump_run (.afterLookup kind false true) (.copyQuery kind true)
        (view ids chosen pfx words [] leftID [] [] [] []) rfl
      have hprefix:=join (join (join (join (join (join hkeys hpop) hfirst) hf) hs0) hc0) hj0
      obtain ⟨u,hu,hsecond⟩:=lookup_stage ids chosen pfx words kind true leftID [] hc
      by_cases hr:bitValue right < ids.length
      · change Runs program u _ _ _ (view ids chosen pfx words right leftID [] [] [decide (bitValue right < ids.length)]
          (if bitValue right < ids.length then rightID else [])) at hsecond
        simp only [hr,decide_true,ite_true] at hsecond
        have hf1:=found_pop ids chosen pfx words kind true true right leftID [] rightID
        have hs1:=save_second ids chosen pfx words kind right leftID rightID hc
        have hc1:=cleanup ids chosen pfx words kind true true right leftID rightID rightID
        have hfinish:=second_present ids chosen pfx words kind leftID rightID hs
        have h:=join (join (join (join (join hprefix hsecond) hf1) hs1) hc1) hfinish
        have hn:¬(ids.length ≤ bitValue left ∨ ids.length ≤ bitValue right):=by omega
        have he:edge ids left right=if bitValue leftID=bitValue rightID then .stable else .reject:=by
          simp only [edge,hloop,ite_false,hn,leftID,rightID]
        refine ⟨_,?_,by
          change Runs program _ _ _ _ (view ids chosen pfx words [] [] [] [possible (edge ids left right),drop (edge ids left right)] [] [])
          rw [he]
          by_cases hi:bitValue leftID=bitValue rightID
          · simpa only [hi,ite_true,possible,drop] using h
          · simpa only [hi,ite_false,possible,drop] using h⟩
        unfold edgeClock
        have hIDTime:=SemiprimeD1StackWordEqualExecution.executionTime_le leftID rightID
        dsimp only [left,right,leftID,rightID] at ht hu hkeyTime hIDTime ⊢
        nlinarith only [ht,hu,hkeyTime,hIDTime]
      · change Runs program u _ _ _ (view ids chosen pfx words right leftID [] [] [decide (bitValue right < ids.length)]
          (if bitValue right < ids.length then rightID else [])) at hsecond
        simp only [hr,decide_false,ite_false] at hsecond
        have hf1:=found_pop ids chosen pfx words kind true false right leftID [] []
        have hc1:=cleanup ids chosen pfx words kind true false right leftID [] []
        have hfinish:=second_missing ids chosen pfx words kind leftID
        have h:=join (join (join (join hprefix hsecond) hf1) hc1) hfinish
        have hfree:ids.length ≤ bitValue left ∨ ids.length ≤ bitValue right:=Or.inr (by omega)
        have he:edge ids left right=.free:=by simp only [edge,hloop,ite_false,hfree,ite_true]
        refine ⟨_,?_,by
          change Runs program _ _ _ _ (view ids chosen pfx words [] [] []
            [possible (edge ids left right),drop (edge ids left right)] [] [])
          simpa only [he,possible,drop] using h⟩
        unfold edgeClock
        dsimp only [left,right,leftID,rightID] at ht hu hkeyTime ⊢
        simp only [List.length_nil]
        nlinarith only [ht,hu,hkeyTime]
    · change Runs program t _ _ _ (view ids chosen pfx words left [] [] [] [decide (bitValue left < ids.length)]
        (if bitValue left < ids.length then leftID else [])) at hfirst
      simp only [hl,decide_false,ite_false] at hfirst
      have hf:=found_pop ids chosen pfx words kind false false left [] [] []
      have hc0:=cleanup ids chosen pfx words kind false false left [] [] []
      have hfinish:=first_missing ids chosen pfx words kind
      have h:=join (join (join (join (join hkeys hpop) hfirst) hf) hc0) hfinish
      have hfree:ids.length ≤ bitValue left ∨ ids.length ≤ bitValue right:=Or.inl (by omega)
      have he:edge ids left right=.free:=by simp only [edge,hloop,ite_false,hfree,ite_true]
      refine ⟨_,?_,by
        change Runs program _ _ _ _ (view ids chosen pfx words [] [] []
          [possible (edge ids left right),drop (edge ids left right)] [] [])
        simpa only [he,possible,drop] using h⟩
      unfold edgeClock
      dsimp only [left,right,leftID,rightID] at ht hkeyTime ⊢
      simp only [List.length_nil]
      nlinarith only [ht,hkeyTime]
end RiemannGaussian.SemiprimeD1StackSourceIncidenceEdges
