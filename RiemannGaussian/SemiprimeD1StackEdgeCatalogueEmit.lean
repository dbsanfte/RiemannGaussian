/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackEdgeCatalogueParse

/-! # Actual edge field framing and reversal, with every bit operation retained -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option synthInstance.maxSize 8192
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackEdgeCatalogueEmit
open SemiprimeD1StackEdgeCatalogue SemiprimeD1StackEdgeCatalogueComponents
open SemiprimeD1StackEdgeCatalogueView SemiprimeD1StackEdgeCatalogueParse
open SemiprimeD1StackProcedureFragments (Runs)
open SemiprimeD1EdgeCatalogueEncoding (Record record half sideWord)
open SemiprimeSourceHistogramKeyBits (frame frame_length)

/-- Literal next label after one actual framed-field reversal. -/
def nextField (side:Bool) (part:Fin 6) : Label :=
  if h:part.val<5 then .inl (.emitFrame side ⟨part.val+1,by omega⟩)
  else if side then .inl .clearSide else .inl .pushSide
/-- Actual source word at each of six static field positions. -/
def sourceField (words:Record) (side:List Bool) (part:Fin 6) : List Bool :=
  if h:part.val=0 then side else words ⟨part.val-1,by omega⟩
/-- Framing reads the actual cached field or physically acquired side marker. -/
theorem source_clean (base:Cat.Stack→List Bool) (tape:List Bool) (words:Record) (raw side:List Bool) (part:Fin 6) :
    clean base tape words raw side (frameSource part)=sourceField words side part := by fin_cases part <;> rfl
/-- A physical raw-output update retains every other source/cache role. -/
theorem clean_raw (base:Cat.Stack→List Bool) (tape:List Bool) (words:Record) (raw side next:List Bool) :
    Function.update (clean base tape words raw side) (aux .reversed) next=clean base tape words next side := by
  unfold clean
  rw [update_aux]
  congr 1
  funext k
  cases k <;> simp [cleanWork,Function.update]
/-- A physical side-marker update retains all actual parsed fields. -/
theorem clean_side (base:Cat.Stack→List Bool) (tape:List Bool) (words:Record) (raw side next:List Bool) :
    Function.update (clean base tape words raw side) (aux .side) next=clean base tape words raw next := by
  unfold clean
  rw [update_aux]
  congr 1
  funext k
  cases k <;> simp [cleanWork,Function.update]
/-- One real Frame call and one real Reverse call emit the actual cached field. -/
theorem field_run (base:Cat.Stack→List Bool) (tape:List Bool) (words:Record) (raw sideWord:List Bool)
    (side:Bool) (part:Fin 6) :
    Runs program (10*(sourceField words sideWord part).length+10) (.inl (.emitFrame side part))
      (clean base tape words raw sideWord) (nextField side part)
      (clean base tape words ((frame (sourceField words sideWord part) []).reverse++raw) sideWord) := by
  let before:=clean base tape words raw sideWord
  let word:=sourceField words sideWord part
  have hf:=frame_call part side before rfl rfl
  have hsource:before (frameSource part)=word:=source_clean base tape words raw sideWord part
  rw [hsource] at hf
  have hr:=reverse_call false (Function.update before (aux .frameBuffer) (frame word []))
    (.inl (.emitReverse side part)) (nextField side part) rfl
  have hi:(Function.update before (aux .frameBuffer) (frame word [])) (reverseInput false)=frame word []:=
    Function.update_self _ _ _
  have ho:(Function.update before (aux .frameBuffer) (frame word [])) (reverseOutput false)=raw:=by
    simp [reverseOutput,before,clean,store,cleanWork,aux,Function.update]
  rw [hi,ho] at hr
  change Runs program _ _ _ _ (Function.update (Function.update
    (Function.update before (aux .frameBuffer) (frame word [])) (aux .frameBuffer) [])
      (aux .reversed) ((frame word []).reverse++raw)) at hr
  rw [Function.update_idem] at hr
  have he:Function.update before (aux .frameBuffer) []=before:=by
    have hh:before (aux .frameBuffer)=[]:=rfl
    rw [←hh]
    exact Function.update_eq_self _ _
  rw [he,clean_raw] at hr
  have h:=hf.trans hr
  rw [frame_length,List.length_nil] at h
  simpa only [show (6*word.length+5)+(2*(2*word.length+0+1)+3)=10*word.length+10 by omega] using h

/-- Framing retains the exact acquired tail. -/
theorem frame_append (xs ys:List Bool) : frame xs ys=frame xs []++ys := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simpa only [frame,List.cons_append] using congrArg (fun rest=>true::b::rest) ih
/-- Literal reverse of one side-plus-descriptor record. -/
theorem reverse_record (words:Record) (side raw:List Bool) :
    (frame (words 4) []).reverse++((frame (words 3) []).reverse++((frame (words 2) []).reverse++
      ((frame (words 1) []).reverse++((frame (words 0) []).reverse++((frame side []).reverse++raw)))))=
      (frame side (record words [])).reverse++raw := by
  symm
  unfold record
  rw [frame_append side,frame_append (words 0),frame_append (words 1),frame_append (words 2),frame_append (words 3)]
  simp only [List.reverse_append,List.append_assoc]

/-- Both output continuations are static finite labels. -/
def afterRecord (side:Bool) : Label := if side then .inl .clearSide else .inl .pushSide
/-- All six actual fields are emitted without catalogue/count/record callbacks. -/
theorem record_run (base:Cat.Stack→List Bool) (tape:List Bool) (words:Record) (raw sideWord:List Bool) (side:Bool) :
    Runs program (10*(sideWord.length+wordMass words)+60) (.inl (.emitFrame side 0))
      (clean base tape words raw sideWord) (afterRecord side)
      (clean base tape words ((frame sideWord (record words [])).reverse++raw) sideWord) := by
  let r1:=(frame sideWord []).reverse++raw
  let r2:=(frame (words 0) []).reverse++r1
  let r3:=(frame (words 1) []).reverse++r2
  let r4:=(frame (words 2) []).reverse++r3
  let r5:=(frame (words 3) []).reverse++r4
  have h0:=field_run base tape words raw sideWord side 0
  have h1:=field_run base tape words r1 sideWord side 1
  have h2:=field_run base tape words r2 sideWord side 2
  have h3:=field_run base tape words r3 sideWord side 3
  have h4:=field_run base tape words r4 sideWord side 4
  have h5:=field_run base tape words r5 sideWord side 5
  have h:=h0.trans (h1.trans (h2.trans (h3.trans (h4.trans h5))))
  change Runs program _ _ _ (afterRecord side) (clean base tape words
    ((frame (words 4) []).reverse++((frame (words 3) []).reverse++((frame (words 2) []).reverse++
      ((frame (words 1) []).reverse++((frame (words 0) []).reverse++((frame sideWord []).reverse++raw)))))) sideWord) at h
  rw [reverse_record] at h
  have ht:(10*sideWord.length+10+(10*(words 0).length+10+(10*(words 1).length+10+
      (10*(words 2).length+10+(10*(words 3).length+10+(10*(words 4).length+10))))))=
      10*(sideWord.length+wordMass words)+60:=by unfold wordMass;omega
  change Runs program (10*sideWord.length+10+(10*(words 0).length+10+(10*(words 1).length+10+
    (10*(words 2).length+10+(10*(words 3).length+10+(10*(words 4).length+10)))))) _ _ _ _ at h
  rw [ht] at h
  exact h

/-- Framing preserves an actual appended tail byte for byte. -/
theorem frame_tail (xs ys zs:List Bool) : frame xs (ys++zs)=frame xs ys++zs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simpa only [frame,List.cons_append] using congrArg (fun rest=>true::b::rest) ih
/-- Five-field descriptor framing preserves its actual tail. -/
theorem record_append (words:Record) (tail:List Bool) : record words tail=record words []++tail := by
  unfold record
  rw [frame_append (words 4) tail,frame_tail (words 3),frame_tail (words 2),frame_tail (words 1),frame_tail (words 0)]
/-- The actual side field and descriptor preserve their acquired tape suffix. -/
theorem half_append (side:Bool) (words:Record) (tail:List Bool) : half side words tail=half side words []++tail := by
  unfold half
  rw [record_append,frame_tail]
/-- Reverse accumulation retains the exact original false-before-true order. -/
theorem reverse_pair (words:Record) (raw:List Bool) :
    (half true words []).reverse++((half false words []).reverse++raw)=
      (half false words (half true words [])).reverse++raw := by
  rw [half_append false words (half true words [])]
  simp only [List.reverse_append,List.append_assoc]
/-- Both literal edge-side records are physically emitted, with actual side acquisition/cleanup. -/
theorem pair_run (base:Cat.Stack→List Bool) (tape:List Bool) (words:Record) (raw:List Bool) :
    Runs program (20*wordMass words+132) (.inl (.emitFrame false 0))
      (clean base tape words raw []) (.inl (.clearCache 0))
      (clean base tape words ((half false words (half true words [])).reverse++raw) []) := by
  let r1:=(half false words []).reverse++raw
  let r2:=(half true words []).reverse++r1
  have h0:=record_run base tape words raw [] false
  change Runs program _ _ _ (.inl .pushSide) (clean base tape words r1 []) at h0
  have h1:=push_run (.inl .pushSide) (.inl (.emitFrame true 0)) (aux .side) true (clean base tape words r1 []) rfl
  change Runs program _ _ _ _ (Function.update (clean base tape words r1 []) (aux .side) [true]) at h1
  rw [clean_side] at h1
  have h2:=record_run base tape words r1 [true] true
  change Runs program _ _ _ (.inl .clearSide) (clean base tape words r2 [true]) at h2
  have h3:=pop_run (.inl .clearSide) (.inl (.clearCache 0)) (aux .side) (clean base tape words r2 [true]) rfl
  change Runs program _ _ _ _ (Function.update (clean base tape words r2 [true]) (aux .side) []) at h3
  rw [clean_side] at h3
  have h:=h0.trans (h1.trans (h2.trans h3))
  change Runs program _ _ _ _ (clean base tape words
    ((half true words []).reverse++((half false words []).reverse++raw)) []) at h
  rw [reverse_pair] at h
  have ht:(10*(0+wordMass words)+60)+(1+((10*(1+wordMass words)+60)+1))=20*wordMass words+132:=by omega
  change Runs program ((10*(0+wordMass words)+60)+(1+((10*(1+wordMass words)+60)+1))) _ _ _ _ at h
  rw [ht] at h
  exact h
end RiemannGaussian.SemiprimeD1StackEdgeCatalogueEmit

