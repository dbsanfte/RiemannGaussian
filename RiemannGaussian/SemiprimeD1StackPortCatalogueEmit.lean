/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortCataloguePrimitives
import RiemannGaussian.SemiprimeD1StackPortCatalogueView
import RiemannGaussian.SemiprimeD1StackEdgeCatalogueEmit
/-! # Actual eight-field occurrence framing, with all copy/reversal transitions -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackPortCatalogueEmit
open SemiprimeD1StackPortCatalogue SemiprimeD1StackPortCataloguePrimitives
open SemiprimeD1StackPortCatalogueView
open SemiprimeD1StackProcedureFragments (Runs)
open SemiprimeD1EdgeCatalogueEncoding (Record record)
open SemiprimeSourceHistogramKeyBits (frame frame_length)
/-- Static next field, then the actual local-slot counter increment. -/
def nextField (part:Fin 8) : Label :=
  if h:part.val<7 then .local (.emitFrame ⟨part.val+1,by omega⟩) else .local .incrementSlot
/-- Literal cached occurrence/factor/local ordinals precede the original descriptor. -/
def sourceField (words:Record) (slot factor occurrence:List Bool) (part:Fin 8) : List Bool :=
  if part.val=0 then occurrence else if part.val=1 then factor else if part.val=2 then slot
  else words ⟨part.val-3,by omega⟩
/-- Every emitted field is physically present in its mapped source stack. -/
theorem source_clean (base:V.Stack→List Bool) (tape:List Bool) (words:Record)
    (raw slot edges factor occurrence remaining:List Bool) (part:Fin 8) :
    clean base tape words raw slot edges factor occurrence remaining (frameSource part)=
      sourceField words slot factor occurrence part := by fin_cases part <;> rfl
/-- One real Frame call and one real Reverse call emit the actual cached field. -/
theorem field_run (base:V.Stack→List Bool) (tape:List Bool) (words:Record)
    (raw slot edges factor occurrence remaining:List Bool) (part:Fin 8) :
    Runs program (10*(sourceField words slot factor occurrence part).length+10) (.local (.emitFrame part))
      (clean base tape words raw slot edges factor occurrence remaining) (nextField part)
      (clean base tape words ((frame (sourceField words slot factor occurrence part) []).reverse++raw) slot edges factor occurrence remaining) := by
  let before:=clean base tape words raw slot edges factor occurrence remaining
  let word:=sourceField words slot factor occurrence part
  have hf:=frame_call part before rfl rfl
  have hsource:before (frameSource part)=word:=source_clean base tape words raw slot edges factor occurrence remaining part
  rw [hsource] at hf
  have hr:=reverse_call false (Function.update before (oldAux .frameBuffer) (frame word []))
    (.local (.emitReverse part)) (nextField part) rfl
  have hi:(Function.update before (oldAux .frameBuffer) (frame word [])) (reverseInput false)=frame word []:=
    Function.update_self _ _ _
  have ho:(Function.update before (oldAux .frameBuffer) (frame word [])) (reverseOutput false)=raw:=by
    simp [reverseOutput,before,clean,store,oldClean,oldAux,edgeStack,E.aux,Function.update]
  rw [hi,ho] at hr
  change Runs program _ _ _ _ (Function.update (Function.update
    (Function.update before (oldAux .frameBuffer) (frame word [])) (oldAux .frameBuffer) [])
      (oldAux .reversed) ((frame word []).reverse++raw)) at hr
  rw [Function.update_idem] at hr
  have he:Function.update before (oldAux .frameBuffer) []=before:=by
    have hh:before (oldAux .frameBuffer)=[]:=rfl
    rw [←hh]
    exact Function.update_eq_self _ _
  rw [he,clean_raw] at hr
  have h:=hf.trans hr
  rw [frame_length,List.length_nil] at h
  simpa only [show (6*word.length+5)+(2*(2*word.length+0+1)+3)=10*word.length+10 by omega] using h

/-- Actual eight-field byte record, including every ordinal rather than an advised ID. -/
def record8 (words:Record) (slot factor occurrence tail:List Bool) : List Bool :=
  frame occurrence (frame factor (frame slot (record words tail)))
/-- Exact byte mass copied by the eight physical component pairs. -/
def mass8 (words:Record) (slot factor occurrence:List Bool) : ℕ :=
  occurrence.length+factor.length+slot.length+SemiprimeD1StackEdgeCatalogueParse.wordMass words
/-- The actual eight-call output has the exact original ordinal/descriptor order. -/
theorem reverse_record8 (words:Record) (slot factor occurrence raw:List Bool) :
    (frame (words 4) []).reverse++((frame (words 3) []).reverse++((frame (words 2) []).reverse++
      ((frame (words 1) []).reverse++((frame (words 0) []).reverse++((frame slot []).reverse++
        ((frame factor []).reverse++((frame occurrence []).reverse++raw)))))))=
      (record8 words slot factor occurrence []).reverse++raw := by
  symm
  unfold record8 record
  rw [SemiprimeD1StackEdgeCatalogueEmit.frame_append occurrence,
    SemiprimeD1StackEdgeCatalogueEmit.frame_append factor,
    SemiprimeD1StackEdgeCatalogueEmit.frame_append slot,
    SemiprimeD1StackEdgeCatalogueEmit.frame_append (words 0),
    SemiprimeD1StackEdgeCatalogueEmit.frame_append (words 1),
    SemiprimeD1StackEdgeCatalogueEmit.frame_append (words 2),
    SemiprimeD1StackEdgeCatalogueEmit.frame_append (words 3)]
  simp only [List.reverse_append,List.append_assoc]
/-- All eight actual fields execute once each, including the actual occurrence/local IDs. -/
theorem record_run (base:V.Stack→List Bool) (tape:List Bool) (words:Record)
    (raw slot edges factor occurrence remaining:List Bool) :
    Runs program (10*mass8 words slot factor occurrence+80) (.local (.emitFrame 0))
      (clean base tape words raw slot edges factor occurrence remaining) (.local .incrementSlot)
      (clean base tape words ((record8 words slot factor occurrence []).reverse++raw)
        slot edges factor occurrence remaining) := by
  let r1:=(frame (occurrence) []).reverse++raw
  let r2:=(frame (factor) []).reverse++r1
  let r3:=(frame (slot) []).reverse++r2
  let r4:=(frame (words 0) []).reverse++r3
  let r5:=(frame (words 1) []).reverse++r4
  let r6:=(frame (words 2) []).reverse++r5
  let r7:=(frame (words 3) []).reverse++r6
  have h0:=field_run base tape words raw slot edges factor occurrence remaining 0
  have h1:=field_run base tape words r1 slot edges factor occurrence remaining 1
  have h2:=field_run base tape words r2 slot edges factor occurrence remaining 2
  have h3:=field_run base tape words r3 slot edges factor occurrence remaining 3
  have h4:=field_run base tape words r4 slot edges factor occurrence remaining 4
  have h5:=field_run base tape words r5 slot edges factor occurrence remaining 5
  have h6:=field_run base tape words r6 slot edges factor occurrence remaining 6
  have h7:=field_run base tape words r7 slot edges factor occurrence remaining 7
  have h:=h0.trans (h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans (h7)))))))
  change Runs program _ _ _ (.local .incrementSlot) (clean base tape words
    ((frame (words 4) []).reverse++((frame (words 3) []).reverse++((frame (words 2) []).reverse++
      ((frame (words 1) []).reverse++((frame (words 0) []).reverse++((frame slot []).reverse++
        ((frame factor []).reverse++((frame occurrence []).reverse++raw))))))))
    slot edges factor occurrence remaining) at h
  rw [reverse_record8] at h
  have ht:(10*occurrence.length+10+(10*factor.length+10+(10*slot.length+10+
      (10*(words 0).length+10+(10*(words 1).length+10+(10*(words 2).length+10+
        (10*(words 3).length+10+(10*(words 4).length+10))))))))=
      10*mass8 words slot factor occurrence+80:=by
    unfold mass8 SemiprimeD1StackEdgeCatalogueParse.wordMass
    omega
  change Runs program (10*occurrence.length+10+(10*factor.length+10+(10*slot.length+10+
      (10*(words 0).length+10+(10*(words 1).length+10+(10*(words 2).length+10+
        (10*(words 3).length+10+(10*(words 4).length+10)))))))) _ _ _ _ at h
  rw [ht] at h
  exact h
end RiemannGaussian.SemiprimeD1StackPortCatalogueEmit
