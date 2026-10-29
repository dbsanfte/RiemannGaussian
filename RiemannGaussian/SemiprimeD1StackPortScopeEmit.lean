/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortScopeView
import RiemannGaussian.SemiprimeD1StackPortScopePrimitives
import RiemannGaussian.SemiprimeD1PortScopeEncoding
/-! # Actual scope-ID-first framing of all unchanged original port fields -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackPortScopeEmit
open SemiprimeD1StackPortScopeRecords SemiprimeD1StackPortScopeView
open SemiprimeD1StackPortScopePrimitives
open SemiprimeD1StackProcedureFragments (Runs)
open SemiprimeSourceHistogramKeyBits (frame frame_length)
/-- Literal finite field continuation, then actual cache-cell cleanup. -/
def nextField (part:Fin 9) : Label :=
  if h:part.val<8 then .local (.emitFrame ⟨part.val+1,by omega⟩) else .local (.clearCache 0)
/-- Actual cached ID first, then unchanged eight old fields. -/
def sourceField (words:Record) (part:Fin 9) : List Bool :=
  if part.val=0 then words 8 else words ⟨part.val-1,by omega⟩
/-- Every framing source is the exact physically cached word. -/
theorem source_clean (base:S.Stack→List Bool) (ports ids:List Bool) (words:Record) (raw:List Bool) (part:Fin 9) :
    clean base ports ids words raw (frameSource part)=sourceField words part := by fin_cases part <;> rfl
/-- One real Frame call and one real Reverse call emit the actual cached field. -/
theorem field_run (base:S.Stack→List Bool) (ports ids:List Bool) (words:Record) (raw:List Bool) (part:Fin 9) :
    Runs program (10*(sourceField words part).length+10) (.local (.emitFrame part))
      (clean base ports ids words raw) (nextField part)
      (clean base ports ids words ((frame (sourceField words part) []).reverse++raw)) := by
  let before:=clean base ports ids words raw
  let word:=sourceField words part
  have hf:=frame_call part before rfl rfl
  have hsource:before (frameSource part)=word:=source_clean base ports ids words raw part
  rw [hsource] at hf
  have hr:=reverse_call false (Function.update before (aux .frameBuffer) (frame word []))
    (.local (.emitReverse part)) (nextField part) rfl
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

/-- Exact nine-field physical output record. -/
def record (w:Record) (tail:List Bool) : List Bool :=
  frame (w 8) (frame (w 0) (frame (w 1) (frame (w 2) (frame (w 3)
    (frame (w 4) (frame (w 5) (frame (w 6) (frame (w 7) tail))))))))
/-- The actual cached parser values give precisely the scope-tagged original record. -/
theorem record_cached (w:SemiprimeD1PortScopeEncoding.Port) (id tail:List Bool) :
    record (SemiprimeD1PortScopeEncoding.cached w id) tail=SemiprimeD1PortScopeEncoding.scopeFrame w id tail := rfl
/-- Exact copied word mass of the nine real component calls. -/
def wordMass (w:Record) : ℕ :=
  (w 8).length+(w 0).length+(w 1).length+(w 2).length+(w 3).length+
    (w 4).length+(w 5).length+(w 6).length+(w 7).length
/-- Exact reversal of the actual nine emitted fields. -/
theorem reverse_record (w:Record) (raw:List Bool) :
    (frame (w 7) []).reverse++((frame (w 6) []).reverse++((frame (w 5) []).reverse++
    ((frame (w 4) []).reverse++((frame (w 3) []).reverse++((frame (w 2) []).reverse++
    ((frame (w 1) []).reverse++((frame (w 0) []).reverse++((frame (w 8) []).reverse++raw))))))))=
      (record w []).reverse++raw := by
  symm
  unfold record
  rw [SemiprimeD1StackEdgeCatalogueEmit.frame_append (w 8),
    SemiprimeD1StackEdgeCatalogueEmit.frame_append (w 0),
    SemiprimeD1StackEdgeCatalogueEmit.frame_append (w 1),
    SemiprimeD1StackEdgeCatalogueEmit.frame_append (w 2),
    SemiprimeD1StackEdgeCatalogueEmit.frame_append (w 3),
    SemiprimeD1StackEdgeCatalogueEmit.frame_append (w 4),
    SemiprimeD1StackEdgeCatalogueEmit.frame_append (w 5),
    SemiprimeD1StackEdgeCatalogueEmit.frame_append (w 6)]
  simp only [List.reverse_append,List.append_assoc]
/-- All nine real Frame/Reverse pairs retain their input cache and both source readers. -/
theorem record_run (base:S.Stack→List Bool) (ports ids:List Bool) (words:Record) (raw:List Bool) :
    Runs program (10*wordMass words+90) (.local (.emitFrame 0))
      (clean base ports ids words raw) (.local (.clearCache 0))
      (clean base ports ids words ((record words []).reverse++raw)) := by
  let r1:=(frame (words 8) []).reverse++raw
  let r2:=(frame (words 0) []).reverse++r1
  let r3:=(frame (words 1) []).reverse++r2
  let r4:=(frame (words 2) []).reverse++r3
  let r5:=(frame (words 3) []).reverse++r4
  let r6:=(frame (words 4) []).reverse++r5
  let r7:=(frame (words 5) []).reverse++r6
  let r8:=(frame (words 6) []).reverse++r7
  have h0:=field_run base ports ids words raw 0
  have h1:=field_run base ports ids words r1 1
  have h2:=field_run base ports ids words r2 2
  have h3:=field_run base ports ids words r3 3
  have h4:=field_run base ports ids words r4 4
  have h5:=field_run base ports ids words r5 5
  have h6:=field_run base ports ids words r6 6
  have h7:=field_run base ports ids words r7 7
  have h8:=field_run base ports ids words r8 8
  have h:=h0.trans (h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans (h7.trans (h8))))))))
  change Runs program _ _ _ (.local (.clearCache 0)) (clean base ports ids words ((frame (words 7) []).reverse++((frame (words 6) []).reverse++((frame (words 5) []).reverse++((frame (words 4) []).reverse++((frame (words 3) []).reverse++((frame (words 2) []).reverse++((frame (words 1) []).reverse++((frame (words 0) []).reverse++((frame (words 8) []).reverse++(raw))))))))))) at h
  rw [reverse_record] at h
  have ht:(10*(words 8).length+10+(10*(words 0).length+10+(10*(words 1).length+10+(10*(words 2).length+10+(10*(words 3).length+10+(10*(words 4).length+10+(10*(words 5).length+10+(10*(words 6).length+10+(10*(words 7).length+10)))))))))=10*wordMass words+90:=by unfold wordMass;omega
  change Runs program (10*(words 8).length+10+(10*(words 0).length+10+(10*(words 1).length+10+(10*(words 2).length+10+(10*(words 3).length+10+(10*(words 4).length+10+(10*(words 5).length+10+(10*(words 6).length+10+(10*(words 7).length+10))))))))) _ _ _ _ at h
  rw [ht] at h
  exact h
end RiemannGaussian.SemiprimeD1StackPortScopeEmit
