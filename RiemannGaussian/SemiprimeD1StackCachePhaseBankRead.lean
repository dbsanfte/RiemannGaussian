/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackCachePhaseBankFields
import RiemannGaussian.SemiprimeD1StackCachePhaseBankReady
import RiemannGaussian.SemiprimeD1StackCachePhaseBankStopped
/-! # Actual matched reference/child stream step into the complete callee input
Both real true markers and both real Field validity bits are consumed. Empty
issued reference0 is an ordinary valid framed field, never confused with EOF.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackCachePhaseBankRead
open SemiprimeD1StackCachePhaseBank SemiprimeD1StackCachePhaseBankState
open SemiprimeD1StackCachePhaseBankPrimitives SemiprimeD1StackCachePhaseBankFields
open SemiprimeD1StackCachePhaseBankReady SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
/-- Same actual two tag/Field/valid-pop cost, before the genuine per-phase source call. -/
def readTime (ref children:List Bool):Nat:=(1+(8*ref.length+8))+(1+(8*children.length+8))
/-- Both physical input fields supply EXACT the complete real callee front door, without external operands. -/
theorem read_run (hp cn originalRefs originalChildren ref children refTail childTail history out:List Bool):
    Runs program (readTime ref children) (.local .header)
      (data (P.input hp cn [] []) (words {references:=originalRefs,children:=originalChildren,referenceReader:=true::frame ref refTail,childReader:=true::frame children childTail,history:=history,output:=out}))
      (.local .phase)
      (data (P.input hp cn ref children) (words {references:=originalRefs,children:=originalChildren,referenceReader:=refTail,childReader:=childTail,history:=history,output:=out})):=by
  let bank:=P.input hp cn [] []
  let refBank:=Function.update bank referenceRole ref
  let v:Words:={references:=originalRefs,children:=originalChildren,referenceReader:=true::frame ref refTail,childReader:=true::frame children childTail,history:=history,output:=out}
  let refTag:Words:={v with referenceReader:=frame ref refTail}
  let refRead:Words:={v with referenceReader:=refTail}
  let childTag:Words:={refRead with childReader:=frame children childTail}
  have h0:=pop_run .header (.local .abort) (.local .referenceEOF) (.local .referenceField) (aux .referenceReader)
    (data bank (words v)) (true::frame ref refTail) rfl rfl
  change Runs program 1 (.local .header) _ (.local .referenceField)
    (Function.update (data bank (words v)) (aux .referenceReader) (frame ref refTail)) at h0
  rw [←data_update_aux,words_update] at h0
  have h1:=field_read false (data bank (words refTag)) ref refTail rfl rfl rfl rfl
  change Runs program (8*ref.length+8) (.local .referenceField) _ (.local .childHeader)
    (Function.update (Function.update (data bank (words refTag)) (aux .referenceReader) refTail) (cached referenceRole) ref) at h1
  rw [←data_update_aux,←data_update_cached,words_update] at h1
  have h2:=pop_run .childHeader (.local .abort) (.local .abort) (.local .childField) (aux .childReader)
    (data refBank (words refRead)) (true::frame children childTail) rfl rfl
  change Runs program 1 (.local .childHeader) _ (.local .childField)
    (Function.update (data refBank (words refRead)) (aux .childReader) (frame children childTail)) at h2
  rw [←data_update_aux,words_update] at h2
  have h3:=field_read true (data refBank (words childTag)) children childTail rfl rfl rfl rfl
  change Runs program (8*children.length+8) (.local .childField) _ (.local .phase)
    (Function.update (Function.update (data refBank (words childTag)) (aux .childReader) childTail) (cached childRole) children) at h3
  rw [←data_update_aux,←data_update_cached,words_update] at h3
  have h:=join (join h0 h1) (join h2 h3)
  change Runs program _ _ _ _ (data (Function.update (Function.update (P.input hp cn [] []) referenceRole ref) childRole children) _) at h
  rw [parsed_input] at h
  exact h
end RiemannGaussian.SemiprimeD1StackCachePhaseBankRead
