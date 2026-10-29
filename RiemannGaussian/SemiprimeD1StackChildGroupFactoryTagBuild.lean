/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryPrimitives
/-! # Real original-tag and candidate-tag acquisition
Both literal source families copy the actual side word and prepend one real
Frame of the actual original edge word. No decoded tag or address is supplied.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryTagBuild
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
/-- Two fixed actual tag destinations, not additional runtime modes. -/
def tagRole (candidate:Bool):Stack:=aux (if candidate then .candidateTag else .tagWord)
/-- Two actual fixed side-copy sites. -/
def copySite (candidate:Bool):Fin 38:=if candidate then 31 else 30
/-- Two actual fixed original-edge Frame sites. -/
def frameSite (candidate:Bool):Fin 25:=if candidate then 17 else 16
/-- Both literal two-call source families. -/
def pc (candidate:Bool) (slot:Fin 3):Label:=if candidate then match slot.val with
  | 0=>.local 13 4 | 1=>.local 13 5 | _=>.local 13 6
else match slot.val with
  | 0=>.local 11 22 | 1=>.local 11 23 | _=>.local 11 24
/-- Actual raw tag bytes, before its later physically appended TRUE sentinel. -/
def rawTag (edge side:List Bool):List Bool:=frame edge side
/-- Own real preserving copy and real preserving Frame clocks. -/
def timeBound (edge side:List Bool):Nat:=(5*side.length+4)+(6*edge.length+5)
/-- Exact full115-word actual tag builder at either fixed caller site. -/
theorem source_trace (candidate:Bool) (before:Stack→List Bool) (edge side:List Bool)
    (he:before (aux .edgeWord)=edge) (hs:before (aux .sideWord)=side)
    (ht:before (tagRole candidate)=[]) (hc:before (aux .copyScratch)=[]):
    Runs program (timeBound edge side) (pc candidate 0) before (pc candidate 2)
      (Function.update before (tagRole candidate) (rawTag edge side)):=by
  let b1:=Function.update before (tagRole candidate) side
  have h0a:=copy_call (copySite candidate) (pc candidate 0) (pc candidate 1) (by cases candidate <;> rfl)
    before side [] (by cases candidate <;> exact hs) (by cases candidate <;> exact ht) hc
  have h0:Runs program (5*side.length+4) (pc candidate 0) before (pc candidate 1) b1:=by
    cases candidate <;> simpa [b1,tagRole,copySite,copyStack,copyPorts] using h0a
  have he':b1 (aux .edgeWord)=edge:=by
    cases candidate <;> simpa [b1,tagRole,aux] using he
  have hc':b1 (aux .copyScratch)=[]:=by
    cases candidate <;> simpa [b1,tagRole,aux] using hc
  have h1a:=frame_call (frameSite candidate) (pc candidate 1) (pc candidate 2) (by cases candidate <;> rfl)
    b1 edge side (by cases candidate <;> exact he') (by cases candidate <;> exact Function.update_self _ _ _) hc'
  have h1:Runs program (6*edge.length+5) (pc candidate 1) b1 (pc candidate 2)
      (Function.update b1 (tagRole candidate) (rawTag edge side)):=by cases candidate <;> exact h1a
  have heq:Function.update b1 (tagRole candidate) (rawTag edge side)=Function.update before (tagRole candidate) (rawTag edge side):=by
    dsimp only [b1]
    rw [Function.update_idem]
  rw [heq] at h1
  exact join h0 h1
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryTagBuild
