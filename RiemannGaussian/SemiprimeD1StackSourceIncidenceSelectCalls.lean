/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectPrimitives
/-! # Actual environment initialization/extension and complete closed scorer calls
Every call instantiates a proved real source trace. All63 fields outside the
component image, and every genuine outer return frame, are preserved.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectCalls
open SemiprimeD1StackSourceIncidenceSelect SemiprimeD1StackSourceIncidenceSelectPrimitives
open SemiprimeD1StackProcedureTrace
local notation "ctl" => Label.local
/-- Replace exactly the25 actual shared environment roles, preserving every other38 words. -/
def withEnvironment (before:Stack→List Bool) (env:E.Stack→List Bool) :Stack→List Bool :=
  Sum.elim (Sum.elim env (fun k=>before (queryStack (Q.aux k)))) (fun k=>before (aux k))
/-- Exact inclusion relation outside the25-role shared environment image. -/
theorem withEnvironment_rel (before:Stack→List Bool) (env:E.Stack→List Bool) :
    Link.DataRel environmentStack before env (withEnvironment before env) :=by
  constructor
  · intro k;rfl
  · intro k hk
    rcases k with k|k
    · rcases k with k|k
      · exact (hk k rfl).elim
      · rfl
    · rfl
/-- A physically empty environment is initialized by the real push/return source and its actual outer call. -/
theorem initialize_call (before:Stack→List Bool) (chosen q pfx:List Bool)
    (hi:∀k,before (environmentStack k)=
      (SemiprimeD1StackSourceEnvironmentExecution.initializeReady chosen q pfx).data k) :
    Runs program 3 (ctl .initialize) before (ctl .copyOwners)
      (withEnvironment before (SemiprimeD1StackSourceEnvironmentExecution.initializeDone chosen q pfx).data) :=by
  apply environment_call .initialize .copyOwners (.local .initialize) rfl 2
    (SemiprimeD1StackSourceEnvironmentExecution.initializeReady chosen q pfx)
    (SemiprimeD1StackSourceEnvironmentExecution.initializeDone chosen q pfx) before _ rfl rfl rfl rfl
    (SemiprimeD1StackSourceEnvironmentExecution.initialize_run chosen q pfx)
  · exact ⟨hi,fun _ _=>rfl⟩
  · exact withEnvironment_rel before _
/-- Temporary and committed candidates use the SAME literal acquired-key extension, retaining arbitrary selected-vector bytes. -/
theorem extend_call (pc next:Control)
    (hc:program (ctl pc)=.call (environmentLabel (.local .extend)) (ctl next))
    (before:Stack→List Bool) (ids:List (List Bool)) (chosen q pfx:List Bool)
    (hi:∀k,before (environmentStack k)=
      (SemiprimeD1StackSourceEnvironmentExecution.extendReady ids chosen q pfx).data k) :
    ∃t ≤ 101*(chosen.length+(SemiprimeD1StackSourceEnvironmentEncoding.variableKey ids.length).length+1)+1,
      Runs program t (ctl pc) before (ctl next)
        (withEnvironment before (SemiprimeD1StackSourceEnvironmentExecution.extendDone ids chosen q pfx).data) :=by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackSourceEnvironmentExecution.extend_run ids chosen q pfx
  refine ⟨t+1,by omega,?_⟩
  apply environment_call pc next (.local .extend) hc t
    (SemiprimeD1StackSourceEnvironmentExecution.extendReady ids chosen q pfx)
    (SemiprimeD1StackSourceEnvironmentExecution.extendDone ids chosen q pfx) before _ rfl rfl rfl rfl hr
  · exact ⟨hi,fun _ _=>rfl⟩
  · exact withEnvironment_rel before _
/-- The complete closed47-role scorer is really called after each temporary extension; all25 environment roles are restored. -/
theorem query_call (first:Bool) (before:Stack→List Bool)
    (i:SemiprimeD1StackSourceIncidenceEncoding.Inputs)
    (hi:∀k,before (queryStack k)=(SemiprimeD1StackSourceIncidenceEncoding.source i).data k) :
    ∃t ≤ SemiprimeD1StackSourceIncidenceExecution.runBound i+1,
      Runs program t (ctl (.evaluate first)) before (ctl (.acquired first))
        (Sum.elim (SemiprimeD1StackSourceIncidenceEncoding.result i) (fun k=>before (aux k))) :=by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackSourceIncidenceExecution.source_run i
  refine ⟨t+1,by omega,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program queryStack Label.queryCode Sum.inl_injective
    Q.program .start (fun _=>rfl) (ctl (.evaluate first)) (ctl (.acquired first)) rfl t
    (SemiprimeD1StackSourceIncidenceEncoding.source i) (SemiprimeD1StackSourceIncidenceEncoding.done i)
    before _ rfl rfl rfl rfl hr
  · exact ⟨hi,fun _ _=>rfl⟩
  · constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k
      · exact (hk k rfl).elim
      · rfl
end RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectCalls
