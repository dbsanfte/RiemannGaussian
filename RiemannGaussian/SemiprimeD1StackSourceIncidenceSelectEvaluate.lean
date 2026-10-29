/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectCalls
import RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectView
/-! # Actual temporary extension and complete closed incidence evaluation
The acquired dictionary temporarily represents candidate::ids while the actual
selected vector remains unchanged. The real47-role source explicitly accepts and
preserves this arbitrary retained prefix, then returns its own binary score.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectEvaluate
open SemiprimeD1StackSourceIncidenceSelect SemiprimeD1StackSourceIncidenceSelectPrimitives
open SemiprimeD1StackSourceIncidenceSelectView SemiprimeD1StackSourceIncidenceSelectCalls
open SemiprimeD1StackProcedureTrace
local notation "ctl" => Label.local
/-- Proof-side interpretation of the actual stopped cache and physical source words; never a runtime operand. -/
def scoreInputs (ids:List (List Bool)) (id pfx:List Bool) (rows:List (List Bool×List Bool))
    (square cube fourth:List Bool) :SemiprimeD1StackSourceIncidenceEncoding.Inputs :=
  ⟨id::ids,id,[],pfx,rows,square,cube,fourth⟩
/-- Real extension and real ordered-pair query follow the same fixed program, with an actual paid call for each. -/
theorem evaluate_run (first:Bool) (ids:List (List Bool)) (id pfx:List Bool)
    (rows:List (List Bool×List Bool)) (square cube fourth catalogue owners factors todo reader savedKey bestID bestScore:List Bool) :
    ∃t ≤ 101*(id.length+(SemiprimeD1StackSourceEnvironmentEncoding.variableKey ids.length).length+1)+
        SemiprimeD1StackSourceIncidenceExecution.runBound (scoreInputs ids id pfx rows square cube fourth)+2,
      Runs program t (ctl (.install first))
        (clean ids id pfx (SemiprimeD1StackOwnerLookup.records rows []) square cube fourth catalogue owners factors
          todo reader savedKey bestID bestScore [])
        (ctl (.acquired first))
        (clean (id::ids) id pfx (SemiprimeD1StackOwnerLookup.records rows []) square cube fourth catalogue owners factors
          todo reader savedKey bestID bestScore
          (SemiprimeD1StackSourceIncidenceSpec.total (id::ids) square cube fourth rows)) :=by
  let stream:=SemiprimeD1StackOwnerLookup.records rows []
  let before:=clean ids id pfx stream square cube fourth catalogue owners factors todo reader savedKey bestID bestScore []
  have hi:∀k,before (environmentStack k)=
      (SemiprimeD1StackSourceEnvironmentExecution.extendReady ids id [] pfx).data k:=fun k=>rfl
  obtain ⟨t0,ht0,h0⟩:=extend_call (.install first) (.evaluate first) rfl before ids id [] pfx hi
  have he:withEnvironment before (SemiprimeD1StackSourceEnvironmentExecution.extendDone ids id [] pfx).data=
      clean (id::ids) id pfx stream square cube fourth catalogue owners factors todo reader savedKey bestID bestScore []:=by
    funext k
    rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k
        · rcases k with k|k <;> cases k <;> rfl
        · cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  rw [he] at h0
  let i:=scoreInputs ids id pfx rows square cube fourth
  let mid:=clean (id::ids) id pfx stream square cube fourth catalogue owners factors todo reader savedKey bestID bestScore []
  have hj:∀k,mid (queryStack k)=(SemiprimeD1StackSourceIncidenceEncoding.source i).data k:=by
    intro k
    exact clean_query (id::ids) id pfx stream square cube fourth catalogue owners factors todo reader savedKey bestID bestScore k
  obtain ⟨t1,ht1,h1⟩:=query_call first mid i hj
  have hf:Sum.elim (SemiprimeD1StackSourceIncidenceEncoding.result i) (fun k=>mid (aux k))=
      clean (id::ids) id pfx stream square cube fourth catalogue owners factors todo reader savedKey bestID bestScore
        (SemiprimeD1StackSourceIncidenceSpec.total (id::ids) square cube fourth rows):=by
    funext k
    rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k
        · rcases k with k|k <;> cases k <;> rfl
        · cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  rw [hf] at h1
  dsimp only [i] at ht1
  exact ⟨t0+t1,by omega,join h0 h1⟩
end RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectEvaluate
