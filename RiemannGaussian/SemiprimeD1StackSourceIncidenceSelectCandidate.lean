/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectParse
import RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectEvaluate
import RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectIncumbent
import RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectRestore
/-! # One complete actual temporary candidate step
The fixed program parses both actual catalogue fields, extends the actual old
dictionary, calls the closed incidence source, retains only strict improvement,
and physically removes its temporary head and restores the acquired saved key.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectCandidate
open SemiprimeD1StackSourceIncidenceSelect SemiprimeD1StackSourceIncidenceSelectPrimitives
open SemiprimeD1StackSourceIncidenceSelectView SemiprimeD1StackProcedureTrace
namespace E
export SemiprimeD1StackSourceEnvironmentEncoding (variableKey)
end E
local notation "ctl" => Label.local
/-- Exact word emitted by the real closed query after installing this actual candidate. -/
def scoreWord (ids:List (List Bool)) (id:List Bool) (rows:List (List Bool×List Bool))
    (square cube fourth:List Bool) :List Bool :=
  SemiprimeD1StackSourceIncidenceSpec.total (id::ids) square cube fourth rows
/-- Finite first-candidate control and actual strict improvement determine the retained word pair. -/
def nextBest (first:Bool) (oldID oldScore id newScore:List Bool) :List Bool×List Bool :=
  if first then (id,newScore) else SemiprimeD1StackSourceIncidenceSelectSpec.scoredPick (oldID,oldScore) (id,newScore)
/-- Own actual primitive/call cap, including complete47-role query and both physical rollback fields. -/
def candidateBound (ids:List (List Bool)) (id colour pfx:List Bool) (rows:List (List Bool×List Bool))
    (square cube fourth oldID oldScore:List Bool) :Nat :=
  (8*id.length+9*colour.length+18)+
    (101*(id.length+(E.variableKey ids.length).length+1)+
      SemiprimeD1StackSourceIncidenceExecution.runBound
        (SemiprimeD1StackSourceIncidenceSelectEvaluate.scoreInputs ids id pfx rows square cube fourth)+2)+
    100*(id.length+(scoreWord ids id rows square cube fourth).length+oldID.length+oldScore.length+1)+
    50*((E.variableKey ids.length).length+id.length+1)
/-- Complete candidate step preserves the exact old dictionary/key/prefix and physically retains the exact best pair. -/
theorem candidate_run (first:Bool) (ids:List (List Bool))
    (pfx:List Bool) (rows:List (List Bool×List Bool))
    (square cube fourth catalogue owners factors todo oldID oldScore id colour:List Bool)
    (tail:List (List Bool×List Bool)) (hfirst:first=true → oldID=[] ∧ oldScore=[]) :
    ∃t ≤ candidateBound ids id colour pfx rows square cube fourth oldID oldScore,
      Runs program t (ctl (.header first))
        (clean ids [] pfx (SemiprimeD1StackOwnerLookup.records rows []) square cube fourth catalogue owners factors todo
          (SemiprimeD1StackOwnerLookup.records ((id,colour)::tail) []) (E.variableKey ids.length) oldID oldScore [])
        (ctl (.header false))
        (clean ids [] pfx (SemiprimeD1StackOwnerLookup.records rows []) square cube fourth catalogue owners factors todo
          (SemiprimeD1StackOwnerLookup.records tail []) (E.variableKey ids.length)
          (nextBest first oldID oldScore id (scoreWord ids id rows square cube fourth)).1
          (nextBest first oldID oldScore id (scoreWord ids id rows square cube fourth)).2 []) :=by
  let stream:=SemiprimeD1StackOwnerLookup.records rows []
  let reader:=SemiprimeD1StackOwnerLookup.records tail []
  let key:=E.variableKey ids.length
  let newScore:=scoreWord ids id rows square cube fourth
  have h0:=SemiprimeD1StackSourceIncidenceSelectParse.candidate_run first ids pfx stream square cube fourth catalogue owners factors
    todo key oldID oldScore id colour tail
  obtain ⟨t1,ht1,h1⟩:=SemiprimeD1StackSourceIncidenceSelectEvaluate.evaluate_run first ids id pfx rows square cube fourth
    catalogue owners factors todo reader key oldID oldScore
  have hi:∃t ≤ 100*(id.length+newScore.length+oldID.length+oldScore.length+1),
      Runs program t (ctl (.acquired first))
        (clean (id::ids) id pfx stream square cube fourth catalogue owners factors todo reader key oldID oldScore newScore)
        (ctl .rollbackTag)
        (clean (id::ids) id pfx stream square cube fourth catalogue owners factors todo reader key
          (nextBest first oldID oldScore id newScore).1 (nextBest first oldID oldScore id newScore).2 []):=by
    cases first with
    | false=>
      exact SemiprimeD1StackSourceIncidenceSelectIncumbent.later_run (id::ids) id pfx stream square cube fourth
        catalogue owners factors todo reader key oldID oldScore newScore
    | true=>
      obtain ⟨rfl,rfl⟩:=hfirst rfl
      exact ⟨_,by omega,SemiprimeD1StackSourceIncidenceSelectIncumbent.first_run (id::ids) id pfx stream square cube fourth
        catalogue owners factors todo reader key newScore⟩
  obtain ⟨t2,ht2,h2⟩:=hi
  obtain ⟨t3,ht3,h3⟩:=SemiprimeD1StackSourceIncidenceSelectRestore.restore_run ids id pfx stream square cube fourth catalogue owners factors
    todo reader (nextBest first oldID oldScore id newScore).1 (nextBest first oldID oldScore id newScore).2
  have h:=join (join (join h0 h1) h2) h3
  refine ⟨_,?_,h⟩
  unfold candidateBound
  dsimp only [newScore,key] at ht2 ht3
  omega
end RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectCandidate
