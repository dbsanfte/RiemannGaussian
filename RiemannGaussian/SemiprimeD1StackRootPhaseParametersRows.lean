/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPhaseParametersSource
import RiemannGaussian.SemiprimeD1StackRootPhaseParametersSerialize
import RiemannGaussian.SemiprimeD1StackRootPhaseParametersCleanup
import RiemannGaussian.SemiprimeD1StackRootPhaseParametersView
/-! # One complete actual phase: parse, source, forty-eight frames, heap, reference, drain -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootPhaseParametersRows
open SemiprimeD1StackRootPhaseParameters SemiprimeD1StackRootPhaseParametersEncoding
open SemiprimeD1StackRootPhaseParametersPrimitives SemiprimeD1StackRootPhaseParametersCalls
open SemiprimeD1StackRootPhaseParametersView SemiprimeD1StackRootPhaseParametersSource
open SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
/-- Exact stopped forty-eight-word result, never a source input. -/
def stopped (a u edges:Nat) (t:List Bool) : P.Stack→List Bool :=
  SemiprimeD1StackPhaseWorkingPrecisionComponents.result a u edges t [false,true]
/-- Actual one-reference reverse-log effect, retaining its chronological position. -/
def nextHistory (n:Nat) (hist:List Bool) : List Bool :=
  (true::frame (List.replicate n true) []).reverse++hist
/-- Complete data immediately before the physical fifty-one-word cleanup. -/
def logged (root:G.Stack→List Bool) (a u edges:Nat) (t tail hp:List Bool) (n:Nat) (hist:List Bool) : Stack→List Bool :=
  view root (stopped a u edges t) tail t (record a u edges t) (frame (record a u edges t) hp)
    (List.replicate (n+1) true) (List.replicate n true) (nextHistory n hist) []
/-- Same-program per-row bound pays every actual source/copy/parser/frame,
allocator/reference restoration and complete physical cleanup, including EOF. -/
def rowBound (root:G.Stack→List Bool) (a u edges:Nat) (t tail hp:List Bool) (n:Nat) (hist:List Bool) : Nat :=
  1000*(a+u+edges+t.length+n+
    SemiprimeD1StackPhaseWorkingPrecisionExecution.runBound a u edges t [false,true]+
    SemiprimeD1StackRootPhaseParametersSerialize.phaseMass (view root (stopped a u edges t) tail t [] hp (List.replicate n true) [] hist [])+
    (record a u edges t).length+
    SemiprimeD1StackRootPhaseParametersCleanup.mass (logged root a u edges t tail hp n hist)+1)
/-- A real vector-row header pop exposes its actual following framed phase index. -/
theorem header_row (root:G.Stack→List Bool) (t tail hp:List Bool) (n:Nat) (hist:List Bool) :
    Runs program 1 .header (loop root (true::frame t tail) hp n hist) .parse
      (view root (fun _=>[]) (frame t tail) [] [] hp (List.replicate n true) [] hist []) :=by
  apply one_base program _ _ (.pop (aux .reader) .finishSeed .finishSeed .parse) _ _ rfl
  · rfl
  · exact update_reader _ _ _ _ _ _ _ _ _ _ _
/-- The true validity bit is physically popped; it never becomes a supplied verdict. -/
theorem valid_row (root:G.Stack→List Bool) (t tail hp:List Bool) (n:Nat) (hist:List Bool) :
    let bank:=view root (fun _=>[]) tail t [] hp (List.replicate n true) [] hist []
    Runs program 1 .check (Function.update bank (aux .valid) [true]) (.copySite 1) bank :=by
  dsimp only
  apply one_base program _ _ (.pop (aux .valid) .abort .abort (.copySite 1)) _ _ rfl
  · rfl
  · change Function.update (Function.update (view root (fun _=>[]) tail t [] hp (List.replicate n true) [] hist []) (aux .valid) [true]) (aux .valid) []=_
    rw [Function.update_idem]
    exact Function.update_eq_self _ _
/-- Complete real phase-row path preserves ALL126 source/grid cells and exact
chronological heap/reference state, while clearing ALL48 phase roles before looping. -/
theorem row_run (root:G.Stack→List Bool) (a u edges:Nat) (t tail hp:List Bool) (n:Nat) (hist:List Bool)
    (ha:root G.exponent=List.replicate a true)
    (hu:root (G.rootStack (SemiprimeD1StackRootRecursiveControl.sourceStack SemiprimeD1StackRootParameters.levels))=List.replicate u true)
    (hm:root (G.rootStack (SemiprimeD1StackRootRecursiveControl.sourceStack SemiprimeD1StackRootParameters.edges))=List.replicate edges true) :
    ∃q≤rowBound root a u edges t tail hp n hist,
      Runs program q .header (loop root (true::frame t tail) hp n hist) .header
        (loop root tail (frame (record a u edges t) hp) (n+1) (nextHistory n hist)) :=by
  let w:=work tail t [] hp (List.replicate n true) [] hist []
  let acquired:=view root (stopped a u edges t) tail t [] hp (List.replicate n true) [] hist []
  let framed:=view root (stopped a u edges t) tail t (record a u edges t) hp (List.replicate n true) [] hist []
  let allocated:=view root (stopped a u edges t) tail t (record a u edges t)
    (frame (record a u edges t) hp) (List.replicate (n+1) true) (List.replicate n true) hist []
  have h0:=header_row root t tail hp n hist
  have h1:=parse_call (view root (fun _=>[]) (frame t tail) [] [] hp (List.replicate n true) [] hist []) t tail rfl rfl rfl rfl
  rw [update_reader,SemiprimeD1StackRootPhaseParametersView.update_index] at h1
  have h2:=valid_row root t tail hp n hist
  dsimp only at h2
  have h3:=setup_run root w a u edges t ha hu hm rfl rfl
  obtain ⟨p,hpBound,h4⟩:=phase_call (withInputs root w a u edges t [false,true]) a u edges t (fun _=>rfl)
  change Runs program (p+1) .phaseCall (withInputs root w a u edges t [false,true]) (.serialize 0) acquired at h4
  obtain ⟨s,hsBound,h5⟩:=SemiprimeD1StackRootPhaseParametersSerialize.serialize_run acquired rfl rfl
  have he5:Function.update acquired (aux .record) (phaseRecord (fun k=>acquired (phaseStack k)))=framed:=by
    exact update_record _ _ _ _ _ _ _ _ _ _ _
  rw [he5] at h5
  have h6:=allocate_call framed rfl rfl rfl
  change Runs program (5*(List.replicate n true).length+6*(record a u edges t).length+8) .allocate framed .logReference
    (Function.update (Function.update (Function.update framed (aux .heap) (frame (record a u edges t) hp))
      (aux .counter) (true::List.replicate n true)) (aux .reference) (List.replicate n true)) at h6
  rw [List.length_replicate] at h6
  have he6:Function.update (Function.update (Function.update framed (aux .heap) (frame (record a u edges t) hp))
      (aux .counter) (true::List.replicate n true)) (aux .reference) (List.replicate n true)=allocated:=by
    dsimp only [framed,allocated]
    rw [update_heap,update_counter,update_reference]
    rfl
  rw [he6] at h6
  obtain ⟨r,hrBound,h7⟩:=reference_call allocated rfl
  have he7:Function.update allocated (aux .refsHistory)
      ((true::frame (allocated (aux .reference)) []).reverse++allocated (aux .refsHistory))=
      logged root a u edges t tail hp n hist:=by
    exact update_history _ _ _ _ _ _ _ _ _ _ _
  rw [he7] at h7
  obtain ⟨c,hcBound,h8⟩:=SemiprimeD1StackRootPhaseParametersCleanup.cleanup_run root (stopped a u edges t)
    tail t (record a u edges t) (frame (record a u edges t) hp) (List.replicate (n+1) true)
    (List.replicate n true) (nextHistory n hist) []
  have hh:=compose (compose (compose (compose (compose (compose (compose (compose h0 h1) h2) h3) h4) h5) h6) h7) h8
  refine ⟨_,?_,hh⟩
  change r≤6*(2*(List.replicate n true).length+3) at hrBound
  rw [List.length_replicate] at hrBound
  change s≤48*(6*SemiprimeD1StackRootPhaseParametersSerialize.phaseMass acquired+5)+1 at hsBound
  change c≤51*(SemiprimeD1StackRootPhaseParametersCleanup.mass (logged root a u edges t tail hp n hist)+1)+1 at hcBound
  unfold rowBound
  change _≤1000*(a+u+edges+t.length+n+_+SemiprimeD1StackRootPhaseParametersSerialize.phaseMass acquired+_+_+1)
  omega
end RiemannGaussian.SemiprimeD1StackRootPhaseParametersRows
