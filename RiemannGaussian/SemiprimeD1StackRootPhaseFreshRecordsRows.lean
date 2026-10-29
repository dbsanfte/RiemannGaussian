/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsSource
import RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsCleanView
import RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsSerialize
/-! # One physical reference, whole cached Fresh call,85 frames, allocation and145 drains -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsRows
open SemiprimeD1StackRootPhaseFreshRecords SemiprimeD1StackRootPhaseFreshRecordsEncoding
open SemiprimeD1StackRootPhaseFreshRecordsPrimitives SemiprimeD1StackRootPhaseFreshRecordsCalls
open SemiprimeD1StackRootPhaseFreshRecordsView SemiprimeD1StackRootPhaseFreshRecordsSource
open SemiprimeD1StackRootPhaseFreshRecordsCleanView SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
namespace E
export SemiprimeD1StackPhaseCacheFreshExecution (heap source done runBound)
end E
/-- Actual stopped logical client bank, including every shared P48 and Fresh field. -/
def stopped (root:R.Stack→List Bool) (a u edges:Nat) (t pointer:List Bool) :Q.Stack→List Bool :=
  SemiprimeD1StackPhaseCacheFreshComponents.completed a u edges t [false,true] []
    (root R.heap) (root (R.aux .counter)) pointer
/-- The issued reference is logged by the real restoring body in chronological reverse history. -/
def nextHistory (n:Nat) (hist:List Bool) :List Bool :=
  (true::frame (List.replicate n true) []).reverse++hist
/-- Complete physical store after the client returned, before its85 framing calls. -/
def acquired (root:R.Stack→List Bool) (a u edges:Nat) (t pointer tail hp:List Bool) (n:Nat) (hist:List Bool) :Stack→List Bool :=
  view root (stopped root a u edges t pointer) (work tail [] hp (List.replicate n true) [] hist [])
/-- All actual work at the145-drain entry, with immutable source heap/count retained. -/
def logged (root:R.Stack→List Bool) (a u edges:Nat) (t pointer tail hp:List Bool) (n:Nat) (hist:List Bool) :Stack→List Bool :=
  view root (stopped root a u edges t pointer)
    (work tail (record a u edges t) (frame (record a u edges t) hp)
      (List.replicate (n+1) true) (List.replicate n true) (nextHistory n hist) [])
/-- Own physical row allowance pays the actual client value expansions, framing, heap and cleanup. -/
def rowBound (root:R.Stack→List Bool) (bs:List (SemiprimeD1StackPhaseWorkingPrecision.Stack→List Bool))
    (i:Fin bs.length) (a u edges:Nat) (t tail hp:List Bool) (n:Nat) (hist:List Bool) :Nat :=
  1000*(i.val+n+E.runBound bs i a u edges t [false,true] []+
    SemiprimeD1StackRootPhaseFreshRecordsSerialize.freshMass (acquired root a u edges t (List.replicate i.val true) tail hp n hist)+
    (record a u edges t).length+
    SemiprimeD1StackRootPhaseFreshRecordsCleanup.mass (logged root a u edges t (List.replicate i.val true) tail hp n hist)+1)
/-- A reference field is installed only by a physical copied-byte update. -/
theorem update_input_reference (hp cn ref axes next:List Bool) :
    Function.update (Q.input hp cn ref axes) I.sourceReference next=Q.input hp cn next axes :=by
  funext k
  by_cases hk:k=I.sourceReference
  · subst k;rw [Function.update_same];rfl
  · rw [Function.update_of_ne hk,input_only,input_only]
    by_cases hh:k=I.sourceHeap
    · simp only [hh,ite_true]
    · by_cases hc:k=I.sourceCounter
      · simp only [hc,ite_true]
      · simp only [hh,hc,hk,ite_false]
/-- Actual row constructor pop exposes the following reference frame. -/
theorem header_row (root:R.Stack→List Bool) (pointer tail hp:List Bool) (n:Nat) (hist:List Bool) :
    Runs program 1 .header (loop root (true::frame pointer tail) hp n hist) .parse
      (view root (cacheInput root [] [false]) (work (frame pointer tail) [] hp (List.replicate n true) [] hist [])) :=by
  apply one_base program _ _ (.pop (aux .reader) .finishSeed .finishSeed .parse) _ _ rfl
  · rfl
  · exact update_reader _ _ _ _ _ _ _ _ _ _
/-- Validity is an actual parser-produced true bit, physically consumed before the source call. -/
theorem valid_row (root:R.Stack→List Bool) (pointer tail hp:List Bool) (n:Nat) (hist:List Bool) :
    let bank:=view root (cacheInput root pointer [false]) (work tail [] hp (List.replicate n true) [] hist [])
    Runs program 1 .check (Function.update bank (aux .valid) [true]) .freshCall bank :=by
  dsimp only
  apply one_base program _ _ (.pop (aux .valid) .abort .abort .freshCall) _ _ rfl
  · rfl
  · change Function.update (Function.update (view root (cacheInput root pointer [false])
      (work tail [] hp (List.replicate n true) [] hist [])) (aux .valid) [true]) (aux .valid) []=_
    rw [Function.update_idem]
    exact Function.update_eq_self _ _
/-- All85 framed words are taken from actual stopped Fresh fields, with shared P48 aliases respected. -/
theorem acquired_fresh (root:R.Stack→List Bool) (a u edges:Nat) (t pointer tail hp:List Bool)
    (n:Nat) (hist:List Bool) (k:F.Stack) :
    acquired root a u edges t pointer tail hp n hist (freshStack k)=freshResult a u edges t k :=by
  rw [acquired,view_fresh]
  exact SemiprimeD1StackPhaseCacheFreshComponents.fresh_data _ _ k
/-- Complete same-program row preserves all188 original source cells, emits its85-word
record once and physically clears all client work before advancing to the next reference. -/
theorem row_run (root:R.Stack→List Bool) (bs:List (SemiprimeD1StackPhaseWorkingPrecision.Stack→List Bool))
    (i:Fin bs.length) (a u edges:Nat) (t tail hp:List Bool) (n:Nat) (hist:List Bool)
    (hh:root R.heap=E.heap bs) (hc:root (R.aux .counter)=List.replicate bs.length true)
    (hb:bs[i.val]=SemiprimeD1StackPhaseCacheFreshComponents.phase a u edges t [false,true]) :
    ∃q ≤ rowBound root bs i a u edges t tail hp n hist,
      Runs program q .header (loop root (true::frame (List.replicate i.val true) tail) hp n hist) .header
        (loop root tail (frame (record a u edges t) hp) (n+1) (nextHistory n hist)) :=by
  let ptr:=List.replicate i.val true
  let w:=work tail [] hp (List.replicate n true) [] hist []
  let initialQ:=cacheInput root ptr [false]
  let qdone:=stopped root a u edges t ptr
  let got:=acquired root a u edges t ptr tail hp n hist
  let framed:=view root qdone (work tail (record a u edges t) hp (List.replicate n true) [] hist [])
  let allocated:=view root qdone (work tail (record a u edges t) (frame (record a u edges t) hp)
    (List.replicate (n+1) true) (List.replicate n true) hist [])
  have h0:=header_row root ptr tail hp n hist
  have h1:=parse_call (view root (cacheInput root [] [false]) (work (frame ptr tail) [] hp (List.replicate n true) [] hist [])) ptr tail rfl rfl rfl rfl
  rw [update_reader,update_pointer] at h1
  simp only [cacheInput,update_input_reference] at h1
  have h2:=valid_row root ptr tail hp n hist
  dsimp only at h2
  obtain ⟨p,hpBound,h3⟩:=fresh_call root w bs i a u edges t hb
  have hin:(E.source bs i []).data=initialQ:=by
    change Q.input (E.heap bs) (List.replicate bs.length true) ptr [false]=cacheInput root ptr [false]
    simp only [cacheInput,hh,hc]
  have hout:(E.done bs i a u edges t [false,true] []).data=qdone:=by
    change SemiprimeD1StackPhaseCacheFreshComponents.completed _ _ _ _ _ _ _ _ _=_
    simp only [qdone,stopped,hh,hc,ptr]
  rw [hin,hout] at h3
  change Runs program (p+1) .freshCall (view root initialQ w) (.serialize 0) got at h3
  obtain ⟨s,hsBound,h4⟩:=SemiprimeD1StackRootPhaseFreshRecordsSerialize.serialize_run got rfl rfl
  have he4:Function.update got (aux .record) (freshRecord (fun k=>got (freshStack k)))=framed:=by
    have he:(fun k=>got (freshStack k))=freshResult a u edges t:=funext (fun k=>acquired_fresh root a u edges t ptr tail hp n hist k)
    rw [he]
    exact update_currentRecord _ _ _ _ _ _ _ _ _ _
  rw [he4] at h4
  have h5:=allocate_call framed rfl rfl rfl
  change Runs program (5*(List.replicate n true).length+6*(record a u edges t).length+8) .allocate framed .logReference
    (Function.update (Function.update (Function.update framed (aux .heap) (frame (record a u edges t) hp))
      (aux .counter) (true::List.replicate n true)) (aux .reference) (List.replicate n true)) at h5
  rw [List.length_replicate,update_heap,update_counter,update_reference] at h5
  change Runs program _ .allocate framed .logReference allocated at h5
  obtain ⟨r,hrBound,h6⟩:=reference_call allocated rfl
  have he6:Function.update allocated (aux .refsHistory)
      ((true::frame (allocated (aux .reference)) []).reverse++allocated (aux .refsHistory))=
      logged root a u edges t ptr tail hp n hist:=by
    exact update_history _ _ _ _ _ _ _ _ _ _
  rw [he6] at h6
  obtain ⟨c,hcBound,h7⟩:=SemiprimeD1StackRootPhaseFreshRecordsCleanup.cleanup_run (logged root a u edges t ptr tail hp n hist)
  rw [logged,cleared_view] at h7
  have hclean:Q.input (qdone I.sourceHeap) (qdone I.sourceCounter) [] (qdone I.oldHeader)=cacheInput root [] [false]:=by
    change Q.input (root R.heap) (root (R.aux .counter)) []
      (SemiprimeD1StackPhaseCacheFreshComponents.completed _ _ _ _ _ _ _ _ _ I.oldHeader)=_
    rw [completed_header]
    rfl
  change Q.input (qdone I.sourceHeap) (qdone I.sourceCounter) [] (qdone I.oldHeader)=_ at hclean
  rw [hclean] at h7
  change Runs program c (.clear 0) _ .header (loop root tail (frame (record a u edges t) hp) (n+1) (nextHistory n hist)) at h7
  have hall:=compose (compose (compose (compose (compose (compose (compose h0 h1) h2) h3) h4) h5) h6) h7
  refine ⟨_,?_,hall⟩
  change r ≤ 6*(2*(List.replicate n true).length+3) at hrBound
  rw [List.length_replicate] at hrBound
  change s ≤ 85*(6*SemiprimeD1StackRootPhaseFreshRecordsSerialize.freshMass got+5)+1 at hsBound
  unfold rowBound
  change _ ≤ 1000*(i.val+n+_+SemiprimeD1StackRootPhaseFreshRecordsSerialize.freshMass got+_+_+1)
  dsimp only [ptr] at hcBound
  simp only [ptr,List.length_replicate]
  omega
end RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsRows
