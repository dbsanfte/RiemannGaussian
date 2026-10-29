/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPhaseParametersResources
/-! # Uniform bound for the same physical complete phase-list sweep -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootPhaseParametersUniform
open SemiprimeD1StackRootPhaseParameters SemiprimeD1StackRootPhaseParametersEncoding
open SemiprimeD1StackRootPhaseParametersRows SemiprimeD1StackRootPhaseParametersLoop
open SemiprimeD1StackRootPhaseParametersResources
open SemiprimeSourceHistogramKeyBits (frame)
/-- The next actual reader suffix cannot exceed the complete acquired vector width. -/
theorem tail_tape_le (t:List Bool) (ts:List (List Bool)) (terminal:List Bool) :
    (rowTape ts terminal).length ≤ (rowTape (t::ts) terminal).length :=by
  change _ ≤ (true::frame t (rowTape ts terminal)).length
  rw [List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length]
  omega
/-- Whole actual sweep counts accumulated heap and unary references: the
quadratic allocation scan remains explicitly paid in K, with all126 retained cells. -/
theorem sweepBound_le (root:G.Stack→List Bool) (a u edges:Nat) (rows cached:List (List Bool))
    (terminal:List Bool) (K R:Nat) (hR:1 ≤ R) (hK:K ≤ R) (hroot:rootMass root ≤ R)
    (ha:a ≤ R) (hu:u ≤ R) (hm:edges ≤ R) (hsize:cached.length+rows.length ≤ K)
    (hc:∀w∈cached,w.length ≤ R)
    (hr:∀t∈rows,t.length ≤ R ∧
      SemiprimeD1StackPhaseWorkingPrecisionExecution.runBound a u edges t [false,true] ≤ R ∧
      stoppedMass a u edges t ≤ R ∧ (record a u edges t).length ≤ R)
    (hbytes:(rowTape rows terminal).length ≤ R) :
    sweepBound root a u edges rows cached terminal ≤ rows.length*(10^8*(K+1)*R)+1 :=by
  induction rows generalizing cached with
  | nil=>simp only [sweepBound,List.length_nil,Nat.zero_mul,Nat.zero_add,le_refl]
  | cons t ts ih=>
    obtain ⟨ht,hclock,hphase,hrecord⟩:=hr t List.mem_cons_self
    have htail:(rowTape ts terminal).length ≤ R:=(tail_tape_le t ts terminal).trans hbytes
    have hn:cached.length ≤ K:=by simp only [List.length_cons] at hsize;omega
    have hrow:=rowBound_le root a u edges t (rowTape ts terminal)
      (SemiprimeD1StackHeapAllocate.heapBytes cached) cached.length K R hR hn hK hroot
      ha hu hm ht htail hclock hphase hrecord (heap_bound cached R hc)
    have hnew:∀w∈cached++[record a u edges t],w.length ≤ R:=by
      intro w hw
      rcases List.mem_append.mp hw with hw|hw
      · exact hc w hw
      · have he:w=record a u edges t:=List.mem_singleton.mp hw
        rw [he]
        exact hrecord
    have hnewsize:(cached++[record a u edges t]).length+ts.length ≤ K:=by
      simpa only [List.length_append,List.length_singleton,List.length_cons,List.length_nil,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hsize
    have h1:=ih (cached++[record a u edges t]) hnewsize hnew
      (fun word hw=>hr word (List.mem_cons_of_mem t hw)) htail
    change rowBound _ _ _ _ _ _ _ _ _+sweepBound _ _ _ _ _ _ _ ≤ _
    simp only [List.length_cons]
    nlinarith
end RiemannGaussian.SemiprimeD1StackRootPhaseParametersUniform
