/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketOrientationPrepare
import RiemannGaussian.SemiprimeD1StackPacketOrientationLayout
import RiemannGaussian.SemiprimeD1StackPacketOrientationFinish
/-! # Entire actual three-input packet orientation source
The original routine appears only in the stopped-state meaning. Runtime has
only the two acquired physical colour vectors and the binary occurrence index.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketOrientationExecution
open SemiprimeD1StackPacketOrientation SemiprimeD1StackPacketOrientationPrimitives
open SemiprimeD1StackPacketOrientationRowView SemiprimeD1StackPacketOrientationPrepare
open SemiprimeD1StackPacketOrientationLoop SemiprimeD1StackPacketOrientationFinish
open SemiprimeD1StackPacketOrientationLayout SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits)
namespace Native
export SemiprimeD1OrientationBits (acquire)
end Native
local notation "ctl"=>Label.local
/-- Actual completely clear stopped bank with the three original inputs and exact old packet bytes retained. -/
def result (left right:List (List Bool)) (index:List Bool):Stack→List Bool:=
  Function.update (rowView (originals (vectorBits left) (vectorBits right) index) (fun _=>[]) [] (fun _=>[]) [] []
    (Native.acquire left right index).key (Native.acquire left right index).slots (Native.acquire left right index).high)
    answer [true]
/-- Actual full halt clears both transient flags and all genuine nested return frames. -/
def done (left right:List (List Bool)) (index:List Bool):C.State Stack Label:=⟨none,none,none,result left right index,[]⟩
/-- Exact source-front copy, paired-loop cap, actual finish and success/halt costs. -/
def timeBound (left right:List (List Bool)) (index:List Bool):Nat:=
  (5*(vectorBits left).length+5*(vectorBits right).length+5*index.length+12)+loopBound left right+
    (11*(Native.acquire left right index).high.length+2*(chunks left right).length+
      2*(Native.acquire left right index).slots.length+15)+2
/-- One whole actual source trace, preserving all three original words and producing exact raw-tail key, slots and high word. -/
theorem source_trace (left right:List (List Bool)) (index:List Bool) (hlen:left.length=right.length):
    ∃t,t+1 ≤ timeBound left right index ∧ Runs program t (ctl .start)
      (initial (vectorBits left) (vectorBits right) index).data (ctl .done) (result left right index) :=by
  let original:=originals (vectorBits left) (vectorBits right) index
  have h0:=prepare_run (vectorBits left) (vectorBits right) index
  obtain ⟨u,hu,h1⟩:=loop_run original left right index [] [] [] [] [] hlen
  simp only [List.append_nil] at h1
  have h2:=finish_run original (Native.acquire left right index).high (chunks left right).reverse
    (Native.acquire left right index).slots.reverse
  simp only [List.length_reverse,List.reverse_reverse] at h2
  rw [chunks_key left right index hlen] at h2
  let ready:=rowView original (fun _=>[]) [] (fun _=>[]) [] []
    (Native.acquire left right index).key (Native.acquire left right index).slots (Native.acquire left right index).high
  have h3:=push_run .accept (ctl .done) answer true ready rfl
  change Runs program 1 _ _ _ (Function.update ready answer [true]) at h3
  have h:=join (join (join h0 h1) h2) h3
  refine ⟨_,?_,h⟩
  unfold timeBound
  omega
/-- Whole source includes its final actual halt, with all19 result words specified exactly. -/
theorem source_run (left right:List (List Bool)) (index:List Bool) (hlen:left.length=right.length):
    ∃t ≤ timeBound left right index,SemiprimeD1StackCalls.run program t
      (initial (vectorBits left) (vectorBits right) index)=some (done left right index) :=by
  obtain ⟨t,ht,h⟩:=source_trace left right index hlen
  obtain ⟨out,he,hAt⟩:=h [] (initial (vectorBits left) (vectorBits right) index) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (ctl .done) rfl (result left right index) [] out hAt
  exact ⟨t+1,ht,by rw [SemiprimeD1StackReturnLink.run_add,he,Option.bind_some];exact hh⟩
end RiemannGaussian.SemiprimeD1StackPacketOrientationExecution
