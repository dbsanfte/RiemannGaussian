/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackAllDescriptorRecordSpec
/-! # Closed actual eighteen-tag source execution with complete private cleanup -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 1000000
namespace RiemannGaussian.SemiprimeD1StackAllDescriptorRecordExecution
open SemiprimeD1StackAllDescriptorRecord SemiprimeD1StackAllDescriptorRecordPrimitives
open SemiprimeD1StackAllDescriptorRecordCalls SemiprimeD1StackAllDescriptorRecordSpec
open SemiprimeD1StackAllDescriptorRecordCleanup SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits)
/-- Every literal original constructor case invokes its complete actual fixed
component; all checker/template/mode/selector suppliers are discharged concretely. -/
theorem component_run (code:Fin 18) (raw:Fin 6→List Bool)
    (htag:raw 1=List.replicate code.val true)
    (h2:raw 2=SemiprimeD1StackUnaryDivmod.unary (raw 2).length)
    (h3:raw 3=SemiprimeD1StackUnaryDivmod.unary (raw 3).length)
    (h4:raw 4=SemiprimeD1StackUnaryDivmod.unary (raw 4).length)
    (htr:(code.val=1∨code.val=2∨code.val=3)→(raw 2).length<3)
    (hc:SemiprimeSourceCompactBits.Compact (raw 0)) (hN:0<SemiprimeBitArithmetic.bitValue (raw 0))
    (words:List (List Bool)) (hist out:List Bool) :
    ∃t≤ componentClock code raw words hist out,
      Runs program t (.inl (.record (family code))) (cleanData raw (vectorBits words) hist out)
        (.inl (.clear 0)) (afterComponent code raw words hist out) :=by
  have hb:raw 0≠[]:=by intro he;rw [he] at hN;exact (Nat.not_lt_zero _ hN).elim
  fin_cases code
  · simpa [componentClock,afterComponent,family] using input_call raw hb words hist out
  · simpa [componentClock,afterComponent,family] using transform_call raw false ⟨(raw 2).length,htr (by simp)⟩ htag h2 hc hN words hist out
  · simpa [componentClock,afterComponent,family] using scale_call raw ⟨(raw 2).length,htr (by simp)⟩ htag h2 h3 h4 hc hN words hist out
  · simpa [componentClock,afterComponent,family] using transform_call raw true ⟨(raw 2).length,htr (by simp)⟩ htag h2 hc hN words hist out
  · simpa [componentClock,afterComponent,family] using product_call raw hb words hist out
  · simpa [componentClock,afterComponent,family] using boundary_call raw hb words hist out
  · simpa [componentClock,afterComponent,family] using carry_call raw hb words hist out
  · simpa [componentClock,afterComponent,family] using boundary_call raw hb words hist out
  · simpa [componentClock,afterComponent,family] using boolean_call .orGate raw words hist out
  · simpa [componentClock,afterComponent,family] using boolean_call .inputCheck raw words hist out
  · simpa [componentClock,afterComponent,family] using boolean_call .equality raw words hist out
  · simpa [componentClock,afterComponent,family] using boolean_call .equality raw words hist out
  · simpa [componentClock,afterComponent,family] using boolean_call .equality raw words hist out
  · simpa [componentClock,afterComponent,family] using boolean_call .equality raw words hist out
  · simpa [componentClock,afterComponent,family] using boolean_call .equality raw words hist out
  · simpa [componentClock,afterComponent,family] using boolean_call .equality raw words hist out
  · simpa [componentClock,afterComponent,family] using boolean_call .equality raw words hist out
  · simpa [componentClock,afterComponent,family] using boolean_call .equality raw words hist out
/-- Actual component execution bounds its physical return store; no native
report or returned-size predicate supplies this cleanup budget. -/
theorem component_mass (code:Fin 18) (raw:Fin 6→List Bool) (words:List (List Bool)) (hist out:List Bool)
    (t:Nat) (ht:t≤ componentClock code raw words hist out)
    (hr:Runs program t (.inl (.record (family code))) (cleanData raw (vectorBits words) hist out)
      (.inl (.clear 0)) (afterComponent code raw words hist out)) :
    mass (afterComponent code raw words hist out)≤
      1263*(mass (cleanData raw (vectorBits words) hist out)+componentClock code raw words hist out) :=by
  let before:C.State Stack Label:=⟨some (.inl (.record (family code))),none,none,cleanData raw (vectorBits words) hist out,[]⟩
  obtain ⟨finish,hf,_,hd,_⟩:=hr [] before ⟨rfl,rfl,rfl⟩
  have hi (k:Stack) : (before.data k).length≤ mass (cleanData raw (vectorBits words) hist out):=
    word_le_mass _ k
  have hh:=SemiprimeD1StackReturnLink.run_data_bound program t
    (mass (cleanData raw (vectorBits words) hist out)) before finish hi hf
  rw [hd] at hh
  unfold mass
  calc
    _≤∑_k:Stack,(mass (cleanData raw (vectorBits words) hist out)+t):=Finset.sum_le_sum (fun k _=>hh k)
    _=1263*(mass (cleanData raw (vectorBits words) hist out)+t):=by
      simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
    _≤_:=Nat.mul_le_mul_left 1263 (Nat.add_le_add_left ht _)
/-- Physical completion from one acquired descriptor and acquired scope. The
ONLY actual data inputs are original fields, bank and caller accumulators. -/
theorem source_run (code:Fin 18) (raw:Fin 6→List Bool)
    (htag:raw 1=List.replicate code.val true)
    (h2:raw 2=SemiprimeD1StackUnaryDivmod.unary (raw 2).length)
    (h3:raw 3=SemiprimeD1StackUnaryDivmod.unary (raw 3).length)
    (h4:raw 4=SemiprimeD1StackUnaryDivmod.unary (raw 4).length)
    (htr:(code.val=1∨code.val=2∨code.val=3)→(raw 2).length<3)
    (hc:SemiprimeSourceCompactBits.Compact (raw 0)) (hN:0<SemiprimeBitArithmetic.bitValue (raw 0))
    (words:List (List Bool)) (hist out:List Bool) :
    ∃t≤ timeBound code raw words hist out,C.run program t
      (initial raw (vectorBits words) hist out)=some (done code raw words hist out) :=by
  have h0:=dispatch_run raw (vectorBits words) hist out code htag
  rw [dispatch_family] at h0
  obtain ⟨b,hb,h1⟩:=component_run code raw htag h2 h3 h4 htr hc hN words hist out
  have hm:=component_mass code raw words hist out b hb h1
  obtain ⟨c,hc,h2⟩:=cleanup_run (afterComponent code raw words hist out)
  have he:Sum.elim (fun part=>afterComponent code raw words hist out (.inl part)) (fun _=>[])=
      (done code raw words hist out).data :=by
    funext k
    cases k with
    | inl part=>exact afterComponent_common code raw words hist out part
    | inr k=>rfl
  rw [he] at h2
  have hh:=compose (compose h0 h1) h2
  obtain ⟨finish,hr,hpc,hd,hframes⟩:=hh [] (initial raw (vectorBits words) hist out) ⟨rfl,rfl,rfl⟩
  refine ⟨((6*code.val+5)+b)+c+1,?_,?_⟩
  · unfold timeBound
    nlinarith
  · rw [SemiprimeD1StackReturnLink.run_add,hr,Option.bind_some]
    change SemiprimeD1StackCalls.step program finish=some (done code raw words hist out)
    simp [SemiprimeD1StackCalls.step,hpc,program,SemiprimeD1StackCalls.execute,hd,hframes,done]
/-- Same complete actual source trace on the genuine1263-role finite machine,
including all fixed alias shadows and the real nested return alphabet. -/
noncomputable def recordInTime (code:Fin 18) (raw:Fin 6→List Bool)
    (htag:raw 1=List.replicate code.val true)
    (h2:raw 2=SemiprimeD1StackUnaryDivmod.unary (raw 2).length)
    (h3:raw 3=SemiprimeD1StackUnaryDivmod.unary (raw 3).length)
    (h4:raw 4=SemiprimeD1StackUnaryDivmod.unary (raw 4).length)
    (htr:(code.val=1∨code.val=2∨code.val=3)→(raw 2).length<3)
    (hc:SemiprimeSourceCompactBits.Compact (raw 0)) (hN:0<SemiprimeBitArithmetic.bitValue (raw 0))
    (words:List (List Bool)) (hist out:List Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial raw (vectorBits words) hist out))
      (some (SemiprimeD1StackCalls.configuration (done code raw words hist out))) (timeBound code raw words hist out) :=by
  apply SemiprimeD1StackCalls.evalsCorrect (source 0) output (.inl .start) program
  let h:=source_run code raw htag h2 h3 h4 htr hc hN words hist out
  let t:=Classical.choose h
  have ht:=Classical.choose_spec h
  exact ⟨⟨t,ht.2⟩,ht.1⟩
end RiemannGaussian.SemiprimeD1StackAllDescriptorRecordExecution
