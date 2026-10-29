/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortOrdinalStreamBounds
import RiemannGaussian.SemiprimeD1OrdinalBankSpec
import RiemannGaussian.SemiprimeD1StackVertexReadExecution
/-! # Exact original port-tape binding for acquired padded occurrence IDs -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1StackPortOrdinalStreamOriginal
open SemiprimeD1StackPortOrdinalStream SemiprimeD1StackPortOrdinalStreamExecution
namespace Bank
export SemiprimeD1OrdinalBankSpec (words idAt id_value id_length values word_length length)
end Bank
/-- Literal output equals the frozen unary Gather input, with raw padding allowed. -/
theorem result_portTape (words:List (List Bool)) :
    result words=SemiprimeD1StackVertexReadExecution.portTape
      (words.map SemiprimeBitArithmetic.bitValue) := by
  simp only [result,SemiprimeD1StackVertexReadExecution.portTape,List.map_map]
  rfl
/-- Every actual selected canonical occurrence ID serializes to its exact port.
The ordinal list appears only in this proof, never in runtime inputs/control. -/
theorem selected_portTape (M:Nat) (ports:List Nat) (hp:∀i∈ports,i<M) :
    result (ports.map (Bank.idAt M))=SemiprimeD1StackVertexReadExecution.portTape ports := by
  rw [result_portTape]
  congr 1
  rw [List.map_map]
  have h : ports.map (fun i=>SemiprimeBitArithmetic.bitValue (Bank.idAt M i))=ports.map id := by
    apply List.map_congr_left
    intro i hi
    exact Bank.id_value M i (hp i hi)
  change ports.map (fun i=>SemiprimeBitArithmetic.bitValue (Bank.idAt M i))=ports
  simpa only [List.map_id] using h
/-- Whole acquired bank covers ALL canonical occurrence ordinals, including
unused scope entries. No wire-major endpoint permutation is asserted. -/
theorem whole_portTape (M:Nat) :
    result (Bank.words M)=SemiprimeD1StackVertexReadExecution.portTape (List.range M) := by
  rw [result_portTape,Bank.values]
/-- Closed actual selected-fibre execution with no unary tape/decoded answer input. -/
theorem selected_source_run (M:Nat) (ports:List Nat) (hp:∀i∈ports,i<M) :
    ∃t≤100*(ports.length+1)*(M+1),SemiprimeD1StackCalls.run program t
      (initial (SemiprimeD1TensorTapeCodec.vectorBits (ports.map (Bank.idAt M))))=
      some (done (ports.map (Bank.idAt M))) := by
  obtain ⟨t,ht,he⟩:=source_run (ports.map (Bank.idAt M))
  refine ⟨t,ht.trans ?_,he⟩
  have h:=SemiprimeD1StackPortOrdinalStreamBounds.timeBound_le (ports.map (Bank.idAt M)) M
    (by intro w hw;obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hw;exact (Bank.id_length M i (hp i hi)).le)
    (by intro w hw;obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hw;rw [Bank.id_value M i (hp i hi)];exact (hp i hi).le)
  simpa only [List.length_map] using h
/-- The N-only acquired root bank's serialization has actual quadratic cost in
its tally M; M is metadata occurrence count, never the original N value. -/
theorem whole_source_run (M:Nat) :
    ∃t≤100*(M+1)^2,SemiprimeD1StackCalls.run program t
      (initial (SemiprimeD1TensorTapeCodec.vectorBits (Bank.words M)))=some (done (Bank.words M)) := by
  obtain ⟨t,ht,he⟩:=source_run (Bank.words M)
  refine ⟨t,ht.trans ?_,he⟩
  have h:=SemiprimeD1StackPortOrdinalStreamBounds.timeBound_le (Bank.words M) M
    (fun w hw=>(Bank.word_length M w hw).le)
    (by intro w hw
        have hm:SemiprimeBitArithmetic.bitValue w∈(Bank.words M).map SemiprimeBitArithmetic.bitValue:=
          List.mem_map.mpr ⟨w,hw,rfl⟩
        rw [Bank.values] at hm
        exact (List.mem_range.mp hm).le)
  simpa only [Bank.length,pow_two,Nat.mul_assoc] using h
end RiemannGaussian.SemiprimeD1StackPortOrdinalStreamOriginal
