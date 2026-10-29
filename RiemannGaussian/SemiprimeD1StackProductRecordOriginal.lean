/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackProductRecordBounds
import RiemannGaussian.SemiprimeD1ProductTableOriginal
import RiemannGaussian.SemiprimeD1StackProductTableOriginal
import RiemannGaussian.SemiprimeD1StackVertexRecordStreamExecution
/-! # Exact original product record bytes in the original scope order
The acquired scope is a caller cache: routing is not computed by this join.
Every numeric ID is converted to the frozen unary port field, and the table is
the exact old product reference in its unchanged local port order.
-/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1StackProductRecordOriginal
open SemiprimeD1StackProductRecord SemiprimeD1StackProductRecordExecution
namespace Bank
export SemiprimeD1OrdinalBankSpec (idAt id_value id_length)
end Bank
namespace Log
export SemiprimeD1StackVertexRecordStreamExecution (rows history)
end Log
namespace Entry
export SemiprimeD1ProductTableOriginal
  (literal_entry_coefficient literal_original_coefficient literal_entry_reduce)
end Entry
/-- The original public product indices, with no runtime selector advice. -/
def endpoint (N : Nat)
    (index : Fin (SemiprimeMacroParameters.firstAxis (SemiprimeMacroParameters.bitLength N)*
      SemiprimeMacroParameters.secondAxis (SemiprimeMacroParameters.bitLength N))) :
    SemiprimePublicAcquiredExecution.PublicVertex N := .inl (.product index)
/-- Changing only a table's type index leaves every original tape byte unchanged. -/
theorem tape_cast {m n : Nat} (h : m=n) (t : SemiprimeD1TensorTables.Table m) :
    SemiprimeD1TensorTapeCodec.tape (cast (congrArg SemiprimeD1TensorTables.Table h) t)=
      SemiprimeD1TensorTapeCodec.tape t := by
  cases h;rfl
/-- Proof-side vertex with the caller's exact ordered global occurrence scope and
the original complete product table; this constructor is never executed. -/
def vertex (N : Nat) (hN : 0<N)
    (index : Fin (SemiprimeMacroParameters.firstAxis (SemiprimeMacroParameters.bitLength N)*
      SemiprimeMacroParameters.secondAxis (SemiprimeMacroParameters.bitLength N))) (ports : List Nat)
    (hlen : ports.length=SemiprimeMacroGraph.subdividedArity (endpoint N index)) :
    SemiprimeD1LeafCounter.Vertex :=
  ⟨ports,cast (congrArg SemiprimeD1TensorTables.Table hlen.symm)
    (SemiprimeD1BooleanRootTablesOriginal.reference N hN (endpoint N index))⟩
/-- The actual N-only table equals the exact old reference at EVERY product index. -/
theorem table_original (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<SemiprimeBitArithmetic.bitValue bits) (index : Fin (SemiprimeMacroParameters.firstAxis (SemiprimeMacroParameters.bitLength (SemiprimeBitArithmetic.bitValue bits))*
      SemiprimeMacroParameters.secondAxis (SemiprimeMacroParameters.bitLength (SemiprimeBitArithmetic.bitValue bits)))) :
    table bits=SemiprimeD1TensorTapeCodec.tape
      (SemiprimeD1BooleanRootTablesOriginal.reference (SemiprimeBitArithmetic.bitValue bits) hN
        (endpoint (SemiprimeBitArithmetic.bitValue bits) index)) := by
  exact SemiprimeD1ProductTableOriginal.output_original bits hc hN index
/-- Exact row bytes bind numeric IDs to unary global ports without a permutation. -/
theorem row_original (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<SemiprimeBitArithmetic.bitValue bits) (index : Fin (SemiprimeMacroParameters.firstAxis (SemiprimeMacroParameters.bitLength (SemiprimeBitArithmetic.bitValue bits))*
      SemiprimeMacroParameters.secondAxis (SemiprimeMacroParameters.bitLength (SemiprimeBitArithmetic.bitValue bits)))) (M : Nat) (ports : List Nat)
    (hp : ∀i∈ports,i<M)
    (hlen : ports.length=SemiprimeMacroGraph.subdividedArity
      (endpoint (SemiprimeBitArithmetic.bitValue bits) index)) :
    R.row (S.result (ports.map (Bank.idAt M))) (table bits)=
      R.row (SemiprimeD1StackVertexReadExecution.portTape
        (vertex (SemiprimeBitArithmetic.bitValue bits) hN index ports hlen).ports)
        (SemiprimeD1TensorTapeCodec.tape
          (vertex (SemiprimeBitArithmetic.bitValue bits) hN index ports hlen).table) := by
  rw [SemiprimeD1StackPortOrdinalStreamOriginal.selected_portTape M ports hp,table_original bits hc hN index]
  exact congrArg (R.row (SemiprimeD1StackVertexReadExecution.portTape ports))
    (tape_cast hlen.symm (SemiprimeD1BooleanRootTablesOriginal.reference
      (SemiprimeBitArithmetic.bitValue bits) hN (endpoint (SemiprimeBitArithmetic.bitValue bits) index))).symm
/-- Literal acquired row prepends exactly the frozen original product-reader record. -/
theorem record_bytes_original (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<SemiprimeBitArithmetic.bitValue bits) (index : Fin (SemiprimeMacroParameters.firstAxis (SemiprimeMacroParameters.bitLength (SemiprimeBitArithmetic.bitValue bits))*
      SemiprimeMacroParameters.secondAxis (SemiprimeMacroParameters.bitLength (SemiprimeBitArithmetic.bitValue bits)))) (M : Nat) (ports : List Nat)
    (hp : ∀i∈ports,i<M)
    (hlen : ports.length=SemiprimeMacroGraph.subdividedArity
      (endpoint (SemiprimeBitArithmetic.bitValue bits) index))
    (rest : List SemiprimeD1LeafCounter.Vertex) :
    R.row (S.result (ports.map (Bank.idAt M))) (table bits)++
      SemiprimeD1StackVertexProduct.records rest=
      SemiprimeD1StackVertexProduct.records
        (vertex (SemiprimeBitArithmetic.bitValue bits) hN index ports hlen::rest) := by
  rw [row_original bits hc hN index M ports hp hlen]
  exact SemiprimeD1StackVertexRecordStream.row_records _ rest
/-- The actual halt keeps every previous row in its original forward order. -/
theorem history_original (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<SemiprimeBitArithmetic.bitValue bits) (index : Fin (SemiprimeMacroParameters.firstAxis (SemiprimeMacroParameters.bitLength (SemiprimeBitArithmetic.bitValue bits))*
      SemiprimeMacroParameters.secondAxis (SemiprimeMacroParameters.bitLength (SemiprimeBitArithmetic.bitValue bits)))) (M : Nat) (ports : List Nat)
    (hp : ∀i∈ports,i<M)
    (hlen : ports.length=SemiprimeMacroGraph.subdividedArity
      (endpoint (SemiprimeBitArithmetic.bitValue bits) index))
    (previous : List SemiprimeD1LeafCounter.Vertex) (old out : List Bool) :
    (done bits (ports.map (Bank.idAt M)) (Log.history previous old) out).data history=
      Log.history (previous++[vertex (SemiprimeBitArithmetic.bitValue bits) hN index ports hlen]) old := by
  change (R.row (S.result (ports.map (Bank.idAt M))) (table bits)).reverse++Log.history previous old=_
  rw [row_original bits hc hN index M ports hp hlen]
  simp only [Log.history,SemiprimeD1StackVertexRecordStreamExecution.rows_append,Log.rows,
    List.append_nil,List.reverse_append,List.append_assoc]
/-- One later physical logger reversal gives the exact frozen record list, including
its one final false tag and retained caller suffix. No host reversal supplies output. -/
theorem reverse_original (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<SemiprimeBitArithmetic.bitValue bits) (index : Fin (SemiprimeMacroParameters.firstAxis (SemiprimeMacroParameters.bitLength (SemiprimeBitArithmetic.bitValue bits))*
      SemiprimeMacroParameters.secondAxis (SemiprimeMacroParameters.bitLength (SemiprimeBitArithmetic.bitValue bits)))) (M : Nat) (ports : List Nat)
    (hp : ∀i∈ports,i<M)
    (hlen : ports.length=SemiprimeMacroGraph.subdividedArity
      (endpoint (SemiprimeBitArithmetic.bitValue bits) index))
    (previous : List SemiprimeD1LeafCounter.Vertex) (out : List Bool) :
    SemiprimeD1StackBytecode.run R.code
      (2*(Log.rows (previous++[vertex (SemiprimeBitArithmetic.bitValue bits) hN index ports hlen])).length+2)
      ⟨some .reverse,none,R.data [] []
        ((done bits (ports.map (Bank.idAt M)) (Log.history previous []) (false::out)).data history) (false::out)⟩=
      some ⟨none,none,R.data [] [] []
        (SemiprimeD1StackVertexProduct.records
          (previous++[vertex (SemiprimeBitArithmetic.bitValue bits) hN index ports hlen])++out)⟩ := by
  rw [history_original bits hc hN index M ports hp hlen]
  exact SemiprimeD1StackVertexRecordStreamExecution.reverse_original _ out
/-- Actual whole join clock for the padded acquired scope bank. Original N remains
binary; the only value-to-unary cost is bounded occurrence metadata. -/
theorem selected_timeBound (bits : List Bool) (M : Nat) (ports : List Nat) (hp : ∀i∈ports,i<M) :
    timeBound bits (ports.map (Bank.idAt M))≤SemiprimeD1StackProductTableBounds.runBound bits+
      21*2^(SemiprimeD1StackProductTableSpec.arity bits)+
      110*(ports.length+1)*(M+1)+20 := by
  have h:=SemiprimeD1StackProductRecordBounds.timeBound_le bits (ports.map (Bank.idAt M)) M
    (by intro w hw;obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hw;exact (Bank.id_length M i (hp i hi)).le)
    (by intro w hw;obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hw;rw [Bank.id_value M i (hp i hi)];exact (hp i hi).le)
  simpa only [List.length_map] using h
/-- Quantitative original-bitwidth envelope for this SAME actual three-call
source, including real table output, ID conversion and record framing. -/
theorem sqrt_timeBound (bits : List Bool) (hb : bits≠[]) (hc : SemiprimeSourceCompactBits.Compact bits)
    (words : List (List Bool)) (M : Nat)
    (hl : ∀w∈words,w.length≤M) (hv : ∀w∈words,SemiprimeBitArithmetic.bitValue w≤M) :
    timeBound bits words≤1000000000000000000000000000021*
      (SemiprimeMacroParameters.bitLength (SemiprimeBitArithmetic.bitValue bits)+1)^3*
      2^(48*(Nat.sqrt (SemiprimeMacroParameters.bitLength (SemiprimeBitArithmetic.bitValue bits))+1))+
      110*(words.length+1)*(M+1)+20 := by
  have ht:=SemiprimeD1StackProductRecordBounds.timeBound_le bits words M hl hv
  have hz:=SemiprimeD1StackProductTableOriginal.runBound_le_sqrt bits hb
  have ha:=SemiprimeD1StackProductTableOriginal.arity_sqrt_le bits hb
  have he:=Nat.pow_le_pow_right (by decide : 1≤(2:Nat)) ha
  have hi:1≤(bits.length+1)^3 := by
    have h:0<(bits.length+1)^3:=Nat.pow_pos (by omega)
    omega
  have hp:2^(SemiprimeD1StackProductTableSpec.arity bits)≤
      (bits.length+1)^3*2^(48*(Nat.sqrt bits.length+1)) := he.trans (by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (2^(48*(Nat.sqrt bits.length+1))) hi)
  have hs:=Nat.mul_le_mul_left 21 hp
  unfold SemiprimeD1StackProductTableOriginal.sqrtBound at hz
  have hg:timeBound bits words≤1000000000000000000000000000021*(bits.length+1)^3*
      2^(48*(Nat.sqrt bits.length+1))+110*(words.length+1)*(M+1)+20 := by nlinarith
  simpa only [SemiprimeD1BinaryDigitAcquisitionBounds.canonical_width bits hc] using hg
/-- The padded acquired scope discharges both metadata premises of the actual
bitwidth bound; original N and all tensor coefficients remain binary. -/
theorem selected_sqrt_timeBound (bits : List Bool) (hb : bits≠[])
    (hc : SemiprimeSourceCompactBits.Compact bits) (M : Nat) (ports : List Nat) (hp : ∀i∈ports,i<M) :
    timeBound bits (ports.map (Bank.idAt M))≤1000000000000000000000000000021*
      (SemiprimeMacroParameters.bitLength (SemiprimeBitArithmetic.bitValue bits)+1)^3*
      2^(48*(Nat.sqrt (SemiprimeMacroParameters.bitLength (SemiprimeBitArithmetic.bitValue bits))+1))+
      110*(ports.length+1)*(M+1)+20 := by
  have h:=sqrt_timeBound bits hb hc (ports.map (Bank.idAt M)) M
    (by intro w hw;obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hw;exact (Bank.id_length M i (hp i hi)).le)
    (by intro w hw;obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hw;rw [Bank.id_value M i (hp i hi)];exact (hp i hi).le)
  simpa only [List.length_map] using h
/-- Genuine complete original-N and acquired-scope finite machine at the closed
own bit-time envelope. Scope routing and bank acquisition remain caller work. -/
noncomputable def machineOriginal (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<SemiprimeBitArithmetic.bitValue bits) (M : Nat) (ports : List Nat)
    (hp : ∀i∈ports,i<M) (hist out : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration
        (initial bits (SemiprimeD1TensorTapeCodec.vectorBits (ports.map (Bank.idAt M))) hist out))
      (some (SemiprimeD1StackCalls.configuration (done bits (ports.map (Bank.idAt M)) hist out)))
      (1000000000000000000000000000021*
        (SemiprimeMacroParameters.bitLength (SemiprimeBitArithmetic.bitValue bits)+1)^3*
        2^(48*(Nat.sqrt (SemiprimeMacroParameters.bitLength (SemiprimeBitArithmetic.bitValue bits))+1))+
        110*(ports.length+1)*(M+1)+20) := by
  have hb:bits≠[] := by intro h;rw [h] at hN;exact Nat.lt_irrefl 0 hN
  let h:=productRecordInTime bits hb (ports.map (Bank.idAt M)) hist out
  exact ⟨h.toEvalsTo,h.steps_le_m.trans (selected_sqrt_timeBound bits hb hc M ports hp)⟩
/-- Source execution and original forward-row semantics hold together, with only
original N, the acquired binary-ID vector and actual caller accumulators as data. -/
theorem source_run_original (bits : List Bool) (hb : bits≠[]) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<SemiprimeBitArithmetic.bitValue bits) (index : Fin (SemiprimeMacroParameters.firstAxis (SemiprimeMacroParameters.bitLength (SemiprimeBitArithmetic.bitValue bits))*
      SemiprimeMacroParameters.secondAxis (SemiprimeMacroParameters.bitLength (SemiprimeBitArithmetic.bitValue bits)))) (M : Nat) (ports : List Nat)
    (hp : ∀i∈ports,i<M)
    (hlen : ports.length=SemiprimeMacroGraph.subdividedArity
      (endpoint (SemiprimeBitArithmetic.bitValue bits) index))
    (previous : List SemiprimeD1LeafCounter.Vertex) (old out : List Bool) :
    ∃t≤timeBound bits (ports.map (Bank.idAt M)),∃finish,
      C.run program t (initial bits (SemiprimeD1TensorTapeCodec.vectorBits (ports.map (Bank.idAt M)))
        (Log.history previous old) out)=some finish ∧
      finish=done bits (ports.map (Bank.idAt M)) (Log.history previous old) out ∧
      finish.data history=Log.history
        (previous++[vertex (SemiprimeBitArithmetic.bitValue bits) hN index ports hlen]) old := by
  obtain ⟨t,ht,hr⟩:=source_run bits hb (ports.map (Bank.idAt M)) (Log.history previous old) out
  exact ⟨t,ht,_,hr,rfl,history_original bits hc hN index M ports hp hlen previous old out⟩
end RiemannGaussian.SemiprimeD1StackProductRecordOriginal
