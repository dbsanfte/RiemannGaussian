/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackVertexProductSetup
/-! # Real record-field parsing and literal gather/tree calls inside the product -/
set_option autoImplicit false
set_option synthInstance.maxSize 65536
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
namespace RiemannGaussian.SemiprimeD1StackVertexProductRead
open SemiprimeD1StackVertexProduct SemiprimeD1StackVertexProductState
open SemiprimeD1StackVertexProductProjection
open SemiprimeD1StackProcedureTrace (Runs one_base runs_trans)
open SemiprimeD1TensorTapeCodec (vectorBits tape)

/-- Actual record-field destination, fixed by the literal caller site. -/
def fieldTarget (table : Bool) : Slot := if table then .table else .ports
/-- The literal field output shares precisely its named physical live register. -/
theorem field_output_address (table : Bool) : fieldStack table (.inl .output)=address (fieldTarget table) := by
  cases table <;> rfl

/-- Actual arbitrary-length field read, including validity acquisition and all copying. -/
theorem field_call (v : Values) (table : Bool) (word tail : List Bool) (pc next : Label)
    (hcode : program pc=.call (.field table (F.active .tagPop (none,false))) next)
    (hr : v .reader=SemiprimeSourceHistogramKeyBits.frame word tail)
    (ho : v (fieldTarget table)=[]) (hv : v .valid=[]) :
    Runs program (8*word.length+7) pc (data v) next
      (data (Function.update (Function.update (Function.update v .reader tail) (fieldTarget table) word) .valid [true])) := by
  apply SemiprimeD1StackProcedureTrace.included_call program (fieldStack table) (Label.field table)
    (fieldStack_injective table) F.code (F.active .tagPop (none,false)) (fun _=>rfl) pc next hcode (8*word.length+6)
    (SemiprimeD1TensorTapeFieldBytecode.initial (SemiprimeSourceHistogramKeyBits.frame word tail) [])
    (⟨none,none,Sum.elim (SemiprimeD1TensorTapeFieldMachine.contents tail [] word) (fun _=>[true])⟩:
      SemiprimeD1StackBytecode.State F.Stack F.Label)
  · rfl
  · rfl
  · exact SemiprimeD1TensorTapeFieldBytecode.framed_run word tail []
  · constructor
    · intro k
      rw [field_project]
      cases table <;> fin_cases k <;>
        simp [SemiprimeD1TensorTapeFieldBytecode.initial,SemiprimeD1TensorTapeFieldMachine.contents,
          fieldTarget,hr,hv] at ho ⊢ <;> assumption
    · intro k hk
      rfl
  · constructor
    · intro k
      rw [field_project]
      cases table <;> fin_cases k <;>
        simp [SemiprimeD1TensorTapeFieldMachine.contents,fieldTarget]
    · intro k hk
      have hir : k ≠ address .reader := fun he=>hk (.inl .input) he.symm
      have hio : k ≠ address (fieldTarget table) := fun he=>hk (.inl .output) ((field_output_address table).trans he.symm)
      have hiv : k ≠ address .valid := fun he=>hk (.inr ()) he.symm
      rw [data_update,data_update,data_update]
      simp only [Function.update_of_ne hiv,Function.update_of_ne hio,Function.update_of_ne hir]

/-- Validity bits are physically consumed; they are not assumed branch answers. -/
theorem field_flag (v : Values) (pc next : Label)
    (hcode : program pc=.base (.pop (address .valid) .abort .abort next)) :
    Runs program 1 pc (data (Function.update v .valid [true])) next (data (Function.update v .valid [])) := by
  apply one_base program pc next (.pop (address .valid) .abort .abort next) _ _ hcode
  · simp only [SemiprimeD1StackBytecode.execute,data_get,Function.update_self,List.head?_cons,
      SemiprimeD1StackBytecode.choose]
  · change Function.update (data (Function.update v .valid [true])) (address .valid)
      ((data (Function.update v .valid [true]) (address .valid)).tail)=_
    rw [data_get,Function.update_self,List.tail_cons,←data_update,Function.update_idem]

/-- Closed original vertex call: real gathered port bits feed the actual table
reader and its encoded result directly fills the multiplier's physical operand. -/
theorem vertex_call (v : Values) (vertex : SemiprimeD1LeafCounter.Vertex)
    (hp : v .ports=SemiprimeD1StackVertexReadExecution.portTape vertex.ports)
    (ht : v .table=tape vertex.table) (hl : v .left=[]) :
    ∃ m ≤ SemiprimeD1StackVertexReadExecution.budget (v .assignment).length
        (SemiprimeD1StackVertexReadExecution.portTape vertex.ports).length (tape vertex.table).length+1,
      Runs program m .callVertex (data v) .callMul
        (data (Function.update (Function.update (Function.update v .ports []) .table []) .left
          (vectorBits (SemiprimeD1TensorTapeLeaf.evaluateVertex vertex (v .assignment)).words))) := by
  obtain ⟨m,hm,hsource⟩:=SemiprimeD1StackVertexReadExecution.vertex_run vertex (v .assignment) [] []
  refine ⟨m+1,by omega,?_⟩
  apply SemiprimeD1StackProcedureInclusion.included_call program vertexStack Label.vertex vertexStack_injective
    V.code (V.control .start) (fun _=>rfl) .callVertex .callMul rfl m
    (⟨some (V.control .start),none,none,SemiprimeD1StackVertexReadExecution.input vertex (v .assignment) [] [],[]⟩:
      SemiprimeD1StackCalls.State V.Stack V.Label)
    (⟨none,none,none,SemiprimeD1StackVertexReadExecution.output vertex (v .assignment) [] [],[]⟩:
      SemiprimeD1StackCalls.State V.Stack V.Label)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact hsource
  · constructor
    · intro k
      rw [vertex_project]
      cases k <;> simp [SemiprimeD1StackVertexReadExecution.input,SemiprimeD1StackVertexRead.data,hp,ht,hl]
    · intro k hk
      rfl
  · constructor
    · intro k
      rw [vertex_project]
      cases k <;> simp [SemiprimeD1StackVertexReadExecution.output,SemiprimeD1StackVertexRead.data]
    · intro k hk
      have hnp : k ≠ address .ports := fun he=>hk .ports he.symm
      have hnt : k ≠ address .table := fun he=>hk .tableTape he.symm
      have hnl : k ≠ address .left := fun he=>hk .output he.symm
      rw [data_update,data_update,data_update]
      simp only [Function.update_of_ne hnl,Function.update_of_ne hnt,Function.update_of_ne hnp]

end RiemannGaussian.SemiprimeD1StackVertexProductRead
