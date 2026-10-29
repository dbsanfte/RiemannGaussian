/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackVertexRecordStream

/-! # Literal calls, forward-order invariant and complete physical prefix cells -/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackVertexRecordStreamExecution
open SemiprimeD1StackVertexRecordStream
open SemiprimeD1StackProcedureTrace
namespace Link
export SemiprimeD1StackMultiplierLink (instruction DataRel)
end Link
/-- Forward rows without the single final list tag; proof notation only. -/
def rows : List SemiprimeD1LeafCounter.Vertex → List Bool
  | [] => []
  | v::vs => row (SemiprimeD1StackVertexReadExecution.portTape v.ports)
      (SemiprimeD1TensorTapeCodec.tape v.table) ++ rows vs
/-- The physically seeded output terminator recovers the exact frozen stream. -/
theorem rows_records (vs : List SemiprimeD1LeafCounter.Vertex) :
    rows vs ++ [false] = SemiprimeD1StackVertexProduct.records vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    rw [rows,List.append_assoc,ih,row_records]
/-- New acquired rows append in original forward order. -/
theorem rows_append (xs ys : List SemiprimeD1LeafCounter.Vertex) : rows (xs++ys)=rows xs++rows ys := by
  induction xs with
  | nil => rfl
  | cons v vs ih => simp only [List.cons_append,rows,ih,List.append_assoc]
/-- Physical state invariant after each forward acquisition/log call. -/
def history (vs : List SemiprimeD1LeafCounter.Vertex) (old : List Bool) : List Bool :=
  (rows vs).reverse ++ old
/-- Each paid source run advances the whole forward-order history invariant. -/
theorem record_forward (previous : List SemiprimeD1LeafCounter.Vertex)
    (v : SemiprimeD1LeafCounter.Vertex) (old out : List Bool) (flag : Option Bool) :
    B.run code (recordTime (SemiprimeD1StackVertexReadExecution.portTape v.ports)
      (SemiprimeD1TensorTapeCodec.tape v.table))
      ⟨some .record,flag,data (SemiprimeD1StackVertexReadExecution.portTape v.ports)
        (SemiprimeD1TensorTapeCodec.tape v.table) (history previous old) out⟩ =
      some ⟨none,none,data [] [] (history (previous++[v]) old) out⟩ := by
  rw [record_run]
  simp only [history,rows_append,rows,List.append_nil,List.reverse_append,List.append_assoc]
/-- One final reversal yields the exact original vertex list and retained outer suffix. -/
theorem reverse_original (vs : List SemiprimeD1LeafCounter.Vertex) (out : List Bool) :
    B.run code (2*(rows vs).length+2)
      ⟨some .reverse,none,data [] [] (history vs []) (false::out)⟩ =
      some ⟨none,none,data [] [] [] (SemiprimeD1StackVertexProduct.records vs++out)⟩ := by
  have h:=reverse_run (rows vs).reverse [] [] (false::out) none
  rw [←rows_records vs]
  simpa only [history,List.append_nil,List.length_reverse,List.reverse_reverse,
    List.append_assoc,List.singleton_append] using h

/-- One real caller instruction enters the same fixed logger; its halt becomes a
real return pop. All four roles and every outer return cell are preserved exactly. -/
theorem call {K G : Type} [DecidableEq K]
    (program : G → C.Instruction K G) (stack : Stack → K) (label : Label → G)
    (hinj : Function.Injective stack) (entry : Label)
    (hcode : ∀l,program (label l)=Link.instruction stack label (code l))
    (pc next : G) (hcall : program pc=.call (label entry) next)
    (time : Nat) (source result : Stack → List Bool) (outer target : K → List Bool)
    (hr : B.run code time ⟨some entry,none,source⟩=some ⟨none,none,result⟩)
    (hin : Link.DataRel stack outer source outer)
    (hout : Link.DataRel stack outer result target) :
    Runs program (time+1) pc outer next target := by
  exact included_call program stack label hinj code entry hcode pc next hcall time
    ⟨some entry,none,source⟩ ⟨none,none,result⟩ outer target rfl rfl hr hin hout

/-- Actual compiled caller, logger and return, then caller halt; no data getter. -/
def recordInTime (ports table hist out : List Bool) :
    StateTransition.EvalsToInTime (machine .record).step
      (SemiprimeD1StackCalls.configuration
        (SemiprimeD1StackReturnLink.initial (L:=Label) (data ports table hist out)))
      (some (SemiprimeD1StackCalls.configuration
        (SemiprimeD1StackReturnLink.final (L:=Label)
          (data [] [] ((row ports table).reverse++hist) out)))) (recordTime ports table+2) := by
  exact SemiprimeD1StackReturnLink.linkedInTime .record code Stack.ports Stack.output
    (recordTime ports table) _ _ (record_run ports table hist out none)
/-- Compiled initialization includes actual call, return and caller halt. -/
def initializeInTime (ports table hist out : List Bool) :
    StateTransition.EvalsToInTime (machine .initialize).step
      (SemiprimeD1StackCalls.configuration
        (SemiprimeD1StackReturnLink.initial (L:=Label) (data ports table hist out)))
      (some (SemiprimeD1StackCalls.configuration
        (SemiprimeD1StackReturnLink.final (L:=Label) (data ports table hist (false::out))))) 4 := by
  exact SemiprimeD1StackReturnLink.linkedInTime .initialize code Stack.ports Stack.output
    2 _ _ (initialize_run ports table hist out none)
/-- Compiled final reversal includes actual call, return and caller halt. -/
def reverseInTime (ports table hist out : List Bool) :
    StateTransition.EvalsToInTime (machine .reverse).step
      (SemiprimeD1StackCalls.configuration
        (SemiprimeD1StackReturnLink.initial (L:=Label) (data ports table hist out)))
      (some (SemiprimeD1StackCalls.configuration
        (SemiprimeD1StackReturnLink.final (L:=Label) (data ports table [] (hist.reverse++out)))))
      (2*hist.length+4) := by
  exact SemiprimeD1StackReturnLink.linkedInTime .reverse code Stack.ports Stack.output
    (2*hist.length+2) _ _ (reverse_run hist ports table out none)

/-- Every source prefix counts all four Boolean roles and actual finite-label
return cells. It applies independently of entry, flags, data values or input size. -/
theorem prefix_cells (entry : Label) (ports table hist out : List Bool) (fuel : Nat)
    (finish : SemiprimeD1StackCalls.State Stack (Label⊕Bool))
    (hr : SemiprimeD1StackCalls.run (SemiprimeD1StackReturnLink.code entry code) fuel
      (SemiprimeD1StackReturnLink.initial (L:=Label) (data ports table hist out))=some finish) :
    (finish.data .ports).length+(finish.data .table).length+
      (finish.data .history).length+(finish.data .output).length+finish.frames.length ≤
      5*(ports.length+table.length+hist.length+out.length+fuel) := by
  have h:=SemiprimeD1StackReturnLink.run_data_bound
    (SemiprimeD1StackReturnLink.code entry code) fuel
    (ports.length+table.length+hist.length+out.length) _ finish (by
      intro k;cases k <;> simp only [SemiprimeD1StackReturnLink.initial,data] <;> omega) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound _ fuel _ finish hr
  change finish.frames.length ≤ 0+fuel at hf
  have hp:=h .ports
  have ht:=h .table
  have hh:=h .history
  have ho:=h .output
  omega
/-- The actual compiled prefix has exactly the same complete payload, including
flags and return cells, at the same source transition count. -/
theorem compiled_prefix (entry : Label) (fuel : Nat)
    (start : SemiprimeD1StackCalls.State Stack (Label⊕Bool)) :
    (SemiprimeD1StackCalls.run (SemiprimeD1StackReturnLink.code entry code) fuel start).map
      SemiprimeD1StackCalls.configuration =
      (fun cfg=>cfg.bind (machine entry).step)^[fuel]
        (some (SemiprimeD1StackCalls.configuration start)) := by
  exact SemiprimeD1StackCalls.run_correct Stack.ports Stack.output (.inr false)
    (SemiprimeD1StackReturnLink.code entry code) fuel start
end RiemannGaussian.SemiprimeD1StackVertexRecordStreamExecution
