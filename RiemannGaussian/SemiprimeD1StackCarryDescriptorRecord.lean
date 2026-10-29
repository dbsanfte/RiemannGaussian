/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackDescriptorRecord
import RiemannGaussian.SemiprimeD1StackPublicCarryRecordOriginal
import RiemannGaussian.SemiprimeD1StackDescriptorRecordExecution
import RiemannGaussian.SemiprimeD1StackDescriptorRecordBounds
import RiemannGaussian.SemiprimeD1StackPublicCarryRecordClock
/-! # Concrete physical carry descriptor to the entire original carry row
This fixed137-role program loads ONLY actual binary N and original coord0
markers from the acquired six-field descriptor, through the real complete
template loader, then executes the entire concrete carry record source.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackCarryDescriptorRecord
namespace I
export SemiprimeD1StackPublicCarryTable (static inputTemplate)
end I
namespace D
export SemiprimeD1StackDescriptorRecord (source scratch recordStack templateStack original history output)
end D
/-- Frozen actual51-role input-checker bank. -/
abbrev Checker :=SemiprimeD1StackPublicCarry.Stack
/-- Exactly the original N input role, independent of original N. -/
def numberRole : Checker :=SemiprimeD1StackPublicCarry.inputRole
/-- Exactly the physical original carry-index marker role. -/
def indexRole : Checker :=SemiprimeD1StackPublicCarryTable.P.index
/-- Static map ONLY N→source0 and original coord1 index markers→source3. -/
def sourceMap (k : Checker) : Option (Fin 6) :=
  if k=numberRole then some 0 else if k=indexRole then some 2 else none
/-- Actual six physically acquired input words in their authoritative order. -/
def fields (bits tag indexWord coord1 coord2 coord3 : List Bool) : Fin 6→List Bool :=
  fun i=>if i=0 then bits else if i=1 then tag else if i=2 then indexWord
    else if i=3 then coord1 else if i=4 then coord2 else coord3
/-- Full concrete137-role inventory, including unused shared-component aliases. -/
abbrev Stack :=SemiprimeD1StackDescriptorRecord.Stack Checker
/-- All static loader, table, serializer, logger and return labels. -/
abbrev Label :=SemiprimeD1StackDescriptorRecord.Label SemiprimeD1StackPublicCarry.Label I.static.roles.length
/-- One literal physical program before ALL original N and descriptor values. -/
def program : Label→SemiprimeD1StackCalls.Instruction Stack Label :=
  SemiprimeD1StackDescriptorRecord.program I.static sourceMap
/-- Charged arbitrary old template, only acquired original fields/scope and caller accumulators. -/
def initial (oldTemplate : Checker→List Bool) (inputFields : Fin 6→List Bool) (bank hist out : List Bool) :
    SemiprimeD1StackCalls.State Stack Label :=
  SemiprimeD1StackDescriptorRecord.initial I.static oldTemplate inputFields bank hist out
/-- One genuine finite machine, independent of original N and descriptor fields. -/
def machine : Turing.FinTM2 :=SemiprimeD1StackDescriptorRecord.machine I.static sourceMap
/-- Every physical register, including all shadows, is counted. -/
theorem stack_card : Fintype.card Stack=137 := by
  rw [SemiprimeD1StackDescriptorRecord.stack_card,SemiprimeD1StackPublicCarry.stack_card]
/-- Actual selected source words equal the frozen input initialization EXACTLY;
no metadata, cached arithmetic, assignment, result or clock is initialized. -/
theorem selected_template (bits tag indexWord coord1 coord2 coord3 : List Bool) :
    SemiprimeD1StackDescriptorRecord.selected sourceMap (fields bits tag indexWord coord1 coord2 coord3)=
      I.inputTemplate bits indexWord := by
  funext k
  rw [SemiprimeD1StackPublicCarryTableTrace.template_only]
  change (if k=numberRole then some 0 else if k=indexRole then some 2 else none).elim []
    (fields bits tag indexWord coord1 coord2 coord3)=
      if k=numberRole then bits else if k=indexRole then indexWord else []
  by_cases hn:k=numberRole
  · subst k;rfl
  · by_cases hi:k=indexRole
    · subst k;rfl
    · simp only [hn,hi,ite_false];rfl

end RiemannGaussian.SemiprimeD1StackCarryDescriptorRecord

namespace RiemannGaussian.SemiprimeD1StackCarryDescriptorRecordExecution
open SemiprimeD1StackCarryDescriptorRecord
open SemiprimeD1TensorTapeCodec (vectorBits)
namespace T
export SemiprimeD1StackPublicCarryTableTrace (answer budget actual_trace)
end T
/-- Six physical source fields equal their literal coordinate projection;
this is proof-side extensionality, never an executed metadata supplier. -/
theorem fields_eta (inputFields : Fin 6→List Bool) :
    fields (inputFields 0) (inputFields 1) (inputFields 2) (inputFields 3) (inputFields 4) (inputFields 5)=inputFields := by
  funext i;fin_cases i <;> rfl
/-- Arbitrary actual acquired fields initialize EXACTLY the frozen original
input template: only binary N and the original coord0 carry-index markers. -/
theorem selected_fields (inputFields : Fin 6→List Bool) :
    SemiprimeD1StackDescriptorRecord.selected sourceMap inputFields=I.inputTemplate (inputFields 0) (inputFields 2) := by
  have h:=selected_template (inputFields 0) (inputFields 1) (inputFields 2) (inputFields 3) (inputFields 4) (inputFields 5)
  rw [fields_eta] at h
  exact h
/-- Whole137-role result after real load, compilation, scope conversion and logging. -/
def done (inputFields : Fin 6→List Bool) (words : List (List Bool)) (hist out : List Bool) :
    SemiprimeD1StackCalls.State Stack Label :=
  SemiprimeD1StackDescriptorRecord.done I.static sourceMap inputFields words
    (T.answer (inputFields 0) (inputFields 2)) hist out
/-- Complete actual source clock, including the arbitrary dirty template. -/
def timeBound (oldTemplate : Checker→List Bool) (inputFields : Fin 6→List Bool) (words : List (List Bool))
    (hist out : List Bool) : Nat :=
  SemiprimeD1StackDescriptorRecordExecution.timeBound I.static sourceMap oldTemplate inputFields words
    (T.answer (inputFields 0) (inputFields 2)) (T.budget (inputFields 0) (inputFields 2)) hist out
/-- The real51-role template loader's complete trace; all original descriptor
fields and every non-template component role are retained exactly. -/
theorem template_run (oldTemplate : Checker→List Bool) (inputFields : Fin 6→List Bool) (bank hist out : List Bool) :
    ∃t≤SemiprimeD1StackDescriptorRecordExecution.prepareBound I.static oldTemplate inputFields bank hist out,
      SemiprimeD1StackProcedureTrace.Runs program t (.inl .start) (initial oldTemplate inputFields bank hist out).data
        (.inl .record) (SemiprimeD1StackDescriptorRecord.data
          (SemiprimeD1StackPublicCarryRecord.initial (inputFields 0) (inputFields 2) bank hist out).data inputFields []) := by
  have h:=SemiprimeD1StackDescriptorRecordExecution.prepare_call I.static sourceMap oldTemplate inputFields bank hist out
  simpa only [SemiprimeD1StackDescriptorRecord.afterLoad,selected_fields,
    SemiprimeD1StackCarryDescriptorRecord.program,SemiprimeD1StackCarryDescriptorRecord.initial,
    SemiprimeD1StackPublicCarryRecord.initial] using h
/-- Fully concrete actual source: no checker/template/count/table/verdict
supplier premise remains. Scope and all six source words are already acquired. -/
theorem source_run (oldTemplate : Checker→List Bool) (inputFields : Fin 6→List Bool)
    (hb : inputFields 0≠[]) (words : List (List Bool)) (hist out : List Bool) :
    ∃t≤timeBound oldTemplate inputFields words hist out,SemiprimeD1StackCalls.run program t
      (initial oldTemplate inputFields (vectorBits words) hist out)=some (done inputFields words hist out) := by
  apply SemiprimeD1StackDescriptorRecordExecution.source_run I.static sourceMap oldTemplate inputFields
  · rw [selected_fields];rfl
  · rw [selected_fields]
    exact T.actual_trace (inputFields 0) (inputFields 2) hb
/-- Genuine finite-machine trace with the same full actual own source clock. -/
noncomputable def recordInTime (oldTemplate : Checker→List Bool) (inputFields : Fin 6→List Bool)
    (hb : inputFields 0≠[]) (words : List (List Bool)) (hist out : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial oldTemplate inputFields (vectorBits words) hist out))
      (some (SemiprimeD1StackCalls.configuration (done inputFields words hist out)))
      (timeBound oldTemplate inputFields words hist out) := by
  apply SemiprimeD1StackDescriptorRecordExecution.recordInTime I.static sourceMap oldTemplate inputFields
  · rw [selected_fields];rfl
  · rw [selected_fields]
    exact T.actual_trace (inputFields 0) (inputFields 2) hb
/-- Every actual component data cell agrees with the frozen concrete132-role
input-record result, after physical descriptor initialization rather than advice. -/
theorem component_done (inputFields : Fin 6→List Bool) (words : List (List Bool)) (hist out : List Bool)
    (k : SemiprimeD1StackPublicCarryRecord.Stack) :
    (done inputFields words hist out).data (D.recordStack k)=
      (SemiprimeD1StackPublicCarryRecordExecution.done (inputFields 0) (inputFields 2) words hist out).data k := by
  unfold done SemiprimeD1StackDescriptorRecord.done
  rw [selected_fields]
  rfl
/-- All six actual source words are retained byte for byte, including tag and unused coordinates. -/
theorem retained_source (inputFields : Fin 6→List Bool) (words : List (List Bool)) (hist out : List Bool) (i : Fin 6) :
    (done inputFields words hist out).data (D.source i)=inputFields i := rfl
/-- The actual loader scratch is physically empty at completion. -/
theorem scratch_clear (inputFields : Fin 6→List Bool) (words : List (List Bool)) (hist out : List Bool) :
    (done inputFields words hist out).data D.scratch=[] := rfl
end RiemannGaussian.SemiprimeD1StackCarryDescriptorRecordExecution

namespace RiemannGaussian.SemiprimeD1StackCarryDescriptorRecordBounds
open SemiprimeD1StackCarryDescriptorRecord SemiprimeD1StackCarryDescriptorRecordExecution
open SemiprimeD1TensorTapeCodec (vectorBits)
/-- All actual physical inputs, including every old template word and all six sources. -/
def inputSize (oldTemplate : Checker→List Bool) (inputFields : Fin 6→List Bool) (bank hist out : List Bool) : Nat :=
  SemiprimeD1StackDescriptorRecordBounds.inputSize I.static oldTemplate inputFields bank hist out
/-- Complete same-source clock: real template drain/load plus the entire
concrete input-checker table, physical ordinal conversion and consuming log. -/
def runBound (oldTemplate : Checker→List Bool) (inputFields : Fin 6→List Bool) (words : List (List Bool))
    (M : Nat) (hist out : List Bool) : Nat :=
  SemiprimeD1StackDescriptorRecordExecution.prepareBound I.static oldTemplate inputFields (vectorBits words) hist out+
    SemiprimeD1StackPublicCarryRecordClock.runBound (inputFields 0) (inputFields 2) words M+2
/-- Every charged old-template byte and every selected-source copy is paid. -/
theorem prepareBound_eq (oldTemplate : Checker→List Bool) (inputFields : Fin 6→List Bool) (bank hist out : List Bool) :
    SemiprimeD1StackDescriptorRecordExecution.prepareBound I.static oldTemplate inputFields bank hist out=
      51*(6*inputSize oldTemplate inputFields bank hist out+5)+2 := by
  unfold SemiprimeD1StackDescriptorRecordExecution.prepareBound SemiprimeD1StackDescriptorRecordLoad.loadUnit
  exact congrArg (fun n:Nat=>n*(6*inputSize oldTemplate inputFields bank hist out+5)+2)
    SemiprimeD1StackPublicCarryTable.roles_length
/-- Closed own bit clock; no native report or evaluator bound is substituted. -/
theorem timeBound_le (oldTemplate : Checker→List Bool) (inputFields : Fin 6→List Bool) (words : List (List Bool))
    (M : Nat) (hist out : List Bool) (hl : ∀w∈words,w.length≤M)
    (hv : ∀w∈words,SemiprimeBitArithmetic.bitValue w≤M) :
    timeBound oldTemplate inputFields words hist out≤runBound oldTemplate inputFields words M hist out := by
  have h:=SemiprimeD1StackPublicCarryRecordClock.timeBound_le (inputFields 0) (inputFields 2) words M hl hv
  unfold timeBound SemiprimeD1StackDescriptorRecordExecution.timeBound runBound
  rw [selected_fields]
  exact Nat.add_le_add_right (Nat.add_le_add_left h _) 2
/-- Complete actual concrete source, including descriptor initialization. -/
theorem source_run_bounded (oldTemplate : Checker→List Bool) (inputFields : Fin 6→List Bool)
    (hb : inputFields 0≠[]) (words : List (List Bool)) (M : Nat) (hist out : List Bool)
    (hl : ∀w∈words,w.length≤M) (hv : ∀w∈words,SemiprimeBitArithmetic.bitValue w≤M) :
    ∃t≤runBound oldTemplate inputFields words M hist out,SemiprimeD1StackCalls.run program t
      (initial oldTemplate inputFields (vectorBits words) hist out)=some (done inputFields words hist out) := by
  obtain ⟨t,ht,hr⟩:=source_run oldTemplate inputFields hb words hist out
  exact ⟨t,ht.trans (timeBound_le oldTemplate inputFields words M hist out hl hv),hr⟩
/-- All137 roles, six retained physical sources, every dormant shadow and every
real nested return-stack cell at every reached source prefix. -/
theorem prefix_cells (oldTemplate : Checker→List Bool) (inputFields : Fin 6→List Bool)
    (hb : inputFields 0≠[]) (words : List (List Bool)) (hist out : List Bool) (fuel : Nat)
    (finish : SemiprimeD1StackCalls.State Stack Label)
    (hr : SemiprimeD1StackCalls.run program fuel (initial oldTemplate inputFields (vectorBits words) hist out)=some finish) :
    (∑k:Stack,(finish.data k).length)+finish.frames.length≤
      138*(inputSize oldTemplate inputFields (vectorBits words) hist out+timeBound oldTemplate inputFields words hist out+1) := by
  have hraw:SemiprimeD1StackDescriptorRecord.selected sourceMap inputFields I.static.raw=[]:=by rw [selected_fields];rfl
  have hc:SemiprimeD1StackStaticTableSpec.CheckerTrace I.static
      (SemiprimeD1StackDescriptorRecord.selected sourceMap inputFields)
      (T.answer (inputFields 0) (inputFields 2)) (T.budget (inputFields 0) (inputFields 2)):=by
    rw [selected_fields];exact T.actual_trace (inputFields 0) (inputFields 2) hb
  have h:=SemiprimeD1StackDescriptorRecordBounds.prefix_cells I.static sourceMap oldTemplate inputFields hraw
    (T.answer (inputFields 0) (inputFields 2)) (T.budget (inputFields 0) (inputFields 2)) hc words hist out fuel finish hr
  rw [SemiprimeD1StackPublicCarry.stack_card] at h
  exact h
/-- Same full physical prefix certificate on the genuine finite machine itself. -/
theorem machine_prefix_cells (oldTemplate : Checker→List Bool) (inputFields : Fin 6→List Bool)
    (hb : inputFields 0≠[]) (words : List (List Bool)) (hist out : List Bool) (fuel : Nat) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial oldTemplate inputFields (vectorBits words) hist out)))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤
      138*(inputSize oldTemplate inputFields (vectorBits words) hist out+timeBound oldTemplate inputFields words hist out+1) := by
  have hraw:SemiprimeD1StackDescriptorRecord.selected sourceMap inputFields I.static.raw=[]:=by rw [selected_fields];rfl
  have hc:SemiprimeD1StackStaticTableSpec.CheckerTrace I.static
      (SemiprimeD1StackDescriptorRecord.selected sourceMap inputFields)
      (T.answer (inputFields 0) (inputFields 2)) (T.budget (inputFields 0) (inputFields 2)):=by
    rw [selected_fields];exact T.actual_trace (inputFields 0) (inputFields 2) hb
  have h:=SemiprimeD1StackDescriptorRecordBounds.machine_prefix_cells I.static sourceMap oldTemplate inputFields hraw
    (T.answer (inputFields 0) (inputFields 2)) (T.budget (inputFields 0) (inputFields 2)) hc words hist out fuel cfg hr
  rw [SemiprimeD1StackPublicCarry.stack_card] at h
  exact h
end RiemannGaussian.SemiprimeD1StackCarryDescriptorRecordBounds

namespace RiemannGaussian.SemiprimeD1StackCarryDescriptorRecordOriginal
open SemiprimeD1StackCarryDescriptorRecord SemiprimeD1StackCarryDescriptorRecordExecution
open SemiprimeMacroParameters SemiprimeBitArithmetic
namespace Bank
export SemiprimeD1OrdinalBankSpec (idAt)
end Bank
namespace Log
export SemiprimeD1StackVertexRecordStreamExecution (rows history)
end Log
/-- Exact old input vertex with the caller's unchanged ordered numeric scope. -/
abbrev vertex :=SemiprimeD1StackPublicCarryRecordOriginal.vertex
variable (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
  (i : Fin (firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))))
  (indexWord : List Bool) (hi : indexWord.length=i.val) (M : Nat) (ports : List Nat)
  (hp : ∀j∈ports,j<M)
  (hlen : ports.length=SemiprimeMacroGraph.subdividedArity
    (.inl (.carry i):SemiprimePublicAcquiredExecution.PublicVertex (bitValue bits)))
include hc hi hp
/-- Actual newly loaded input row bytes are exactly the frozen entire old input
record, including complete original tensor framing and unary numeric ports. -/
theorem record_bytes_original (rest : List SemiprimeD1LeafCounter.Vertex) :
    SemiprimeD1StackVertexRecordStream.row
      (SemiprimeD1StackPortOrdinalStream.result (ports.map (Bank.idAt M)))
      (SemiprimeD1StackPublicCarryTableExecution.table bits indexWord (ports.map (Bank.idAt M)))++
      SemiprimeD1StackVertexProduct.records rest=
      SemiprimeD1StackVertexProduct.records
        (vertex (bitValue bits) hN (.inl (.carry i)) ports hlen::rest) :=
  SemiprimeD1StackPublicCarryRecordOriginal.record_bytes_original bits hc hN i indexWord hi M ports hp hlen rest
/-- Actual physical descriptor initialization followed by the actual record
call preserves every previous row in its original chronological order. -/
theorem history_original (tag coord1 coord2 coord3 : List Bool)
    (previous : List SemiprimeD1LeafCounter.Vertex) (old out : List Bool) :
    (done (fields bits tag indexWord coord1 coord2 coord3) (ports.map (Bank.idAt M))
      (Log.history previous old) out).data D.history=
      Log.history (previous++[vertex (bitValue bits) hN (.inl (.carry i)) ports hlen]) old := by
  change (done _ _ _ _).data (D.recordStack SemiprimeD1StackPublicCarryRecord.G.history)=_
  rw [component_done]
  exact SemiprimeD1StackPublicCarryRecordOriginal.history_original bits hc hN i indexWord hi M ports hp hlen previous old out
/-- One final actual logger reversal emits exactly the forward old record list
and final false tag, retaining the caller's final output suffix. -/
theorem reverse_original (tag coord1 coord2 coord3 : List Bool)
    (previous : List SemiprimeD1LeafCounter.Vertex) (out : List Bool) :
    SemiprimeD1StackBytecode.run SemiprimeD1StackVertexRecordStream.code
      (2*(Log.rows (previous++[vertex (bitValue bits) hN (.inl (.carry i)) ports hlen])).length+2)
      ⟨some .reverse,none,SemiprimeD1StackVertexRecordStream.data [] []
        ((done (fields bits tag indexWord coord1 coord2 coord3) (ports.map (Bank.idAt M))
          (Log.history previous []) (false::out)).data D.history) (false::out)⟩=
      some ⟨none,none,SemiprimeD1StackVertexRecordStream.data [] [] []
        (SemiprimeD1StackVertexProduct.records
          (previous++[vertex (bitValue bits) hN (.inl (.carry i)) ports hlen])++out)⟩ := by
  rw [history_original bits hc hN i indexWord hi M ports hp hlen]
  exact SemiprimeD1StackVertexRecordStreamExecution.reverse_original _ out
/-- Complete real source trace and exact old chronological record, from ONLY
actual six acquired fields, acquired numeric scope, caller words and erased dirty template. -/
theorem source_run_original (oldTemplate : Checker→List Bool) (tag coord1 coord2 coord3 : List Bool)
    (previous : List SemiprimeD1LeafCounter.Vertex) (old out : List Bool) :
    ∃t≤timeBound oldTemplate (fields bits tag indexWord coord1 coord2 coord3)
      (ports.map (Bank.idAt M)) (Log.history previous old) out,∃finish,
      SemiprimeD1StackCalls.run program t
        (initial oldTemplate (fields bits tag indexWord coord1 coord2 coord3)
          (SemiprimeD1TensorTapeCodec.vectorBits (ports.map (Bank.idAt M))) (Log.history previous old) out)=some finish ∧
      finish=done (fields bits tag indexWord coord1 coord2 coord3) (ports.map (Bank.idAt M)) (Log.history previous old) out ∧
      finish.data D.history=Log.history
        (previous++[vertex (bitValue bits) hN (.inl (.carry i)) ports hlen]) old := by
  have hb:bits≠[]:=by intro he;subst bits;exact (Nat.not_lt_zero _ hN).elim
  obtain ⟨t,ht,hr⟩:=source_run oldTemplate (fields bits tag indexWord coord1 coord2 coord3) hb
    (ports.map (Bank.idAt M)) (Log.history previous old) out
  exact ⟨t,ht,_,hr,rfl,history_original bits hc hN i indexWord hi M ports hp hlen tag coord1 coord2 coord3 previous old out⟩
end RiemannGaussian.SemiprimeD1StackCarryDescriptorRecordOriginal
