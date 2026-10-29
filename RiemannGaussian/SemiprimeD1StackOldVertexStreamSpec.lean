/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOldVertexStreamOperands
/-! # Exact chronological input and output specifications
These descriptors describe physical streams and proved outputs. They are not
accepted by the parameterless source program as callbacks or control data.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackOldVertexStreamSpec
open SemiprimeD1StackOldVertexStream SemiprimeD1StackOldVertexStreamRoles
open SemiprimeD1StackOldVertexStreamView SemiprimeD1StackOldVertexStreamOperands
open SemiprimeD1TensorTapeCodec (tape vectorBits)
open SemiprimeD1StackUnaryDivmod (unary)
namespace Q
export SemiprimeD1StackChildVertexChoiceSpec (originalInitial done resource)
export SemiprimeD1StackChildVertexChoiceBounds (polynomial)
end Q
/-- One row in the original chronological stream, with physically acquired metadata. -/
structure Row where
  /-- Actual old full parent vertex. -/
  parent : SemiprimeD1LeafCounter.Vertex
  /-- Actual acquired canonical ordinal order. -/
  order : List ℕ
  /-- Actual acquired child scope, including empty inactive scopes. -/
  scope : List ℕ
  /-- Actual acquired activity bit. -/
  activity : Bool
/-- Literal port bytes, physically read and then drained by the source. -/
def parentPorts (v : Row) : List Bool:=SemiprimeD1StackVertexReadExecution.portTape v.parent.ports
/-- Literal old parent tensor bytes, physically parsed into the real template. -/
def parentTable (v : Row) : List Bool:=tape v.parent.table
/-- Exact actual canonical scope vector. -/
def scopeWord (v : Row) : List Bool:=vectorBits (v.scope.map unary)
/-- Exact actual acquired ordinal order vector. -/
def orderWord (v : Row) : List Bool:=SemiprimeD1StackChildTableEntryPrepare.orderTape v.order
/-- Complete original family of physical eight-word inputs. -/
def inputs (old : SemiprimeD1JetAxes.Context) (extra : List ℕ) (oldp newp : List Bool) (rows : List Row) : Inputs:=
  ⟨SemiprimeD1StackVertexProduct.records (rows.map Row.parent),rows.map Row.activity,
    vectorBits (rows.map scopeWord),vectorBits (rows.map orderWord),
    vectorBits (old.axes.map unary),oldp,vectorBits ((extra++old.axes).map unary),newp⟩
/-- Exact stable waiting bank at any real stream suffix. -/
def waiting (rows : List Row) (history : List Bool) : Words:=
  ⟨fun _=>[],SemiprimeD1StackVertexProduct.records (rows.map Row.parent),rows.map Row.activity,
    vectorBits (rows.map scopeWord),vectorBits (rows.map orderWord),[],history,[],[]⟩
/-- Four actually acquired work operands, while all stream readers already point at their real tails. -/
def prepared (v : Row) (rows : List Row) (history : List Bool) : Words:=
  {waiting rows history with source:=sparse (parentTable v) (orderWord v) (scopeWord v) [v.activity],oldPorts:=parentPorts v}
/-- Complete output vertex of the SAME active or inactive constructor. -/
def vertex (old : SemiprimeD1JetAxes.Context) (extra : List ℕ) (newp : List Bool) (v : Row) : SemiprimeD1LeafCounter.Vertex:=
  if v.activity then SemiprimeD1StackChildLiftVertexOriginal.vertex old extra newp v.parent.table v.order v.scope
  else SemiprimeD1StackChildUnitVertexSpec.vertex ⟨extra++old.axes,SemiprimeBitArithmetic.bitValue newp⟩
/-- Exact original canonical vertex row without the surrounding stream EOF. -/
def row (old : SemiprimeD1JetAxes.Context) (extra : List ℕ) (newp : List Bool) (v : Row) : List Bool:=
  SemiprimeD1StackVertexRecordSpliceMeaning.row (vertex old extra newp v)
/-- The exact whole169 stopped bank, before row logging and physical cleanup. -/
noncomputable def childDone (old : SemiprimeD1JetAxes.Context) (extra : List ℕ) (oldp newp : List Bool) (v : Row) :
    C.State ChoiceStack X.Label:=Q.done old extra oldp newp v.parent.table v.order v.scope v.activity
/-- Every coefficient bit of the generic active/inactive result is the canonical complete singleton. -/
theorem output_bytes (old : SemiprimeD1JetAxes.Context) (ho : old.Positive)
    (extra : List ℕ) (he : 0<extra.prod) (oldp newp : List Bool) (v : Row) :
    (childDone old extra oldp newp v).data X.output=row old extra newp v++[false]:=by
  have hn:=SemiprimeD1StackChildTableEntryOriginal.appended_positive old.axes extra ho he
  unfold row
  rw [←SemiprimeD1StackVertexRecordSpliceMeaning.singleton_stream]
  unfold childDone SemiprimeD1StackChildVertexChoiceSpec.done SemiprimeD1StackChildVertexChoiceExecution.stopped
    SemiprimeD1StackChildVertexChoiceSpec.result
  cases hb : v.activity
  · change SemiprimeD1StackChildVertexChoiceView.inactiveResult
      (SemiprimeD1StackChildLiftVertexOriginal.originalInitial old extra oldp newp v.parent.table v.order v.scope).data
      (SemiprimeD1StackChildUnitVertexOriginal.done (extra++old.axes) newp).data X.output=_
    rw [SemiprimeD1StackChildVertexChoiceSpec.inactive_output]
    change SemiprimeD1StackChildUnitVertexFrames.recordWord (extra++old.axes) newp=_
    simpa only [vertex,hb,Bool.false_eq_true,ite_false,SemiprimeD1StackChildUnitVertexCalls.ctx] using
      SemiprimeD1StackChildUnitVertexOriginal.record_original (extra++old.axes) newp hn
  · change SemiprimeD1StackVertexProduct.records
      [SemiprimeD1StackChildLiftVertexOriginal.vertex old extra newp v.parent.table v.order v.scope]=_
    rw [vertex,hb,ite_eq_left rfl]
/-- Every included original source input is the exact actual sparse parsed bank plus retained headers. -/
theorem prepared_project (old : SemiprimeD1JetAxes.Context) (extra : List ℕ) (oldp newp : List Bool)
    (all rows : List Row) (v : Row) (history : List Bool) (k : ChoiceStack) :
    data (inputs old extra oldp newp all) (prepared v rows history) (choice k)=
      (Q.originalInitial old extra oldp newp v.parent.table v.order v.scope v.activity).data k:=by
  rw [project]
  exact congrFun (initial_sparse (inputs old extra oldp newp all) (parentTable v) (orderWord v) (scopeWord v) [v.activity]) k
end RiemannGaussian.SemiprimeD1StackOldVertexStreamSpec
