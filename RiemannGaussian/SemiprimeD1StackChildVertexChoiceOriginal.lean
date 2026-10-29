/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildVertexChoiceBounds
/-! # SAME actual activity caller yields the complete original child vertex
Original-family acquisitions derive scope and ordinal order, including empty
inactive scopes. Neither an activation mask nor a table answer enters control.
This eight-word prepared caller leaves stream extraction to its enclosing zip.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildVertexChoiceOriginal
open SemiprimeD1StackChildVertexChoice SemiprimeD1StackChildVertexChoiceSpec
open SemiprimeD1StackChildVertexChoiceBounds SemiprimeD1StackChildVertexChoiceSource
open SemiprimeD1StackChildVertexChoiceView
open SemiprimeD1ChildOldEntrySemantics (data order)
open SemiprimeD1TensorNetwork (Network leftPorts)
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeD1StackUnaryDivmod (unary)
/-- The singleton operand comes from this actual original metadata bit, not an externally supplied mask. -/
def activityBit (net : Network) (r a : ℕ) (q : Fin a) (g : Fin r)
    (v : Fin (net.leftCount+net.rows.length)) : Bool:=
  ((data net r a q g).activation.bits[v.val]?).getD false
/-- Canonical original child scope, obtained by the actual routing acquisition. -/
def ports (net : Network) (r a : ℕ) (q : Fin a) (g : Fin r)
    (v : Fin (net.leftCount+net.rows.length)) : List ℕ:=
  leftPorts (SemiprimeD1TensorNetworkLayout.childRows (data net r a q g).graph) v
/-- Exactly eight physical source words, before either branch starts acquiring its output. -/
def acquiredSource (net : Network) (r a : ℕ) (q : Fin a) (g : Fin r)
    (old : SemiprimeD1JetAxes.Context) (extra : List ℕ) (oldp newp : List Bool)
    (v : Fin (net.leftCount+net.rows.length)) : C.State Stack Label:=
  originalInitial old extra oldp newp (SemiprimeD1ChildNetwork.parentVertex net v).table
    (order net r a q g v).order (ports net r a q g v) (activityBit net r a q g v)
/-- Complete169-word stopped bank, retaining the actual old and new headers separately. -/
noncomputable def acquiredDone (net : Network) (r a : ℕ) (q : Fin a) (g : Fin r)
    (old : SemiprimeD1JetAxes.Context) (extra : List ℕ) (oldp newp : List Bool)
    (v : Fin (net.leftCount+net.rows.length)) : C.State Stack Label:=
  done old extra oldp newp (SemiprimeD1ChildNetwork.parentVertex net v).table
    (order net r a q g v).order (ports net r a q g v) (activityBit net r a q g v)
/-- Exact complete native bytes in BOTH branches, including the record-list terminator. -/
theorem output_original (net : Network) (r a : ℕ) [NeZero r] (q : Fin a) (g : Fin r)
    (old : SemiprimeD1JetAxes.Context) (ho : old.Positive) (extra : List ℕ) (he : 0<extra.prod)
    (oldp newp : List Bool) (v : Fin (net.leftCount+net.rows.length)) :
    (acquiredDone net r a q g old extra oldp newp v).data output=
      SemiprimeD1StackVertexProduct.records
        [(SemiprimeD1ChildNetworkTape.leftOne net (data net r a q g) old extra
          (SemiprimeBitArithmetic.bitValue newp) v).1] := by
  have hn:=SemiprimeD1StackChildTableEntryOriginal.appended_positive old.axes extra ho he
  unfold acquiredDone done SemiprimeD1StackChildVertexChoiceExecution.stopped result
  cases h : activityBit net r a q g v
  · simp only [Bool.false_eq_true,ite_false]
    rw [inactive_output]
    rw [SemiprimeD1StackChildUnitVertexSpec.native_inactive net r a q g old extra _ v h]
    exact SemiprimeD1StackChildUnitVertexOriginal.record_original (extra++old.axes) newp hn
  · rw [SemiprimeD1StackChildLiftVertexMeaning.original_active_vertex net r a q g old extra newp v h]
    rfl
/-- Whole literal pop→actual branch source→true halt, with original scope/order facts derived internally. -/
theorem source_run_actual (net : Network) (r a : ℕ) [NeZero r] (q : Fin a) (g : Fin r)
    (old : SemiprimeD1JetAxes.Context) (ho : old.Positive) (extra : List ℕ) (he : 0<extra.prod)
    (oldp newp : List Bool) (hp : SemiprimeBitArithmetic.bitValue oldp=old.precision)
    (hg : SemiprimeD1TensorNetwork.Good old net) (v : Fin (net.leftCount+net.rows.length)) :
    ∃t≤polynomial old extra oldp newp (SemiprimeD1ChildNetwork.parentVertex net v).table
      (order net r a q g v).order (ports net r a q g v),
      SemiprimeD1StackCalls.run program t (acquiredSource net r a q g old extra oldp newp v)=
        some (acquiredDone net r a q g old extra oldp newp v) ∧
      (acquiredDone net r a q g old extra oldp newp v).data output=
        SemiprimeD1StackVertexProduct.records
          [(SemiprimeD1ChildNetworkTape.leftOne net (data net r a q g) old extra
            (SemiprimeBitArithmetic.bitValue newp) v).1] := by
  obtain ⟨t,ht,hr⟩:=source_run_bounded old ho extra he oldp newp hp
    (SemiprimeD1ChildNetwork.parentVertex net v).table
    (SemiprimeD1ChildNetwork.parentVertex_good old net hg v)
    (order net r a q g v).order (ports net r a q g v) (activityBit net r a q g v)
  exact ⟨t,ht,hr,output_original net r a q g old ho extra he oldp newp v⟩
/-- Distinct retained old binary precision role. -/
def oldPrecision : A.Stack:=A.table (SemiprimeD1StackVectorTable.template
  (SemiprimeD1StackChildTableEntry.context false J.precisionBits))
/-- Distinct retained old axis header role. -/
def oldAxes : A.Stack:=A.table (SemiprimeD1StackVectorTable.template
  (SemiprimeD1StackChildTableEntry.context false J.axesCache))
/-- Both actual binary precision words and the appended new axis header survive either source branch. -/
theorem headers_retained {d : ℕ} (old : SemiprimeD1JetAxes.Context) (extra : List ℕ)
    (oldp newp : List Bool) (parent : SemiprimeD1TensorTables.Table d) (permutation scope : List ℕ) (bit : Bool) :
    (done old extra oldp newp parent permutation scope bit).data (active oldPrecision)=oldp ∧
    (done old extra oldp newp parent permutation scope bit).data (active newPrecision)=newp ∧
    (done old extra oldp newp parent permutation scope bit).data (active oldAxes)=vectorBits (old.axes.map unary) ∧
    (done old extra oldp newp parent permutation scope bit).data (active newAxes)=vectorBits ((extra++old.axes).map unary) := by
  let aa:=(AO.originalInitial old extra oldp newp parent permutation scope).data
  let uu:=(UO.done (extra++old.axes) newp).data
  cases bit
  · constructor
    · exact (inactive_foreign aa uu oldPrecision (by decide) (by decide) (by decide) (by decide)).trans rfl
    constructor
    · change inactiveResult aa uu (inactive (U.context J.precisionBits))=newp
      rw [inactive_project];rfl
    constructor
    · exact (inactive_foreign aa uu oldAxes (by decide) (by decide) (by decide) (by decide)).trans rfl
    · change inactiveResult aa uu (inactive (U.context J.axesCache))=vectorBits ((extra++old.axes).map unary)
      rw [inactive_project];rfl
  · exact ⟨rfl,rfl,rfl,rfl⟩
end RiemannGaussian.SemiprimeD1StackChildVertexChoiceOriginal
