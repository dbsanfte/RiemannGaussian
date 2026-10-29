/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildLiftVertexStorage
import RiemannGaussian.SemiprimeD1ChildTableDirect
import RiemannGaussian.SemiprimeD1ChildOldEntrySemantics
/-! # The actual active old vertex needs neither aligned-table nor canonical-recopy acquisition
Both original metadata lengths are derived from the actual child acquisitions.
The full native vertex/record is preserved; no native clock is transported.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildLiftVertexMeaning
open SemiprimeD1StackChildLiftVertexOriginal
open SemiprimeD1TensorNetwork (Network leftPorts)
open SemiprimeD1ChildOldEntrySemantics (data order)
/-- Generic actual active source loses neither a coefficient nor a canonical port when the two intermediates are removed. -/
theorem active_vertex {a : ℕ} (net : Network) (pulled : SemiprimeD1ChildNetwork.Pullback net a)
    (old : SemiprimeD1JetAxes.Context) (extra : List ℕ) (newp : List Bool)
    (v : Fin (net.leftCount+net.rows.length))
    (ha : (pulled.activation.bits[v.val]?).getD false=true)
    (hc : (leftPorts (SemiprimeD1TensorNetworkLayout.childRows pulled.graph) v).length=
      (SemiprimeD1ChildTableOrder.acquire (SemiprimeD1TensorNetwork.owner net.rows) pulled v).child.length) :
    (SemiprimeD1ChildNetworkTape.leftOne net pulled old extra (SemiprimeBitArithmetic.bitValue newp) v).1=
      vertex old extra newp (SemiprimeD1ChildNetwork.parentVertex net v).table
        (SemiprimeD1ChildTableOrder.acquire (SemiprimeD1TensorNetwork.owner net.rows) pulled v).order
        (leftPorts (SemiprimeD1TensorNetworkLayout.childRows pulled.graph) v) := by
  dsimp only [SemiprimeD1ChildNetworkTape.leftOne,SemiprimeD1ChildTensorTablesTape.fromCache]
  rw [ha]
  exact SemiprimeD1ChildTableDirect.copy_lift_aligned old extra (SemiprimeBitArithmetic.bitValue newp)
    (SemiprimeD1ChildNetwork.parentVertex net v).table
    (SemiprimeD1ChildTableOrder.acquire (SemiprimeD1TensorNetwork.owner net.rows) pulled v).order
    (leftPorts (SemiprimeD1TensorNetworkLayout.childRows pulled.graph) v) _ _
    (SemiprimeD1ChildTableOrder.order_length _ _ _) hc
/-- Actual original-family lengths discharge the generic degree condition, including empty/isolated vertices. -/
theorem original_active_vertex (net : Network) (r a : ℕ) [NeZero r] (q : Fin a) (g : Fin r)
    (old : SemiprimeD1JetAxes.Context) (extra : List ℕ) (newp : List Bool)
    (v : Fin (net.leftCount+net.rows.length))
    (ha : ((data net r a q g).activation.bits[v.val]?).getD false=true) :
    (SemiprimeD1ChildNetworkTape.leftOne net (data net r a q g) old extra (SemiprimeBitArithmetic.bitValue newp) v).1=
      vertex old extra newp (SemiprimeD1ChildNetwork.parentVertex net v).table (order net r a q g v).order
        (leftPorts (SemiprimeD1TensorNetworkLayout.childRows (data net r a q g).graph) v) :=
  active_vertex net (data net r a q g) old extra newp v ha
    (SemiprimeD1ChildOldEntrySemantics.child_length net r a q g v)
/-- SAME physical source writes the ENTIRE actual native active child record, from original parent and actual routing operands. -/
theorem source_run_actual (net : Network) (r a : ℕ) [NeZero r] (q : Fin a) (g : Fin r)
    (old : SemiprimeD1JetAxes.Context) (ho : old.Positive) (extra : List ℕ) (he : 0<extra.prod)
    (oldp newp : List Bool) (hp : SemiprimeBitArithmetic.bitValue oldp=old.precision)
    (hg : SemiprimeD1TensorNetwork.Good old net) (v : Fin (net.leftCount+net.rows.length))
    (ha : ((data net r a q g).activation.bits[v.val]?).getD false=true) :
    let parent:=(SemiprimeD1ChildNetwork.parentVertex net v).table
    let permutation:=(order net r a q g v).order
    let ports:=leftPorts (SemiprimeD1TensorNetworkLayout.childRows (data net r a q g).graph) v
    ∃t≤SemiprimeD1StackChildLiftVertexBounds.polynomial old extra oldp newp parent permutation ports,
      SemiprimeD1StackCalls.run SemiprimeD1StackChildLiftVertex.program t
        (originalInitial old extra oldp newp parent permutation ports)=some (done old extra oldp newp parent permutation ports) ∧
      (done old extra oldp newp parent permutation ports).data (SemiprimeD1StackChildLiftVertex.aux .record)=
        SemiprimeD1StackVertexProduct.records
          [(SemiprimeD1ChildNetworkTape.leftOne net (data net r a q g) old extra (SemiprimeBitArithmetic.bitValue newp) v).1] := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackChildLiftVertexBounds.source_run_bounded old ho extra he oldp newp hp
    (SemiprimeD1ChildNetwork.parentVertex net v).table (SemiprimeD1ChildNetwork.parentVertex_good old net hg v)
    (order net r a q g v).order (leftPorts (SemiprimeD1TensorNetworkLayout.childRows (data net r a q g).graph) v)
  refine ⟨t,ht,hr,?_⟩
  rw [original_active_vertex net r a q g old extra newp v ha]
  rfl
end RiemannGaussian.SemiprimeD1StackChildLiftVertexMeaning
