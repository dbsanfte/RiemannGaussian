/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildUnitVertex
import RiemannGaussian.SemiprimeD1ChildTableDirect
import RiemannGaussian.SemiprimeD1ChildOldEntrySemantics
/-! # Exact whole native inactive vertex and dense-unit byte specification
No inactive parent table is required by the source. Native acquisition lengths
internally imply the empty canonical port list, including isolated vertices.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildUnitVertexSpec
open SemiprimeD1JetAxes (Context)
open SemiprimeD1TensorNetwork (Network leftPorts)
open SemiprimeD1ChildOldEntrySemantics (data order)
/-- Whole canonical zero-port unit vertex; only a proof/output specification. -/
def vertex (ctx : Context) : SemiprimeD1LeafCounter.Vertex := ⟨[],(SemiprimeD1ChildTensorTables.unit ctx).table⟩
/-- The literal dense-adder unit output matches EVERY raw native inactive coefficient. -/
theorem one_words (ctx : Context) (hp : ∀q∈ctx.axes,0<q) :
    (SemiprimeD1JetAffineCoefficient.one ctx).words=
      (SemiprimeD1TensorTables.lookup (SemiprimeD1ChildTensorTables.unit ctx).table []).words := by
  have h:=SemiprimeD1ChildOldEntrySemantics.unitWords_scalar ctx hp
  dsimp only [SemiprimeD1ChildOldEntrySemantics.unitWords,SemiprimeD1JetPolynomialBits.scalar] at h
  rw [SemiprimeSourceCompactBits.copy_bits] at h
  exact h.symm
/-- Literal FALSE table tag turns the actually acquired dense vector into the exact unit table tape. -/
theorem table_tape (ctx : Context) (hp : ∀q∈ctx.axes,0<q) :
    false::SemiprimeD1TensorTapeCodec.vectorBits (SemiprimeD1JetAffineCoefficient.one ctx).words=
      SemiprimeD1TensorTapeCodec.tape (vertex ctx).table := by
  rw [one_words ctx hp]
  dsimp only [vertex,SemiprimeD1ChildTensorTables.unit,SemiprimeD1TensorTables.lookup,SemiprimeD1TensorTapeCodec.tape]
  rw [SemiprimeD1JetAxes.copyVector_value]
/-- Original inactive metadata forces the ACTUAL canonical scope empty; no emptiness advice is supplied. -/
theorem inactive_ports (net : Network) (r a : ℕ) [NeZero r] (q : Fin a) (g : Fin r)
    (v : Fin (net.leftCount+net.rows.length))
    (ha : ((data net r a q g).activation.bits[v.val]?).getD false=false) :
    leftPorts (SemiprimeD1TensorNetworkLayout.childRows (data net r a q g).graph) v=[] := by
  have h:=SemiprimeD1ChildTableOrder.inactive_child_empty net.leftCount net.rows.length r a
    (SemiprimeD1TensorNetwork.arity net.rows) (SemiprimeD1TensorNetwork.owner net.rows) q g v ha
  have hc:=SemiprimeD1ChildOldEntrySemantics.child_length net r a q g v
  rw [h,List.length_nil] at hc
  exact List.eq_nil_of_length_eq_zero hc
/-- ENTIRE original inactive child vertex equals the literal unit; aligned-parent bytes and canonical recopy are unnecessary. -/
theorem native_inactive (net : Network) (r a : ℕ) [NeZero r] (q : Fin a) (g : Fin r)
    (old : Context) (extra : List ℕ) (p : ℕ) (v : Fin (net.leftCount+net.rows.length))
    (ha : ((data net r a q g).activation.bits[v.val]?).getD false=false) :
    (SemiprimeD1ChildNetworkTape.leftOne net (data net r a q g) old extra p v).1=vertex ⟨extra++old.axes,p⟩ := by
  dsimp only [SemiprimeD1ChildNetworkTape.leftOne,SemiprimeD1ChildTensorTablesTape.fromCache]
  rw [ha,inactive_ports net r a q g v ha]
  exact SemiprimeD1ChildTableDirect.canonical_recopy [] (SemiprimeD1ChildTensorTables.unit ⟨extra++old.axes,p⟩).table
end RiemannGaussian.SemiprimeD1StackChildUnitVertexSpec
