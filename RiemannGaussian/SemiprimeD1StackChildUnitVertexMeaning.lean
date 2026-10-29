/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildUnitVertexStorage
/-! # Actual inactive child-family vertex from only new original context headers
The activity and source-stream reader remain an enclosing caller obligation.
Here the metadata's inactive bit derives empty canonical ports internally, and
the whole actual finite source writes exactly that native inactive record.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildUnitVertexMeaning
open SemiprimeD1StackChildUnitVertex SemiprimeD1StackChildUnitVertexOriginal
open SemiprimeD1StackChildUnitVertexBounds SemiprimeD1StackChildUnitVertexCalls
open SemiprimeD1ChildOldEntrySemantics (data)
/-- Complete SAME physical32-source native inactive record; neither parent/table nor rank/unit advice is input. -/
theorem source_run_actual (net : SemiprimeD1TensorNetwork.Network) (r a : ℕ) [NeZero r] (q : Fin a) (g : Fin r)
    (old : SemiprimeD1JetAxes.Context) (extra : List ℕ) (newp : List Bool)
    (hp : ∀k∈extra++old.axes,0<k) (v : Fin (net.leftCount+net.rows.length))
    (ha : ((data net r a q g).activation.bits[v.val]?).getD false=false) :
    ∃t≤polynomial (extra++old.axes) newp,
      SemiprimeD1StackCalls.run program t (originalInitial (extra++old.axes) newp)=some (done (extra++old.axes) newp) ∧
      (done (extra++old.axes) newp).data (aux .record)=SemiprimeD1StackVertexProduct.records
        [(SemiprimeD1ChildNetworkTape.leftOne net (data net r a q g) old extra (SemiprimeBitArithmetic.bitValue newp) v).1] := by
  obtain ⟨t,ht,hr⟩:=source_run_bounded (extra++old.axes) hp newp
  refine ⟨t,ht,hr,?_⟩
  rw [SemiprimeD1StackChildUnitVertexSpec.native_inactive net r a q g old extra _ v ha]
  exact record_original (extra++old.axes) newp hp
end RiemannGaussian.SemiprimeD1StackChildUnitVertexMeaning
