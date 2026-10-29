/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildTableEntryView
import RiemannGaussian.SemiprimeD1StackChildTableEntryPrimitives
/-! # Real ordered physical gather and actual serialized parent table lookup -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildTableEntryBackend
open SemiprimeD1StackChildTableEntry SemiprimeD1StackChildTableEntryEncoding
open SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits tape)
namespace Link
export SemiprimeD1StackMultiplierLink (DataRel)
end Link
local notation "ctl"=>Label.local
/-- Actual gather reads the paid physical unary-index vector and retains the whole original assignment. -/
theorem gather_call (assignment:List Bool) (indices:List (List Bool)) (old child:J.Stack→List Bool)
    (t:T.Stack→List Bool) (r:R.Stack→List Bool) (a:Aux→List Bool):
    ∃q ≤ SemiprimeD1StackGatherBytecode.budget assignment.length (vectorBits indices).length+1,
      Runs program q (ctl .gather)
        (bank old child (G.contents (vectorBits indices) assignment [] [] [] []) t r a) (ctl .copyTable)
        (bank old child (G.contents [] assignment [] [] [] (SemiprimeD1StackBitGather.values assignment indices)) t r a):=by
  let start:SemiprimeD1StackBytecode.State G.Stack G.Label:=
    ⟨some G.entry,none,G.contents (vectorBits indices) assignment [] [] [] []⟩
  let stop:SemiprimeD1StackBytecode.State G.Stack G.Label:=
    ⟨none,none,G.contents [] assignment [] [] [] (SemiprimeD1StackBitGather.values assignment indices)⟩
  have hin:Link.DataRel gather (bank old child start.store t r a) start.store (bank old child start.store t r a):=⟨fun _=>rfl,fun _ _=>rfl⟩
  have hout:Link.DataRel gather (bank old child start.store t r a) stop.store (bank old child stop.store t r a):=by
    constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k|k|k|k|k
      · rfl
      · rfl
      · exact False.elim (hk k rfl)
      · rfl
      · rfl
      · rfl
  obtain ⟨q,hq,hr⟩:=SemiprimeD1StackGatherBytecode.gather_run assignment indices [] []
  have hrun:SemiprimeD1StackBytecode.run G.code q start=some stop:=by simpa only [List.append_nil] using hr
  exact ⟨q+1,by omega,included_call program gather Label.gather gather_injective G.code G.entry (fun _=>rfl)
    (ctl .gather) (ctl .copyTable) rfl q start stop _ _ rfl rfl hrun hin hout⟩
/-- Actual serialized tree read consumes DIRECT gathered path bits, scans all skipped subtrees and acquires every original coefficient byte. -/
theorem tree_call {d:Nat} (table:SemiprimeD1TensorTables.Table d) (path assignment:List Bool)
    (old child:J.Stack→List Bool) (r:R.Stack→List Bool) (a:Aux→List Bool):
    ∃q ≤ SemiprimeD1StackTreeBytecode.budget (tape table).length+1,
      Runs program q (ctl .lookup)
        (bank old child (G.contents [] assignment [] [] [] path) (T.contents (tape table) [] [] [] []) r a) (ctl .copyEntry)
        (bank old child (G.contents [] assignment [] [] [] (path.drop d))
          (T.contents [] [] [] [] (vectorBits (SemiprimeD1TensorTables.lookup table path).words)) r a):=by
  let start:SemiprimeD1StackBytecode.State T.Stack T.Label:=⟨some T.entry,none,T.contents (tape table) [] path [] []⟩
  let stop:SemiprimeD1StackBytecode.State T.Stack T.Label:=
    ⟨none,none,T.contents [] [] (path.drop d) [] (vectorBits (SemiprimeD1TensorTables.lookup table path).words)⟩
  let before:=bank old child (G.contents [] assignment [] [] [] path) (T.contents (tape table) [] [] [] []) r a
  let after:=bank old child (G.contents [] assignment [] [] [] (path.drop d))
    (T.contents [] [] [] [] (vectorBits (SemiprimeD1TensorTables.lookup table path).words)) r a
  have hin:Link.DataRel tree before start.store before:=by
    constructor
    · intro k;cases k <;> rfl
    · intro k _;rfl
  have hout:Link.DataRel tree before stop.store after:=by
    constructor
    · intro k;cases k <;> rfl
    · intro k hk
      rcases k with k|k|k|k|k|k
      · rfl
      · rfl
      · cases k with
        | output=>exact False.elim (hk .path rfl)
        | input|assignment|reader|scratch|accumulator=>rfl
      · cases k with
        | path=>rfl
        | input=>exact False.elim (hk .input rfl)
        | tasks=>exact False.elim (hk .tasks rfl)
        | scratch=>exact False.elim (hk .scratch rfl)
        | output=>exact False.elim (hk .output rfl)
      · rfl
      · rfl
  obtain ⟨q,hq,hr⟩:=SemiprimeD1StackTreeBytecode.tree_run table path []
  have hrun:SemiprimeD1StackBytecode.run T.code q start=some stop:=by simpa only [List.append_nil] using hr
  exact ⟨q+1,by omega,included_call program tree Label.tree tree_injective T.code T.entry (fun _=>rfl)
    (ctl .lookup) (ctl .copyEntry) rfl q start stop before after rfl rfl hrun hin hout⟩
end RiemannGaussian.SemiprimeD1StackChildTableEntryBackend
