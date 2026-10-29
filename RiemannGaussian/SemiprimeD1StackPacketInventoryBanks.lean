/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketInventoryClass
import RiemannGaussian.SemiprimeD1StackPacketInventoryComponents
/-! # Exact physical banks of sparse replay at whole-source boundaries
The apparently displaced input words are actual persistent globals. Component
views below only name their finite tape addresses; no such view enters sigma.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketInventoryBanks
open SemiprimeD1StackPacketInventory SemiprimeD1StackPacketInventoryView
open SemiprimeD1StackPacketInventoryEncoding SemiprimeD1StackPacketInventoryClass
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeSourceHistogramKeyBits (frame)
namespace ReaderWords
export SemiprimeD1StackPacketRowsView (view)
end ReaderWords
namespace OrientationWords
export SemiprimeD1StackPacketOrientationView (view)
end OrientationWords
/-- Exact allocated19 reader words with persistent packet/history globals, acquired vectors and actual success byte. -/
def reader (packets history left right flag:List Bool):R.Stack→List Bool:=
  ReaderWords.view packets history [] [] [] [] [] [] flag [] [] [] [] [] left right
/-- Updating the displaced key allocation really changes only the persistent packet vector. -/
theorem reader_update_packets (packets hist left right flag word:List Bool):
    Function.update (reader packets hist left right flag) (.inr .key) word=reader word hist left right flag :=by
  funext k;rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- Updating the displaced catalogue allocation really changes only the persistent placement history. -/
theorem reader_update_history (packets hist left right flag word:List Bool):
    Function.update (reader packets hist left right flag) (.inr .catalogue) word=reader packets word left right flag :=by
  funext k;rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- A real mapped reader-left-output drain leaves both persistent globals unchanged. -/
theorem reader_update_left (packets hist left right flag word:List Bool):
    Function.update (reader packets hist left right flag) (.inr .leftOutput) word=reader packets hist word right flag :=by
  funext k;rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- A real mapped reader-right-output drain leaves both persistent globals unchanged. -/
theorem reader_update_right (packets hist left right flag word:List Bool):
    Function.update (reader packets hist left right flag) (.inr .rightOutput) word=reader packets hist left word flag :=by
  funext k;rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- Exact allocated19 orientation words with persistent catalogue/seen/slots globals and actual computed packet outputs. -/
def orientation (alphabet seen slots key slot high flag:List Bool):O.Stack→List Bool:=
  OrientationWords.view alphabet seen slots [] [] [] [] [] [] [] [] [] flag [] [] [] key slot high
/-- One actual chronological six-field placement vector row, without the vector's final false marker. -/
def placementRow (p:SemiprimeD1PacketInventory.Placement):List Bool:=true::frame (placementBytes p) []
/-- Complete chronological row bytes; the real loop retains their actual reverse. -/
def history (placements:List SemiprimeD1PacketInventory.Placement):List Bool:=placements.flatMap placementRow
/-- Actual clean loop boundary retains all actual prefix maps and original inputs, with no advised index or packet cache. -/
def boundary (keys alphabet stream:List Bool) (s:Summary):Stack→List Bool:=
  SemiprimeD1StackPacketInventoryView.view (fresh keys stream [] (Dict.dictionary s.classes) s.edge)
    (reader (vectorBits s.packets) (history s.placements).reverse [] [] [])
    (orientation alphabet (Dict.dictionary s.seen) (Dict.dictionary s.slots) [] [] [] [])
/-- Applying the complete real reader's result preserves the two allocated persistent globals, not callee input answers. -/
theorem reader_patch (packets history key cat:List Bool) (left right:List (List Bool)):
    SemiprimeD1StackPacketInventoryComponents.withReader (reader packets history [] [] [])
      (SemiprimeD1StackPacketRowsExecution.done key cat left right).data=
      reader packets history (vectorBits left) (vectorBits right) [true] :=by
  funext k;rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- Applying the complete real orientation result preserves all three allocated globals and exposes only real packet bytes. -/
theorem orientation_patch (alphabet seen slots:List Bool) (left right:List (List Bool)) (index:List Bool):
    SemiprimeD1StackPacketInventoryComponents.withOrientation (orientation alphabet seen slots [] [] [] [])
      (SemiprimeD1StackPacketOrientationExecution.done left right index).data=
      orientation alphabet seen slots (SemiprimeD1OrientationBits.acquire left right index).key
        (SemiprimeD1OrientationBits.acquire left right index).slots (SemiprimeD1OrientationBits.acquire left right index).high [true] :=by
  funext k;rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- The final source history reversal has the exact literal outer vector grammar, including an empty occurrence stream. -/
theorem history_vector (placements:List SemiprimeD1PacketInventory.Placement):
    history placements++[false]=vectorBits (placements.map placementBytes) :=by
  induction placements with
  | nil=>rfl
  | cons p ps ih=>
    change (placementRow p++history ps)++[false]=true::frame (placementBytes p) (vectorBits (ps.map placementBytes))
    rw [List.append_assoc,ih]
    simp only [placementRow,List.cons_append,SemiprimeD1TensorTapeCodec.frame_append,List.nil_append]
/-- One actual logged placement preserves chronological order when later reversed once. -/
theorem history_append (ps:List SemiprimeD1PacketInventory.Placement) (p:SemiprimeD1PacketInventory.Placement):
    history (ps++[p])=history ps++placementRow p :=by
  simp only [history,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]
end RiemannGaussian.SemiprimeD1StackPacketInventoryBanks
