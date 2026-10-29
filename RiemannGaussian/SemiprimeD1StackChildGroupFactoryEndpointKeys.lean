/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryEndpointLoop
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryActivationMap
/-! # Computed endpoint flags from the actual preceding activation map
No classification, row getter or unread suffix is a runtime input. All are
mathematical interpretations of the physically acquired lookup source bytes.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryEndpointKeys
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactory
namespace Act
export SemiprimeD1StackChildGroupFactoryActivationLoop (Row)
export SemiprimeD1StackChildGroupFactoryActivationMap (entries flags lookup_value)
end Act
namespace End
export SemiprimeD1StackChildGroupFactoryEndpointLoop (Row pairs placements Valid)
end End
namespace Parse
export SemiprimeD1StackChildGroupFactoryEndpointParse (Fields payload)
end Parse
open SemiprimeBitArithmetic (bitValue)
open SemiprimeSourceHistogramKeyBits (frame)
/-- Only actual paired source fields are encoded; no computed flags enter either source tape. -/
def pairs:List Parse.Fields→List Bool
  | []=>[false]
  | f::fs=>true::frame f.owner (frame f.factor (pairs fs))
/-- Only the actual six original placement fields, including real validity, enter the source vector. -/
def placements:List Parse.Fields→List Bool
  | []=>[false]
  | f::fs=>true::frame (Parse.payload f) (placements fs)
/-- Computed lookup meanings for the proof of the literal loop, never additional physical operands. -/
def row (i:Inputs) (coordinate:Nat) (activation:List Act.Row) (f:Parse.Fields):End.Row:=
  let records:=Act.entries i coordinate [] activation
  ⟨f,(Act.flags i coordinate activation).getD (bitValue f.owner) false,
    (Act.flags i coordinate activation).getD (bitValue f.factor) false,
    (SemiprimeD1StackOwnerLookup.result f.owner records []).2,
    (SemiprimeD1StackOwnerLookup.result f.factor records []).2⟩
/-- Actual source input words are independent of all proof-only computed classifications. -/
theorem pairs_rows (i:Inputs) (coordinate:Nat) (activation:List Act.Row) (fields:List Parse.Fields):
    End.pairs (fields.map (row i coordinate activation))=pairs fields:=by
  induction fields with
  | nil=>rfl
  | cons f fs ih=>simp only [List.map_cons,End.pairs,pairs,row,ih]
/-- Actual placement bytes retain complete raw packets/slots/positive original occurrence IDs. -/
theorem placements_rows (i:Inputs) (coordinate:Nat) (activation:List Act.Row) (fields:List Parse.Fields):
    End.placements (fields.map (row i coordinate activation))=placements fields:=by
  induction fields with
  | nil=>rfl
  | cons f fs ih=>simp only [List.map_cons,End.placements,placements,row,ih]
/-- Typed original vertex domains suffice even for differently padded binary query words. -/
theorem row_valid (i:Inputs) (coordinate:Nat) (activation:List Act.Row) (f:Parse.Fields)
    (ho:bitValue f.owner < activation.length) (hf:bitValue f.factor < activation.length):
    End.Valid (Act.entries i coordinate [] activation) [row i coordinate activation f]:=by
  intro r hr
  have he:r=row i coordinate activation f:=List.mem_singleton.mp hr
  subst r
  constructor
  · exact Prod.ext (Act.lookup_value i coordinate activation [] f.owner (bitValue f.owner) ho
      (by simp only [SemiprimeBitArithmetic.bitValue,Nat.zero_add])) rfl
  · exact Prod.ext (Act.lookup_value i coordinate activation [] f.factor (bitValue f.factor) hf
      (by simp only [SemiprimeBitArithmetic.bitValue,Nat.zero_add])) rfl
/-- Every loop classification and unread-byte witness follows from the one actual generated map. -/
theorem rows_valid (i:Inputs) (coordinate:Nat) (activation:List Act.Row) (fields:List Parse.Fields)
    (hdom:∀f∈fields,bitValue f.owner < activation.length ∧ bitValue f.factor < activation.length):
    End.Valid (Act.entries i coordinate [] activation) (fields.map (row i coordinate activation)):=by
  intro r hr
  obtain ⟨f,hf,rfl⟩:=List.mem_map.mp hr
  exact row_valid i coordinate activation f (hdom f hf).1 (hdom f hf).2 _ List.mem_cons_self
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryEndpointKeys
