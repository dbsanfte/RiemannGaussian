/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryEndpointOperationBounds
/-! # Entire actual forward-endpoint source clock from paid source/map bytes -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryEndpointBounds
namespace Raw
export SemiprimeD1StackChildGroupFactoryAcquisitionByteBounds (fieldBytes)
end Raw
namespace Loop
export SemiprimeD1StackChildGroupFactoryEndpointLoop (Row pairs placements Valid timeBound)
end Loop
namespace View
export SemiprimeD1StackChildGroupFactoryEndpointLoopView (oldRecords selectedRecords chosen)
end View
namespace Old
export SemiprimeD1StackChildGroupFactoryEndpointOldLog (row oldPoint)
end Old
namespace Emit
export SemiprimeD1StackChildGroupFactoryEndpointEmit (row endpoint)
end Emit
namespace Map
export SemiprimeD1StackOwnerLookup (records)
end Map
/-- Every original side's actual old-tag record is paid by its acquired fields. -/
theorem old_row_bytes (owner:Bool) (v edge:List Bool):
    (Old.row owner v edge).length≤20*(v.length+edge.length+1):=by
  simp only [Old.row,Old.oldPoint,List.length_cons,List.length_nil,SemiprimeSourceHistogramKeyBits.frame_length]
  omega
/-- Every actually selected side has literal bounded five-field record bytes. -/
theorem chosen_bytes (owner flag:Bool) (f:SemiprimeD1StackChildGroupFactoryEndpointParse.Fields):
    (View.chosen owner flag f).length≤20*Raw.fieldBytes f:=by
  cases owner <;> cases flag <;> simp only [View.chosen,Emit.row,Emit.endpoint,Bool.false_eq_true,
    ite_false,ite_true,List.length_cons,List.length_nil,SemiprimeSourceHistogramKeyBits.frame_length,Raw.fieldBytes] <;> omega
/-- Both computed selected sides remain linear in actual field bytes, regardless of branch. -/
theorem selected_bytes (rows:List Loop.Row) (S:Nat) (hc:∀r∈rows,Raw.fieldBytes r.fields≤S):
    (View.selectedRecords rows).length≤40*S*rows.length:=by
  induction rows with
  | nil=>simp only [View.selectedRecords,List.length_nil,Nat.mul_zero,le_refl]
  | cons r rs ih=>
    have ho:=chosen_bytes true r.ownerFlag r.fields
    have hf:=chosen_bytes false r.factorFlag r.fields
    have hh:=hc r List.mem_cons_self
    have ht:=ih (fun q h=>hc q (List.mem_cons_of_mem r h))
    simp only [View.selectedRecords,List.length_append,List.length_cons]
    nlinarith
/-- Both unmasked old sides remain linear and preserve every original incidence. -/
theorem old_bytes (rows:List Loop.Row) (S:Nat) (hc:∀r∈rows,Raw.fieldBytes r.fields≤S):
    (View.oldRecords rows).length≤40*S*rows.length:=by
  induction rows with
  | nil=>simp only [View.oldRecords,List.length_nil,Nat.mul_zero,le_refl]
  | cons r rs ih=>
    have ho:=old_row_bytes true r.fields.owner r.fields.edge
    have hf:=old_row_bytes false r.fields.factor r.fields.edge
    have hh:=hc r List.mem_cons_self
    have ht:=ih (fun q h=>hc q (List.mem_cons_of_mem r h))
    simp only [View.oldRecords,List.length_append,List.length_cons]
    dsimp only [Raw.fieldBytes] at hh
    nlinarith
/-- All actual numeric lookups and raw-field reads are counted once per acquired original row. -/
theorem loop_time (entries:List (List Bool×List Bool)) (rows:List Loop.Row) (S:Nat)
    (hc:∀r∈rows,Raw.fieldBytes r.fields≤S) (hv:Loop.Valid entries rows):
    Loop.timeBound entries rows≤100000*S*((Map.records entries []).length+1)*rows.length+4:=by
  induction rows with
  | nil=>simp only [Loop.timeBound,List.length_nil,Nat.mul_zero,Nat.zero_add,le_refl]
  | cons r rs ih=>
    have hh:=hv r List.mem_cons_self
    have ho: r.ownerUnread.length≤(Map.records entries []).length:=by
      have h:=(SemiprimeD1StackPacketRowsClock.lookup_lengths r.fields.owner entries).2
      rw [hh.1] at h
      exact h
    have hf:r.factorUnread.length≤(Map.records entries []).length:=by
      have h:=(SemiprimeD1StackPacketRowsClock.lookup_lengths r.fields.factor entries).2
      rw [hh.2] at h
      exact h
    have hr:=SemiprimeD1StackChildGroupFactoryEndpointOperationBounds.occurrence_time r.ownerFlag r.factorFlag
      r.fields entries r.ownerUnread r.factorUnread ho hf
    have hb:=hc r List.mem_cons_self
    have ht:=ih (fun q h=>hc q (List.mem_cons_of_mem r h)) (fun q h=>hv q (List.mem_cons_of_mem r h))
    simp only [Loop.timeBound,List.length_cons]
    nlinarith
/-- Whole real forward endpoint acquisition has one fixed quartic cap in physically paid byte bounds. -/
theorem source_time (entries:List (List Bool×List Bool)) (rows:List Loop.Row) (S:Nat)
    (hc:∀r∈rows,Raw.fieldBytes r.fields≤S) (hv:Loop.Valid entries rows)
    (hn:rows.length≤S) (hraw:(Loop.pairs rows).length+(Loop.placements rows).length≤S)
    (hmap:(Map.records entries []).length≤10*(S+1)^2):
    SemiprimeD1StackChildGroupFactoryEndpointSource.timeBound entries rows≤100000000*(S+1)^4:=by
  have hl:=loop_time entries rows S hc hv
  have hs:=selected_bytes rows S hc
  have ho:=old_bytes rows S hc
  have hm:100000*S*((Map.records entries []).length+1)*rows.length≤
      100000*S*(10*(S+1)^2+1)*S:=by gcongr
  dsimp only [SemiprimeD1StackChildGroupFactoryEndpointSource.timeBound]
  nlinarith
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryEndpointBounds
