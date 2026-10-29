/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryNativeFields
/-! # Original typed incidence/placement lineage and computed endpoint colour flags
All fields come from the exact acquired ordered zip. Actual selected activation
bits at the two real numeric keys yield the original owner/factor colour tests.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryNativePairs
open SemiprimeD1StackChildGroupFactory (Inputs)
namespace Fld
export SemiprimeD1StackChildGroupFactoryNativeFields (source fields ofPair)
end Fld
namespace Key
export SemiprimeSourceHistogramHeadRefinement (numberKey numberKey_value)
end Key
namespace Act
export SemiprimeD1StackChildGroupFactoryNativeActivation (originalIDs flags_original)
export SemiprimeD1StackChildGroupFactoryActivationMap (flags)
end Act
namespace Forward
export SemiprimeD1StackChildGroupFactoryForwardSource (activation)
end Forward
namespace Native
export SemiprimeD1ChildGraphSemantics (zip_alignment original_ports)
export SemiprimeD1PacketInventory (Placement)
end Native
/-- Original factor-major typed source pairs; the real placement list determines the second input bytes. -/
def paired (n F a:Nat) (arity:Fin F→Nat) (owner:((e:Fin F)×Fin (arity e))→Fin n):=
  (SemiprimeD1CollisionOriginal.ports n F a arity).zip (Fld.source n F a arity owner).placements
/-- Literal physical seven fields of one original typed occurrence and its actual replay placement. -/
def fieldOf {n F:Nat} {arity:Fin F→Nat} (owner:((e:Fin F)×Fin (arity e))→Fin n)
    (p:((e:Fin F)×Fin (arity e))×Native.Placement):=
  Fld.ofPair (Key.numberKey (owner p.1).val,Key.numberKey (n+p.1.1.val)) p.2
/-- Typed original pairing and the physically parsed seven words agree on EVERY byte. -/
theorem fields_typed (n F a:Nat) (arity:Fin F→Nat) (owner:((e:Fin F)×Fin (arity e))→Fin n):
    Fld.fields n F a arity owner=(paired n F a arity owner).map (fieldOf owner):=by
  unfold Fld.fields SemiprimeD1StackChildGroupFactoryNativeFields.keys
    SemiprimeD1StackSourceIncidenceSelectMeaning.originalKeys paired SemiprimeD1CollisionOriginal.ports
  rw [List.zip_map_left,List.map_map]
  rfl
/-- Actual replay source equality derives the exact typed incidence/placement pairing. -/
theorem source_aligned (n F a:Nat) (arity:Fin F→Nat) (owner:((e:Fin F)×Fin (arity e))→Fin n)
    (p:((e:Fin F)×Fin (arity e))×Native.Placement) (hp:p∈paired n F a arity owner):
    p.2.source=SemiprimeD1IncidenceAcquisition.originalKey n F 64 a arity owner p.1:=by
  have hs: (Fld.source n F a arity owner).placements.map SemiprimeD1PacketInventory.Placement.source=
      (SemiprimeD1CollisionOriginal.ports n F a arity).map
        (SemiprimeD1IncidenceAcquisition.originalKey n F 64 a arity owner):=
    (SemiprimeD1PacketReplayOriginal.sources n F 64 a arity owner).trans
      (SemiprimeD1IncidenceAcquisition.keys_original n F 64 a arity owner)
  exact Native.zip_alignment _ _ _ hs p hp
/-- Every original physical flag agrees with its finite original selected colour, including isolated vertices. -/
theorem flag_original (i:Inputs) (n F a:Nat) (arity:Fin F→Nat)
    (owner:((e:Fin F)×Fin (arity e))→Fin n) (q:Fin a) (g:Fin 64)
    (hg:SemiprimeBitArithmetic.bitValue i.group=g.val) (v:Fin (n+F)):
    (Act.flags i q.val (Forward.activation a (Act.originalIDs n F a arity owner))).getD v.val false=
      decide (SemiprimeMaterializedScoreEnvironment.denote
        (SemiprimeSourceHistogramHeadOriginal.originalEnv 64 a (Act.originalIDs n F a arity owner)) v.val q=g):=by
  rw [Act.flags_original i n F a arity owner q g hg]
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  simpa only [List.getD_eq_getElem?_getD,Act.originalIDs] using SemiprimeD1ChildActivationOriginal.mask_value n F 64 a arity owner q g v
/-- Actual owner key is its original owner vertex, with no decoded owner supplier. -/
theorem owner_flag (i:Inputs) (n F a:Nat) (arity:Fin F→Nat)
    (owner:((e:Fin F)×Fin (arity e))→Fin n) (q:Fin a) (g:Fin 64)
    (hg:SemiprimeBitArithmetic.bitValue i.group=g.val) (p:((e:Fin F)×Fin (arity e))×Native.Placement):
    (Act.flags i q.val (Forward.activation a (Act.originalIDs n F a arity owner))).getD
      (SemiprimeBitArithmetic.bitValue (fieldOf owner p).owner) false=
      decide ((SemiprimeD1SelectedCollision.selectedLabel n F 64 a arity owner p.1).1 q=g):=by
  have hv:(owner p.1).val<n+F:=by have h:=(owner p.1).isLt;omega
  have h:=flag_original i n F a arity owner q g hg ⟨(owner p.1).val,hv⟩
  apply Bool.eq_iff_iff.mpr
  have hh:=Bool.eq_iff_iff.mp h
  simp only [decide_eq_true_eq] at hh ⊢
  simpa only [fieldOf,Fld.ofPair,Key.numberKey_value,SemiprimeD1SelectedCollision.selectedLabel,
    Act.originalIDs] using hh
/-- Actual disjoint factor key is n+factor, never an occurrence/global-child ordinal. -/
theorem factor_flag (i:Inputs) (n F a:Nat) (arity:Fin F→Nat)
    (owner:((e:Fin F)×Fin (arity e))→Fin n) (q:Fin a) (g:Fin 64)
    (hg:SemiprimeBitArithmetic.bitValue i.group=g.val) (p:((e:Fin F)×Fin (arity e))×Native.Placement):
    (Act.flags i q.val (Forward.activation a (Act.originalIDs n F a arity owner))).getD
      (SemiprimeBitArithmetic.bitValue (fieldOf owner p).factor) false=
      decide ((SemiprimeD1SelectedCollision.selectedLabel n F 64 a arity owner p.1).2 q=g):=by
  have hv:n+p.1.1.val<n+F:=by have h:=p.1.1.isLt;omega
  have h:=flag_original i n F a arity owner q g hg ⟨n+p.1.1.val,hv⟩
  apply Bool.eq_iff_iff.mpr
  have hh:=Bool.eq_iff_iff.mp h
  simp only [decide_eq_true_eq] at hh ⊢
  simpa only [fieldOf,Fld.ofPair,Key.numberKey_value,SemiprimeD1SelectedCollision.selectedLabel,
    Act.originalIDs] using hh
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryNativePairs
