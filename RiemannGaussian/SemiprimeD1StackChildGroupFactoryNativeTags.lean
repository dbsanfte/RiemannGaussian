/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryNativePairs
import RiemannGaussian.SemiprimeD1ChildAssignmentEndpoint
/-! # Exact injective raw old-tag codec derived from the original acquired ID bank
These erased specifications identify actual edge/side bytes already copied by
the source. No tag lookup, inverse, getter or permutation is a runtime operand.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryNativeTags
namespace Pair
export SemiprimeD1StackChildGroupFactoryNativePairs (paired)
end Pair
namespace Fld
export SemiprimeD1StackChildGroupFactoryNativeFields (source)
end Fld
namespace Native
export SemiprimeD1ChildPortBijection (original_ports_nodup original_ports_complete)
export SemiprimeD1ChildPortPullbackCorrectness (ids_value ids_nodup findPort_member)
end Native
/-- Actual unique-key zip lookup, independent of any original graph normalization. -/
theorem lookup_zip {A B:Type} [BEq A] [LawfulBEq A] (xs:List A) (ys:List B) (word:B→List Bool)
    (hn:xs.Nodup) (p:A×B) (hp:p∈xs.zip ys):
    (ys.map word).getD (xs.idxOf p.1) []=word p.2:=by
  induction xs generalizing ys with
  | nil=>simp only [List.zip_nil_left,List.not_mem_nil] at hp
  | cons x xs ih=>
    cases ys with
    | nil=>simp only [List.zip_nil_right,List.not_mem_nil] at hp
    | cons y ys=>
      have hnd:=List.nodup_cons.mp hn
      simp only [List.zip_cons_cons,List.mem_cons] at hp
      rcases hp with rfl|hp
      · simp only [List.map_cons,List.idxOf_cons_self,List.getD_cons_zero]
      · have hne:x≠p.1:=by
          intro he
          exact hnd.1 (he ▸ (List.of_mem_zip hp).1)
        simp only [List.map_cons,List.idxOf_cons_ne _ hne,List.getD_cons_succ]
        exact ih ys hnd.2 hp
/-- Every actual original key has a paired physical placement when acquired lengths agree. -/
theorem exists_zip_right {A B:Type} (xs:List A) (ys:List B) (hl:xs.length=ys.length)
    (x:A) (hx:x∈xs):∃y,(x,y)∈xs.zip ys:=by
  induction xs generalizing ys with
  | nil=>simp only [List.not_mem_nil] at hx
  | cons a xs ih=>
    cases ys with
    | nil=>simp only [List.length_cons,List.length_nil] at hl;omega
    | cons b ys=>
      have ht:xs.length=ys.length:=by simp only [List.length_cons] at hl;omega
      rcases List.mem_cons.mp hx with rfl|hx
      · exact ⟨b,List.mem_cons_self⟩
      · obtain ⟨y,hy⟩:=ih ys ht hx
        exact ⟨y,List.mem_cons_of_mem _ hy⟩
/-- The original edge word is read from its SAME acquired original-position placement. Proof notation only. -/
def edgeFor (n F a:Nat) (arity:Fin F→Nat) (owner:((e:Fin F)×Fin (arity e))→Fin n)
    (port:(e:Fin F)×Fin (arity e)):List Bool:=
  ((Fld.source n F a arity owner).placements.map SemiprimeD1PacketInventory.Placement.edge).getD
    ((SemiprimeD1CollisionOriginal.ports n F a arity).idxOf port) []
/-- The raw edge code is precisely the actual acquired byte field at each real typed pair. -/
theorem edgeFor_pair (n F a:Nat) (arity:Fin F→Nat) (owner:((e:Fin F)×Fin (arity e))→Fin n)
    (p:((e:Fin F)×Fin (arity e))×SemiprimeD1PacketInventory.Placement)
    (hp:p∈Pair.paired n F a arity owner):edgeFor n F a arity owner p.1=p.2.edge:=
  lookup_zip _ _ _ (Native.original_ports_nodup n F a arity) p hp
/-- Every original typed port has its actual physical pair; no choice enters the runtime source. -/
theorem pair_for (n F a:Nat) (arity:Fin F→Nat) (owner:((e:Fin F)×Fin (arity e))→Fin n)
    (port:(e:Fin F)×Fin (arity e)):
    ∃out,(port,out)∈Pair.paired n F a arity owner:=by
  have hl:=congrArg List.length (SemiprimeD1PacketReplayOriginal.sources n F 64 a arity owner)
  rw [List.length_map,SemiprimeD1IncidenceAcquisition.keys_original,List.length_map] at hl
  exact exists_zip_right _ _ hl.symm port (Native.original_ports_complete n F a arity port)
/-- Actual edge-ID acquisition gives an injective original port codec, proved using its real first-match bank. -/
theorem edgeFor_injective (n F a:Nat) (arity:Fin F→Nat) (owner:((e:Fin F)×Fin (arity e))→Fin n)
    (q:Fin a) (g:Fin 64):Function.Injective (edgeFor n F a arity owner):=by
  intro left right he
  obtain ⟨lo,hlo⟩:=pair_for n F a arity owner left
  obtain ⟨ro,hro⟩:=pair_for n F a arity owner right
  have hl:=edgeFor_pair n F a arity owner (left,lo) hlo
  have hr:=edgeFor_pair n F a arity owner (right,ro) hro
  have heq:lo.edge=ro.edge:=hl.symm.trans (he.trans hr)
  let data:=SemiprimeD1ChildPortPullback.acquire n F 64 a arity owner q g
  have hmleft:(lo.edge,left)∈data.ids:=by
    rw [Native.ids_value]
    exact List.mem_map.mpr ⟨(left,lo),hlo,rfl⟩
  have hmright:(ro.edge,right)∈data.ids:=by
    rw [Native.ids_value]
    exact List.mem_map.mpr ⟨(right,ro),hro,rfl⟩
  have hfindleft:=Native.findPort_member data.ids (Native.ids_nodup n F 64 a arity owner q g) lo.edge left hmleft
  have hfindright:=Native.findPort_member data.ids (Native.ids_nodup n F 64 a arity owner q g) ro.edge right hmright
  rw [heq,hfindright] at hfindleft
  exact Option.some.inj hfindleft.symm
/-- Exact edge-plus-side field key, before the source's later physical TRUE sentinel. -/
def rawTag (n F a:Nat) (arity:Fin F→Nat) (owner:((e:Fin F)×Fin (arity e))→Fin n)
    (tag:((e:Fin F)×Fin (arity e))×Bool):List Bool:=
  SemiprimeSourceHistogramKeyBits.frame (edgeFor n F a arity owner tag.1) [tag.2]
/-- Sentinel-protected raw equality is injective on ALL original typed ports and sides. -/
theorem rawTag_injective (n F a:Nat) (arity:Fin F→Nat) (owner:((e:Fin F)×Fin (arity e))→Fin n)
    (q:Fin a) (g:Fin 64):Function.Injective (rawTag n F a arity owner):=by
  intro left right h
  have hs:=SemiprimeSourceHistogramKeyBits.frame_injective _ _ _ _ h
  exact Prod.ext (edgeFor_injective n F a arity owner q g hs.1) (List.cons.inj hs.2).1
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryNativeTags
