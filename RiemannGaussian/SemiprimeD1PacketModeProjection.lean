/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PacketModeMask
import RiemannGaussian.SemiprimeD1SeparatedCoefficient

/-! # Computed packet query equals the actual erased mode projection
The subset is read from the acquired descriptor list, with false outside its
actual finite range. There is no supplied restricted exponent or mode owner.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace RiemannGaussian.SemiprimeD1PacketModeProjection
open SemiprimeD1PacketModeMask

/-- Actual target-query flag, false beyond the acquired catalogue. -/
def targetEnabled (items : List Item) (j : ℕ) : Bool :=
  match items[j]? with
  | none => false
  | some item => item.inPacket && item.targetHere

/-- Actual source-factor flag, false beyond the acquired catalogue. -/
def sourceEnabled (items : List Item) (j : ℕ) : Bool :=
  match items[j]? with
  | none => false
  | some item => item.inPacket && item.sourceHere

/-- Exact pointwise value of the executed exponent scan, including all high zero slots. -/
theorem restrictFrom_getD (beta : List ℕ) (items : List Item) (start j : ℕ) :
    (restrictFrom beta items start).value.getD j 0=
      if targetEnabled items j then beta.getD (start+j) 0 else 0 := by
  induction items generalizing start j with
  | nil => simp [restrictFrom,targetEnabled]
  | cons item items ih =>
    cases j with
    | zero =>
      simp only [restrictFrom,List.getD_cons_zero,targetEnabled,List.getElem?_cons_zero,
        SemiprimeD1AffineCoefficient.read_value,Nat.add_zero]
      rfl
    | succ j =>
      simp only [restrictFrom,List.getD_cons_succ,targetEnabled,List.getElem?_cons_succ]
      rw [ih]
      simp only [targetEnabled]
      congr 2
      omega

/-- Concrete acquired target-index set; not a supplied semantic ownership predicate. -/
def targetSet (cache : Cache) : Set ℕ := {j | targetEnabled cache.items j=true}

/-- Concrete acquired source-index set used by the original-beta product. -/
def sourceSet (cache : Cache) : Set ℕ := {j | sourceEnabled cache.items j=true}

/-- The ACTUALLY computed query vector is exactly the erased coefficient restriction.
No length advice is needed: the acquired mask is false beyond its own finite range. -/
theorem restrict_toFinsupp (cache : Cache) (beta : List ℕ) :
    (restrict cache beta).value.toFinsupp=
      SemiprimeD1SeparatedCoefficient.restrict (targetSet cache) beta.toFinsupp := by
  ext j
  rw [List.toFinsupp_apply,SemiprimeD1SeparatedCoefficient.restrict_apply,List.toFinsupp_apply]
  have hh := restrictFrom_getD beta cache.items 0 j
  by_cases h : targetEnabled cache.items j=true
  · simpa only [restrict,targetSet,Set.mem_ofPred_eq,Nat.zero_add,h,ite_true] using hh
  · simpa only [restrict,targetSet,Set.mem_ofPred_eq,Nat.zero_add,h,ite_false] using hh

/-- Every target mask index is an actual acquired catalogue index. -/
theorem targetSet_lt (cache : Cache) (j : ℕ) (hj : j∈targetSet cache) : j<cache.items.length := by
  by_contra hn
  have h := List.getElem?_eq_none_iff.mpr (by omega : cache.items.length≤j)
  simp only [targetSet,Set.mem_ofPred_eq,targetEnabled,h,Bool.false_eq_true] at hj

/-- Every source mask index is an actual acquired catalogue index. -/
theorem sourceSet_lt (cache : Cache) (j : ℕ) (hj : j∈sourceSet cache) : j<cache.items.length := by
  by_contra hn
  have h := List.getElem?_eq_none_iff.mpr (by omega : cache.items.length≤j)
  simp only [sourceSet,Set.mem_ofPred_eq,sourceEnabled,h,Bool.false_eq_true] at hj

/-- An acquired target flag is the actual packet test plus physical routed target equality. -/
theorem scan_target {n F a : ℕ} {arity : Fin F→ℕ}
    (source : SemiprimeD1PacketReplayOriginal.Acquired n F a arity)
    (packet : Fin source.state.packets.length) (i : Fin a) (group : List Bool)
    (modes : List SemiprimeD1ModeCatalog.Mode) (j : Fin modes.length) :
    targetEnabled (scan source packet i group modes).items j.val=true ↔
      let mode := modes[j.val]
      let tile : Fin (2^(i.val+1)) := ⟨mode.slot%2^(i.val+1),Nat.mod_lt _ (by positivity)⟩
      mode.slot/2^(i.val+1)=packet.val ∧
        (SemiprimeD1ModeRoutingBits.acquire source.state.packets[packet.val] a i tile).target=group := by
  rw [scan_items]
  simp only [targetEnabled,List.getElem?_map,List.getElem?_eq_getElem j.isLt,Option.map_some]
  by_cases h : modes[j.val].slot/2^(i.val+1)=packet.val
  · have hh := acquireOne_here source packet i group modes[j.val] h
    dsimp only at hh
    rw [hh.1]
    simp only [Bool.true_and,h,true_and,hh.2.1]
  · have hh := acquireOne_other source packet i group modes[j.val] h
    rw [hh.1]
    simp only [Bool.false_and,Bool.false_eq_true,h,false_and]

/-- An acquired source flag uses exactly the original physical source colour. -/
theorem scan_source {n F a : ℕ} {arity : Fin F→ℕ}
    (source : SemiprimeD1PacketReplayOriginal.Acquired n F a arity)
    (packet : Fin source.state.packets.length) (i : Fin a) (group : List Bool)
    (modes : List SemiprimeD1ModeCatalog.Mode) (j : Fin modes.length) :
    sourceEnabled (scan source packet i group modes).items j.val=true ↔
      let mode := modes[j.val]
      let tile : Fin (2^(i.val+1)) := ⟨mode.slot%2^(i.val+1),Nat.mod_lt _ (by positivity)⟩
      mode.slot/2^(i.val+1)=packet.val ∧
        (SemiprimeD1ModeRoutingBits.acquire source.state.packets[packet.val] a i tile).source=group := by
  rw [scan_items]
  simp only [sourceEnabled,List.getElem?_map,List.getElem?_eq_getElem j.isLt,Option.map_some]
  by_cases h : modes[j.val].slot/2^(i.val+1)=packet.val
  · have hh := acquireOne_here source packet i group modes[j.val] h
    dsimp only at hh
    rw [hh.1]
    simp only [Bool.true_and,h,true_and,hh.2.2]
  · have hh := acquireOne_other source packet i group modes[j.val] h
    rw [hh.1]
    simp only [Bool.false_and,Bool.false_eq_true,h,false_and]

/-- Original-source target projection is tied to the actual acquired catalogue and route. -/
theorem original_target {n F r a : ℕ} {arity : Fin F→ℕ}
    (source : SemiprimeD1OriginalModeAcquisition.Acquired n F a arity)
    (packet : Fin source.packets.state.packets.length) (i : Fin a) (g : Fin r)
    (j : Fin (SemiprimeD1ModeCatalog.catalog
      (source.packets.state.packets.length*2^(i.val+1)) (source.precision-1)).length) :
    j.val∈targetSet (fromModes source packet i g) ↔
      let modes := SemiprimeD1ModeCatalog.catalog
        (source.packets.state.packets.length*2^(i.val+1)) (source.precision-1)
      let mode := modes[j.val]
      let tile : Fin (2^(i.val+1)) := ⟨mode.slot%2^(i.val+1),Nat.mod_lt _ (by positivity)⟩
      mode.slot/2^(i.val+1)=packet.val ∧
        (SemiprimeD1ModeRoutingBits.acquire source.packets.state.packets[packet.val] a i tile).target=
          (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits := by
  change targetEnabled (scan source.packets packet i _
    (SemiprimeD1ModeCatalog.acquireCatalog _ _).value).items j.val=true ↔ _
  rw [SemiprimeD1ModeCatalog.acquireCatalog_value]
  exact scan_target source.packets packet i _ _ j

/-- Original-source source-power mask is tied to the same actual mode route. -/
theorem original_source {n F r a : ℕ} {arity : Fin F→ℕ}
    (source : SemiprimeD1OriginalModeAcquisition.Acquired n F a arity)
    (packet : Fin source.packets.state.packets.length) (i : Fin a) (g : Fin r)
    (j : Fin (SemiprimeD1ModeCatalog.catalog
      (source.packets.state.packets.length*2^(i.val+1)) (source.precision-1)).length) :
    j.val∈sourceSet (fromModes source packet i g) ↔
      let modes := SemiprimeD1ModeCatalog.catalog
        (source.packets.state.packets.length*2^(i.val+1)) (source.precision-1)
      let mode := modes[j.val]
      let tile : Fin (2^(i.val+1)) := ⟨mode.slot%2^(i.val+1),Nat.mod_lt _ (by positivity)⟩
      mode.slot/2^(i.val+1)=packet.val ∧
        (SemiprimeD1ModeRoutingBits.acquire source.packets.state.packets[packet.val] a i tile).source=
          (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits := by
  change sourceEnabled (scan source.packets packet i _
    (SemiprimeD1ModeCatalog.acquireCatalog _ _).value).items j.val=true ↔ _
  rw [SemiprimeD1ModeCatalog.acquireCatalog_value]
  exact scan_source source.packets packet i _ _ j

end RiemannGaussian.SemiprimeD1PacketModeProjection
