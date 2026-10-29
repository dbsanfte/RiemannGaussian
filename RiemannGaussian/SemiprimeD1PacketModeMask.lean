/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ModeRoutingOriginal
import RiemannGaussian.SemiprimeD1OriginalModeAcquisition
import RiemannGaussian.SemiprimeD1JetAffineCoefficient

/-! # Actual packet-local target/source mode masks
The global acquired catalogue is preserved in its original order. Each mode is
classified by its literal flattened packet/tile index and the physical routing
colours. Requested target coefficients are restricted to this packet before
affine coefficient extraction; unrelated positive exponents are not queried.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace RiemannGaussian.SemiprimeD1PacketModeMask
open SemiprimeD1ModeCatalog SemiprimeMaterializedWords

/-- One original global mode with actually acquired local routing flags. -/
structure Item where
  /-- Unchanged global catalogue label. -/
  mode : Mode
  /-- Literal tile ordinal from the flattened original slot. -/
  tile : ℕ
  /-- Whether this mode belongs to the requested observed packet. -/
  inPacket : Bool
  /-- Physical target colour equals the requested child group. -/
  targetHere : Bool
  /-- Physical source colour equals the requested child group. -/
  sourceHere : Bool
  /-- Both colour reads/comparisons and every routing report. -/
  clock : ℕ
  deriving Repr

/-- Classify one literal mode, acquiring no route for an unrelated packet. -/
def acquireOne {n F a : ℕ} {arity : Fin F→ℕ}
    (source : SemiprimeD1PacketReplayOriginal.Acquired n F a arity)
    (packet : Fin source.state.packets.length) (i : Fin a) (group : List Bool) (mode : Mode) : Item :=
  let tiles := 2^(i.val+1)
  let tile : Fin tiles := ⟨mode.slot%tiles,Nat.mod_lt _ (by positivity)⟩
  if mode.slot/tiles=packet.val then
    let key := SemiprimeSourceCompactBits.copy source.state.packets[packet.val]
    let route := SemiprimeD1ModeRoutingBits.acquire key.bits a i tile
    let target := SemiprimeD1ChildGraph.equalBytes route.target group
    let origin := SemiprimeD1ChildGraph.equalBytes route.source group
    ⟨mode,tile.val,true,target.value,origin.value,
      key.clock+route.clock+target.work+origin.work+packet.val+mode.slot+tiles+9⟩
  else ⟨mode,tile.val,false,false,false,mode.slot+tiles+5⟩

/-- Actual in-packet flags are exactly the two physical route-byte comparisons. -/
theorem acquireOne_here {n F a : ℕ} {arity : Fin F→ℕ}
    (source : SemiprimeD1PacketReplayOriginal.Acquired n F a arity)
    (packet : Fin source.state.packets.length) (i : Fin a) (group : List Bool) (mode : Mode)
    (h : mode.slot/2^(i.val+1)=packet.val) :
    let tile : Fin (2^(i.val+1)) := ⟨mode.slot%2^(i.val+1),Nat.mod_lt _ (by positivity)⟩
    let route := SemiprimeD1ModeRoutingBits.acquire source.state.packets[packet.val] a i tile
    (acquireOne source packet i group mode).inPacket=true ∧
      ((acquireOne source packet i group mode).targetHere=true ↔ route.target=group) ∧
      ((acquireOne source packet i group mode).sourceHere=true ↔ route.source=group) := by
  dsimp only [acquireOne]
  rw [h]
  simp only [ite_true,SemiprimeSourceCompactBits.copy_bits]
  exact ⟨True.intro,SemiprimeD1ChildGraph.equalBytes_correct _ _,SemiprimeD1ChildGraph.equalBytes_correct _ _⟩

/-- A concrete descriptor cache, with no semantic Word fields or mode owner oracle. -/
structure Cache where
  /-- Original global catalogue order, with physical classification data. -/
  items : List Item
  /-- All catalogue, routing, encoded group and descriptor allocation reports. -/
  clock : ℕ

/-- Cache actual descriptors in catalogue order, retaining every producer report. -/
def scan {n F a : ℕ} {arity : Fin F→ℕ}
    (source : SemiprimeD1PacketReplayOriginal.Acquired n F a arity)
    (packet : Fin source.state.packets.length) (i : Fin a) (group : List Bool) : List Mode→Cache
  | [] => ⟨[],1⟩
  | mode::modes =>
    let item := acquireOne source packet i group mode
    let tail := scan source packet i group modes
    ⟨item::tail.items,item.clock+tail.clock+4⟩

/-- The cache contains exactly the actually executed classifiers in original order. -/
theorem scan_items {n F a : ℕ} {arity : Fin F→ℕ}
    (source : SemiprimeD1PacketReplayOriginal.Acquired n F a arity)
    (packet : Fin source.state.packets.length) (i : Fin a) (group : List Bool) (modes : List Mode) :
    (scan source packet i group modes).items=modes.map (acquireOne source packet i group) := by
  induction modes with
  | nil => rfl
  | cons mode modes ih => simp only [scan,ih,List.map_cons]

/-- Acquire the complete actual catalogue and classify it from retained original packets. -/
def fromModes {n F r a : ℕ} {arity : Fin F→ℕ}
    (source : SemiprimeD1OriginalModeAcquisition.Acquired n F a arity)
    (packet : Fin source.packets.state.packets.length) (i : Fin a) (g : Fin r) : Cache :=
  let group := SemiprimeSourceHistogramPortKeys.encodeKey g.val
  let catalogue := acquireCatalog (source.packets.state.packets.length*2^(i.val+1)) (source.precision-1)
  let out := scan source.packets packet i group.bits catalogue.value
  ⟨out.items,source.work+group.clock+catalogue.work+out.clock+8⟩

/-- Unrelated packet modes never enter either local mask. -/
theorem acquireOne_other {n F a : ℕ} {arity : Fin F→ℕ}
    (source : SemiprimeD1PacketReplayOriginal.Acquired n F a arity)
    (packet : Fin source.state.packets.length) (i : Fin a) (group : List Bool) (mode : Mode)
    (h : mode.slot/2^(i.val+1)≠packet.val) :
    (acquireOne source packet i group mode).inPacket=false ∧
    (acquireOne source packet i group mode).targetHere=false ∧
    (acquireOne source packet i group mode).sourceHere=false := by
  simp only [acquireOne,h,ite_false]
  exact ⟨True.intro,True.intro,True.intro⟩

/-- Classifying a mode preserves its actual global label. -/
theorem acquireOne_mode {n F a : ℕ} {arity : Fin F→ℕ}
    (source : SemiprimeD1PacketReplayOriginal.Acquired n F a arity)
    (packet : Fin source.state.packets.length) (i : Fin a) (group : List Bool) (mode : Mode) :
    (acquireOne source packet i group mode).mode=mode := by
  dsimp only [acquireOne]
  split_ifs <;> rfl

/-- The acquired descriptor vector preserves every global mode and its multiplicity. -/
theorem scan_modes {n F a : ℕ} {arity : Fin F→ℕ}
    (source : SemiprimeD1PacketReplayOriginal.Acquired n F a arity)
    (packet : Fin source.state.packets.length) (i : Fin a) (group : List Bool) (modes : List Mode) :
    ((scan source packet i group modes).items.map Item.mode)=modes := by
  induction modes with
  | nil => rfl
  | cons mode modes ih => simp only [scan,List.map_cons,acquireOne_mode,ih]

/-- The actual descriptor cache is the acquired original catalogue, not an advised subset. -/
theorem fromModes_catalogue {n F r a : ℕ} {arity : Fin F→ℕ}
    (source : SemiprimeD1OriginalModeAcquisition.Acquired n F a arity)
    (packet : Fin source.packets.state.packets.length) (i : Fin a) (g : Fin r) :
    (fromModes source packet i g).items.map Item.mode=
      catalog (source.packets.state.packets.length*2^(i.val+1)) (source.precision-1) := by
  rw [fromModes,scan_modes,acquireCatalog_value]

/-- Chronological native exponent read and target-mask application. -/
def restrictFrom (beta : List ℕ) : List Item→ℕ→Run (List ℕ)
  | [],_ => ⟨[],1⟩
  | item::items,index =>
    let exponent := SemiprimeD1AffineCoefficient.read 0 beta index
    let tail := restrictFrom beta items (index+1)
    let value := if item.inPacket && item.targetHere then exponent.1 else 0
    ⟨value::tail.value,exponent.2+tail.work+5⟩

/-- Restrict the coefficient QUERY; source powers continue to use the original beta. -/
def restrict (cache : Cache) (beta : List ℕ) : Run (List ℕ) := restrictFrom beta cache.items 0

/-- Every original descriptor has a query slot, including a literal zero outside the mask. -/
theorem restrictFrom_length (beta : List ℕ) (items : List Item) (index : ℕ) :
    (restrictFrom beta items index).value.length=items.length := by
  induction items generalizing index with
  | nil => rfl
  | cons item items ih => simp only [restrictFrom,List.length_cons,ih]

/-- Exact original-order coefficient restriction, with no positive outside-packet query. -/
theorem restrictFrom_value (beta : List ℕ) (items : List Item) (index : ℕ) :
    (restrictFrom beta items index).value=
      (items.zipIdx index).map (fun entry => if entry.1.inPacket && entry.1.targetHere then
        (beta[entry.2]?).getD 0 else 0) := by
  induction items generalizing index with
  | nil => rfl
  | cons item items ih =>
    simp only [restrictFrom,SemiprimeD1AffineCoefficient.read_value,ih,List.zipIdx_cons,List.map_cons]
    rfl

end RiemannGaussian.SemiprimeD1PacketModeMask
