/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PacketModeProjection

/-! # Unique source and target owners read from actual global mode routes
The owners used in the erased mode-separation proof are determined by actual
mode slots and acquired route bytes. No chosen projection or supplied colour
function occurs. These are proof-side views of the existing acquired metadata,
not a second catalogue-acquisition stage asserted free at runtime.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace RiemannGaussian.SemiprimeD1GlobalModeOwners
open SemiprimeBitArithmetic
open SemiprimeD1ModeCatalog SemiprimeD1PacketModeProjection

/-- Exact original sparse source whose route palette is already proved. -/
abbrev original (n F r a : ℕ) (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) :=
  SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner

/-- The literal GLOBAL finite catalogue, before any packet/group restriction. -/
def modes (n F r a P : ℕ) (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (i : Fin a) : List Mode :=
  catalog ((original n F r a arity owner).state.packets.length*2^(i.val+1)) P

/-- Read the actual global catalogue label at its finite acquired position. -/
def mode (n F r a P : ℕ) (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (i : Fin a)
    (j : Fin (modes n F r a P arity owner i).length) : Mode :=
  (modes n F r a P arity owner i)[j.val]

/-- The acquired mode's packet index comes from its actual slot quotient. -/
def packet (n F r a P : ℕ) (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (i : Fin a)
    (j : Fin (modes n F r a P arity owner i).length) :
    Fin (original n F r a arity owner).state.packets.length :=
  ⟨(mode n F r a P arity owner i j).slot/2^(i.val+1), by
    have hm := (mem_catalog _ _ _).mp (List.getElem_mem j.isLt)
    exact (Nat.div_lt_iff_lt_mul (show 0 < (2:ℕ)^(i.val+1) by positivity)).mpr hm.1⟩

/-- The acquired mode's tile index is its actual slot remainder. -/
def tile (n F r a P : ℕ) (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (i : Fin a)
    (j : Fin (modes n F r a P arity owner i).length) : Fin (2^(i.val+1)) :=
  ⟨(mode n F r a P arity owner i j).slot%2^(i.val+1), Nat.mod_lt _ (by positivity)⟩

/-- Actual original route for this global acquired mode index. -/
def route (n F r a P : ℕ) (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (i : Fin a)
    (j : Fin (modes n F r a P arity owner i).length) :=
  SemiprimeD1ModeRoutingBits.fromReplay (original n F r a arity owner)
    (packet n F r a P arity owner i j) i (tile n F r a P arity owner i j)

/-- Unique actual target group, with the palette bound derived from original rows. -/
def target (n F r a P : ℕ) [NeZero r] (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (i : Fin a)
    (j : Fin (modes n F r a P arity owner i).length) : Fin r :=
  ⟨bitValue (route n F r a P arity owner i j).target,
    (SemiprimeD1ModeRoutingOriginal.route_palette n F r a arity owner
      (packet n F r a P arity owner i j) i (tile n F r a P arity owner i j)).2.2.2⟩

/-- Unique actual source group, with no colour function supplied as advice. -/
def source (n F r a P : ℕ) [NeZero r] (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (i : Fin a)
    (j : Fin (modes n F r a P arity owner i).length) : Fin r :=
  ⟨bitValue (route n F r a P arity owner i j).source,
    (SemiprimeD1ModeRoutingOriginal.route_palette n F r a arity owner
      (packet n F r a P arity owner i j) i (tile n F r a P arity owner i j)).2.1⟩

/-- Compact original route bytes equal an encoded group precisely at their actual value. -/
theorem target_bytes (n F r a P : ℕ) [NeZero r] (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (i : Fin a)
    (j : Fin (modes n F r a P arity owner i).length) (g : Fin r) :
    target n F r a P arity owner i j = g ↔
      (route n F r a P arity owner i j).target =
        (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits := by
  have hc := (SemiprimeD1ModeRoutingOriginal.route_palette n F r a arity owner
    (packet n F r a P arity owner i j) i (tile n F r a P arity owner i j)).2.2.1
  constructor
  · intro h
    apply SemiprimeSourceCompactWordIds.compact_value_injective _ _ hc
      (SemiprimeSourceHistogramPortKeys.encodeKey_compact g.val)
    rw [SemiprimeSourceHistogramPortKeys.encodeKey_value]
    exact congrArg Fin.val h
  · intro h
    apply Fin.ext
    change bitValue (route n F r a P arity owner i j).target = g.val
    rw [h, SemiprimeSourceHistogramPortKeys.encodeKey_value]

/-- The source owner is likewise exactly the actual compact source-route byte value. -/
theorem source_bytes (n F r a P : ℕ) [NeZero r] (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (i : Fin a)
    (j : Fin (modes n F r a P arity owner i).length) (g : Fin r) :
    source n F r a P arity owner i j = g ↔
      (route n F r a P arity owner i j).source =
        (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits := by
  have hc := (SemiprimeD1ModeRoutingOriginal.route_palette n F r a arity owner
    (packet n F r a P arity owner i j) i (tile n F r a P arity owner i j)).1
  constructor
  · intro h
    apply SemiprimeSourceCompactWordIds.compact_value_injective _ _ hc
      (SemiprimeSourceHistogramPortKeys.encodeKey_compact g.val)
    rw [SemiprimeSourceHistogramPortKeys.encodeKey_value]
    exact congrArg Fin.val h
  · intro h
    apply Fin.ext
    change bitValue (route n F r a P arity owner i j).source = g.val
    rw [h, SemiprimeSourceHistogramPortKeys.encodeKey_value]

end RiemannGaussian.SemiprimeD1GlobalModeOwners
