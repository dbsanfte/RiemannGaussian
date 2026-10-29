/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PacketSourceValues

/-! # Original global source-value vector
Each original catalogue coordinate is evaluated at the reconstructed source
form of its actual packet and computed source group. High absent indices are
zero. No external mode-owner or source-value function is supplied.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace RiemannGaussian.SemiprimeD1PacketSourceVector
open SemiprimeD1PacketEntryInputs SemiprimeD1PacketSourceValues SemiprimeD1PacketGlobalRowForm
open SemiprimeD1ChildGraph SemiprimeD1JetAxes SemiprimeD1JetInterpretation
open SemiprimeD1ModeCatalog
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Source value reconstructed from the literal flattened original mode label. -/
def modeBase (ctx : Context) (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (i : Fin a)
    (assignment : Endpoint (n+F)→Bool) (mode : Mode) : Carrier ctx :=
  if hp : mode.slot/2^(i.val+1)<
      (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets.length then
    sourceForm ctx n F r a arity owner ⟨mode.slot/2^(i.val+1),hp⟩ i assignment
      ⟨mode.slot%2^(i.val+1),Nat.mod_lt _ (by positivity)⟩ mode.order
  else 0

/-- Total original global vector, in the literal acquired catalogue order. -/
def values (ctx : Context) (n F r a P : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (i : Fin a)
    (assignment : Endpoint (n+F)→Bool) (j : ℕ) : Carrier ctx :=
  match (SemiprimeD1GlobalModeOwners.modes n F r a P arity owner i)[j]? with
  | none => 0
  | some mode => modeBase ctx n F r a arity owner i assignment mode

/-- Exact flattened-slot source form at every original order/packet/tile grid
position. No enumeration or source-form certificate is a premise. -/
theorem modeBase_grid (ctx : Context) (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (i : Fin a)
    (assignment : Endpoint (n+F)→Bool)
    (packet : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets.length)
    (tile : Fin (2^(i.val+1))) (b : ℕ) :
    modeBase ctx n F r a arity owner i assignment ⟨tile.val+2^(i.val+1)*packet.val,b⟩=
      sourceForm ctx n F r a arity owner packet i assignment tile b := by
  have hd : (tile.val+2^(i.val+1)*packet.val)/2^(i.val+1)=packet.val := by
    rw [Nat.add_mul_div_left _ _ (by positivity),Nat.div_eq_of_lt tile.isLt,Nat.zero_add]
  have hm : (tile.val+2^(i.val+1)*packet.val)%2^(i.val+1)=tile.val := by
    rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt tile.isLt]
  unfold modeBase
  simp only [hd,packet.isLt,dite_true,hm]

/-- At every actual catalogue index, the global vector is exactly the source
form at its computed original packet/source owner, not an advised L value. -/
theorem values_owner (ctx : Context) (n F r a P : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (i : Fin a)
    (assignment : Endpoint (n+F)→Bool)
    (j : Fin (SemiprimeD1GlobalModeOwners.modes n F r a P arity owner i).length) :
    values ctx n F r a P arity owner i assignment j.val=
      SemiprimeD1PacketSourceAlignment.tilePower ctx a i
        (columnsOf n F r a arity owner i
          (SemiprimeD1GlobalModeOwners.packet n F r a P arity owner i j) assignment
          (SemiprimeD1GlobalModeOwners.source n F r a P arity owner i j))
        (SemiprimeD1GlobalModeOwners.tile n F r a P arity owner i j).val
        (SemiprimeD1GlobalModeOwners.mode n F r a P arity owner i j).order := by
  unfold values
  rw [List.getElem?_eq_getElem j.isLt]
  dsimp only
  unfold modeBase
  have hp := (SemiprimeD1GlobalModeOwners.packet n F r a P arity owner i j).isLt
  change (SemiprimeD1GlobalModeOwners.modes n F r a P arity owner i)[j.val].slot/2^(i.val+1)<
    (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets.length at hp
  simp only [hp,dite_true]
  rfl

end
end RiemannGaussian.SemiprimeD1PacketSourceVector
