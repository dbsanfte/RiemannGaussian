/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PacketSourceAlignment

/-! # Original D.12 expanded over the literal real-column list
The arithmetic source form is reconstructed from actual column bits and slots.
All list occurrences, including parallel columns, are preserved. This is the
row-form expansion seam, not a global D.16 contraction assertion.
-/
set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace RiemannGaussian.SemiprimeD1PacketRowExpansion
open scoped BigOperators
open SemiprimeD1PacketEntryInputs SemiprimeD1PacketEntryBits
open SemiprimeD1PacketSourceAlignment SemiprimeD1JetAxes SemiprimeD1JetInterpretation
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The original residue tile embedded in the full packet slot type. -/
def liftTile (a : ℕ) (i : Fin a) (tile : Fin (2^(i.val+1))) : Fin (2^a) :=
  ⟨tile.val,tile.isLt.trans_le (Nat.pow_le_pow_right (by omega) (by omega))⟩

/-- Actual original mode value at the arithmetic tile used by the source form. -/
def modeValue (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (a : ℕ) (i : Fin a) (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (row : Wire a) (tile : Fin (2^(i.val+1))) (b : ℕ) : Carrier ctx :=
  SemiprimeD1UniversalModeData.evaluate ctx.precision
    (SemiprimeD1JetAlgebra.constants (SemiprimeD1JetBoxIndex.dims ctx.axes)) (interpret ctx z.words)
    (SemiprimeD1UniversalModeData.acquireOriginal ctx.precision a i.val b t row.slot (liftTile a i tile))

/-- A literal column contributes precisely when its bit is on and its slot is
in this tile. No table of source terms is supplied. -/
def columnPower (ctx : Context) (a : ℕ) (i : Fin a) (tile : Fin (2^(i.val+1)))
    (column : Wire a) (b : ℕ) : Carrier ctx :=
  if column.bit && (column.slot.val%2^(i.val+1) == tile.val) then
    (SemiprimeD1JetAlgebra.constants (SemiprimeD1JetBoxIndex.dims ctx.axes)
      ((column.slot.val/2^(i.val+1):ℕ):ZMod (2^ctx.precision)))^b else 0

/-- The actual kernel contribution in one arithmetic tile. -/
def columnEntry (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (a : ℕ) (i : Fin a) (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (row : Wire a) (tile : Fin (2^(i.val+1))) (column : Wire a) : Carrier ctx :=
  if column.bit && (column.slot.val%2^(i.val+1) == tile.val) then
    SemiprimeD1UniversalModeData.entryValue ctx.precision
      (SemiprimeD1JetAlgebra.constants (SemiprimeD1JetBoxIndex.dims ctx.axes)) (interpret ctx z.words)
      (SemiprimeD1WireKernelOriginal.acquireOriginal a t row.slot column.slot) else 0

/-- Source forms are sums of the exact same column powers appearing in D.12. -/
theorem tilePower_columns (ctx : Context) (a : ℕ) (i : Fin a)
    (tile : Fin (2^(i.val+1))) (columns : List (Wire a)) (b : ℕ) :
    tilePower ctx a i columns tile.val b=(columns.map (fun column => columnPower ctx a i tile column b)).sum := by
  induction columns with
  | nil => rfl
  | cons column columns ih =>
    unfold tilePower at *
    by_cases h : (column.bit && (column.slot.val%2^(i.val+1) == tile.val))=true
    · simpa only [List.filter_cons,h,ite_true,List.map_cons,List.sum_cons,columnPower] using
        congrArg (fun tail => (SemiprimeD1JetAlgebra.constants (SemiprimeD1JetBoxIndex.dims ctx.axes)
          ((column.slot.val/2^(i.val+1):ℕ):ZMod (2^ctx.precision)))^b+tail) ih
    · simpa only [List.filter_cons,h,Bool.false_eq_true,ite_false,List.map_cons,List.sum_cons,columnPower,zero_add] using ih

/-- One original D.12 identity with its displacement reconstructed from the
actual column slot. The same-bit condition is a physical test value. -/
theorem column_D12 (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (a : ℕ) (i : Fin a) (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (row : Wire a) (tile : Fin (2^(i.val+1))) (column : Wire a)
    (hp : 0<ctx.precision) (ht : SemiprimeD1WireKernelOriginal.point a t.val≠0)
    (hi : padicValInt 2 (SemiprimeD1WireKernelOriginal.point a t.val)=i.val)
    (hbit : (sameBit row.slot.val tile.val i.val).value=true) :
    columnEntry ctx z a i t row tile column=
      ∑ b∈Finset.range (ctx.precision-1), modeValue ctx z a i t row tile b*columnPower ctx a i tile column b := by
  by_cases h : (column.bit && (column.slot.val%2^(i.val+1) == tile.val))=true
  · have hc : column.slot.val%2^(i.val+1)=tile.val :=
      beq_iff_eq.mp (Bool.and_eq_true_iff.mp h).2
    have hb : row.slot.val.testBit i.val=tile.val.testBit i.val := by
      rw [sameBit_value] at hbit
      exact beq_iff_eq.mp hbit
    have hy : column.slot.val=(liftTile a i tile).val+2^(i.val+1)*(column.slot.val/2^(i.val+1)) := by
      change column.slot.val=tile.val+2^(i.val+1)*(column.slot.val/2^(i.val+1))
      rw [←hc]
      exact (Nat.mod_add_div _ _).symm
    simpa only [columnEntry,columnPower,h,ite_true,modeValue,map_pow] using
      SemiprimeD1UniversalModeData.original_D12 ctx.precision a i.val
        (column.slot.val/2^(i.val+1))
        (SemiprimeD1JetAlgebra.constants (SemiprimeD1JetBoxIndex.dims ctx.axes)) (interpret ctx z.words)
        t row.slot (liftTile a i tile) column.slot ht hi i.isLt hb hy hp
  · simp only [columnEntry,columnPower,h,Bool.false_eq_true,ite_false,mul_zero,Finset.sum_const_zero]

/-- Full evaluated real-row source-tile expansion. This is the literal column
list, not a deduplicated set or an advised source linear form. -/
theorem row_tile_D12 (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (a : ℕ) (i : Fin a) (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (row : Wire a) (tile : Fin (2^(i.val+1))) (columns : List (Wire a))
    (hp : 0<ctx.precision) (ht : SemiprimeD1WireKernelOriginal.point a t.val≠0)
    (hi : padicValInt 2 (SemiprimeD1WireKernelOriginal.point a t.val)=i.val)
    (hbit : (sameBit row.slot.val tile.val i.val).value=true) :
    (columns.map (columnEntry ctx z a i t row tile)).sum=
      ∑ b∈Finset.range (ctx.precision-1), modeValue ctx z a i t row tile b*
        tilePower ctx a i columns tile.val b := by
  simp_rw [tilePower_columns]
  induction columns with
  | nil => simp only [List.map_nil,List.sum_nil,mul_zero,Finset.sum_const_zero]
  | cons column columns ih =>
    simp only [List.map_cons,List.sum_cons]
    rw [column_D12 ctx z a i t row tile column hp ht hi hbit,ih,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b _
    exact (mul_add _ _ _).symm

/-- On every actual crossing real row, original replay routing proves the bit
condition required by the whole source-tile expansion. No same-bit certificate,
row-origin witness or arbitrary row value is passed by the original caller. -/
theorem original_row_tile_D12 (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (packet : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets.length)
    (i : Fin a) (g : Fin r) (tile : Fin (2^(i.val+1)))
    (endpoint : SemiprimeD1ChildGraph.Endpoint (n+F))
    (he : endpoint∈((SemiprimeD1ChildGraph.acquire n F r a arity owner i g).factors[packet.val]?).getD [])
    (hside : endpoint.side=true)
    (hsource : (SemiprimeD1ModeRoutingBits.acquire
      (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets[packet.val] a i tile).source≠
        (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits)
    (bit : Bool) (columns : List (Wire a)) (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (hp : 0<ctx.precision) (ht : SemiprimeD1WireKernelOriginal.point a t.val≠0)
    (hi : padicValInt 2 (SemiprimeD1WireKernelOriginal.point a t.val)=i.val) :
    let row := (SemiprimeD1PacketEntryInputs.wire a endpoint bit).1
    (columns.map (columnEntry ctx z a i t row tile)).sum=
      ∑ b∈Finset.range (ctx.precision-1), modeValue ctx z a i t row tile b*
        tilePower ctx a i columns tile.val b := by
  exact row_tile_D12 ctx z a i t _ tile columns hp ht hi
    (SemiprimeD1PacketModeOriginal.row_test_true n F r a arity owner packet i g tile
      endpoint he hside hsource bit)

end
end RiemannGaussian.SemiprimeD1PacketRowExpansion
