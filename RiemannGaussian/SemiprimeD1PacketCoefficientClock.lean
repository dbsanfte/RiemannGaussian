/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PacketArithmeticClock

/-! # Actual packet mode coefficients and cached affine row acquisition
All same-bit checks and actual signed crossing-mode calls are charged. Numeric
mode/tile caps describe acquired original catalogue fields, not supplied entry
values or intermediate width/clock answers.
-/
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1PacketCoefficientClock
open SemiprimeD1JetAxes SemiprimeD1JetAffineCoefficient SemiprimeD1JetAffineCoefficientBounds
open SemiprimeD1PacketEntryBits SemiprimeD1PacketEntryInputs SemiprimeD1PacketArithmeticClock

/-- Original physical index acquisition and both actual bit scans. -/
def sameBitClock (a : ℕ) : ℕ := 2*SemiprimeSourceHistogramPortKeys.encodeBudget (2^a)+8*a+9

/-- Same-bit control is computed, never assumed as a branch oracle. -/
theorem sameBit_clock (a : ℕ) (i : Fin a) (x y : Fin (2^a)) :
    (sameBit x.val y.val i.val).work ≤ sameBitClock a := by
  have hx := SemiprimeSourceHistogramPortKeys.encodeKey_clock x.val (2^a) x.isLt.le
  have hy := SemiprimeSourceHistogramPortKeys.encodeKey_clock y.val (2^a) y.isLt.le
  have hl := SemiprimeD1ModeRoutingBits.readBit_work
    (SemiprimeSourceHistogramPortKeys.encodeKey x.val).bits i.val
  have hr := SemiprimeD1ModeRoutingBits.readBit_work
    (SemiprimeSourceHistogramPortKeys.encodeKey y.val).bits i.val
  change (SemiprimeSourceHistogramPortKeys.encodeKey x.val).clock+
    (SemiprimeSourceHistogramPortKeys.encodeKey y.val).clock+_+_+5 ≤ _
  unfold sameBitClock
  omega

/-- Mode budget is monotone in the actual finite original mode exponent. -/
theorem mode_order_mono (ctx : Context) (a b B : ℕ) (hb : b ≤ B) :
    SemiprimeD1JetModeBitsBounds.modeBudget ctx ctx.precision (2^(a+1)*(a+1)) (2^(a+1)) b ≤
      SemiprimeD1JetModeBitsBounds.modeBudget ctx ctx.precision (2^(a+1)*(a+1)) (2^(a+1)) B := by
  unfold SemiprimeD1JetModeBitsBounds.modeBudget
  gcongr

/-- Whole crossing coefficient, including both zero and active physical branches. -/
def coefficientClock (ctx : Context) (a B T : ℕ) : ℕ :=
  SemiprimeD1JetModeBitsBounds.modeBudget ctx ctx.precision (2^(a+1)*(a+1)) (2^(a+1)) B+
    signClock ctx+sameBitClock a+T+2^a+2^a+10+ctx.rank+1

/-- Every actual catalogue coefficient derives canonical current shape. -/
theorem coefficient_good (ctx : Context) (z : JetRun) (a : ℕ) (i : Fin a)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (row : Wire a)
    (item : SemiprimeD1PacketModeMask.Item) : Good ctx (coefficient ctx z a i t row item).words := by
  dsimp only [coefficient]
  split
  · exact signed_good ctx _ _ (SemiprimeD1JetModeBitsBounds.mode_good ctx _ _ _ _ _ _ _)
  · exact zero_good ctx

/-- Whole actual physical coefficient cost from original acquired input bounds. -/
theorem coefficient_clock (ctx : Context) (z : JetRun) (hz : Good ctx z.words) (a : ℕ) (i : Fin a)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (row : Wire a)
    (item : SemiprimeD1PacketModeMask.Item) (B T : ℕ)
    (hb : item.mode.order ≤ B) (ht : item.tile ≤ T) :
    (coefficient ctx z a i t row item).clock ≤ coefficientClock ctx a B T := by
  let tile : Fin (2^a) := ⟨item.tile%2^a,Nat.mod_lt _ (by positivity)⟩
  have htest := sameBit_clock a i row.slot tile
  have hmode := SemiprimeD1JetModeBitsBounds.acquireOriginal_clock ctx (borrow z) a i.val
    item.mode.order t row.slot tile ctx.precision le_rfl hz.1.le hz.2
  have hmodeGood : Good ctx (SemiprimeD1JetModeBits.acquireOriginal ctx (borrow z) a i.val
      item.mode.order t row.slot tile).words := SemiprimeD1JetModeBitsBounds.mode_good ctx _ _ _ _ _ _ _
  have hsign := signed_clock ctx (!row.bit)
    (SemiprimeD1JetModeBits.acquireOriginal ctx (borrow z) a i.val item.mode.order t row.slot tile) hmodeGood
  have hbound := mode_order_mono ctx a _ B hb
  change (SemiprimeD1JetModeBits.acquireOriginal ctx (borrow z) a i.val item.mode.order t row.slot tile).clock ≤
    0+SemiprimeD1JetModeBitsBounds.modeBudget ctx ctx.precision (2^(a+1)*(a+1)) (2^(a+1)) item.mode.order at hmode
  simp only [Nat.zero_add] at hmode
  have hrow : row.slot.val ≤ 2^a := row.slot.isLt.le
  dsimp only [coefficient]
  split
  · change (signed ctx (!row.bit)
      (SemiprimeD1JetModeBits.acquireOriginal ctx (borrow z) a i.val item.mode.order t row.slot tile)).clock+
      (sameBit row.slot.val tile.val i.val).work+item.tile+row.slot.val+2^a+10 ≤ _
    unfold coefficientClock
    omega
  · change ctx.rank+1+(sameBit row.slot.val tile.val i.val).work+item.tile+row.slot.val+2^a+10 ≤ _
    unfold coefficientClock
    omega

/-- Actual coefficient-vector list traversal, with every called coefficient paid. -/
theorem coefficients_clock (ctx : Context) (z : JetRun) (hz : Good ctx z.words) (a : ℕ) (i : Fin a)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (row : Wire a)
    (items : List SemiprimeD1PacketModeMask.Item) (B T : ℕ)
    (hb : ∀item∈items,item.mode.order ≤ B) (ht : ∀item∈items,item.tile ≤ T) :
    (coefficients ctx z a i t row items).work ≤ items.length*(coefficientClock ctx a B T+4)+1 := by
  induction items with
  | nil => simp only [coefficients,List.length_nil,Nat.zero_mul,Nat.zero_add,le_refl]
  | cons item items ih =>
    have hh := coefficient_clock ctx z hz a i t row item B T (hb _ List.mem_cons_self) (ht _ List.mem_cons_self)
    have hh' := ih (fun x hx => hb x (List.mem_cons_of_mem _ hx)) (fun x hx => ht x (List.mem_cons_of_mem _ hx))
    change (coefficient ctx z a i t row item).clock+(coefficients ctx z a i t row items).work+4 ≤ _
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

/-- Computed row recipe satisfies the actual physical coefficient interpreter's
source invariant, with no intermediate shape or fit advice. -/
theorem recipe_source (ctx : Context) (z : JetRun) (a : ℕ) (i : Fin a)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (row : Wire a) (columns : List (Wire a))
    (items : List SemiprimeD1PacketModeMask.Item) :
    Source ctx ctx.precision items.length (recipe ctx z a i t row columns items).value := by
  have hb := rowBase_good ctx z a t row columns
  refine ⟨hb.1.le,hb.2,?_,?_⟩
  · change (coefficients ctx z a i t row items).value.length ≤ items.length
    rw [SemiprimeD1PacketEntryValue.coefficients_value,List.length_map]
  · intro v hv
    change v ∈ (coefficients ctx z a i t row items).value at hv
    rw [SemiprimeD1PacketEntryValue.coefficients_value] at hv
    obtain ⟨item,_,rfl⟩ := List.mem_map.mp hv
    have hh := coefficient_good ctx z a i t row item
    exact ⟨hh.1.le,hh.2⟩

/-- Full row acquisition budget, polynomial in the original catalogue and row columns. -/
def recipeClock (ctx : Context) (a C K B T : ℕ) : ℕ :=
  rowBaseClock ctx a C+K*(coefficientClock ctx a B T+4)+6

/-- Cached base and coefficient producers are both retained by the actual recipe. -/
theorem recipe_clock (ctx : Context) (z : JetRun) (hz : Good ctx z.words) (a : ℕ) (i : Fin a)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (row : Wire a) (columns : List (Wire a))
    (items : List SemiprimeD1PacketModeMask.Item) (B T : ℕ)
    (hb : ∀item∈items,item.mode.order ≤ B) (ht : ∀item∈items,item.tile ≤ T) :
    (recipe ctx z a i t row columns items).work ≤ recipeClock ctx a columns.length items.length B T := by
  have hbase := rowBase_clock ctx z hz a t row columns
  have hcoeff := coefficients_clock ctx z hz a i t row items B T hb ht
  change (rowBase ctx z a t row columns).clock+(coefficients ctx z a i t row items).work+5 ≤ _
  unfold recipeClock
  omega

/-- All actual real rows are acquired once; no local truth table callback is supplied. -/
theorem recipes_clock (ctx : Context) (z : JetRun) (hz : Good ctx z.words) (a : ℕ) (i : Fin a)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (columns : List (Wire a))
    (items : List SemiprimeD1PacketModeMask.Item) (rows : List (Wire a)) (B T : ℕ)
    (hb : ∀item∈items,item.mode.order ≤ B) (ht : ∀item∈items,item.tile ≤ T) :
    (recipes ctx z a i t columns items rows).work ≤
      rows.length*(recipeClock ctx a columns.length items.length B T+4)+1 := by
  induction rows with
  | nil => simp only [recipes,List.length_nil,Nat.zero_mul,Nat.zero_add,le_refl]
  | cons row rows ih =>
    have hh := recipe_clock ctx z hz a i t row columns items B T hb ht
    change (recipe ctx z a i t row columns items).work+(recipes ctx z a i t columns items rows).work+4 ≤ _
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

end RiemannGaussian.SemiprimeD1PacketCoefficientClock
