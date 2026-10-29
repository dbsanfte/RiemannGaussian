/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PacketEntryValue

/-! # Original kernel, signed row and source-power recipe values
Every statement refines an executed physical supplier. The original mode's
same-bit hypothesis is discharged by the actual runtime branch, not supplied
as intermediate algebra advice.
-/
set_option autoImplicit false
set_option maxHeartbeats 2800000
namespace RiemannGaussian.SemiprimeD1PacketEntryComponents
open SemiprimeD1PacketEntryBits SemiprimeD1PacketEntryValue SemiprimeD1PacketEntryInputs
open SemiprimeD1JetAxes SemiprimeD1JetInterpretation
noncomputable section

/-- Every real local-column term is the acquired original wire value times its Boolean bit. -/
theorem baseTerm_value (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun) (a : ℕ)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (row column : Wire a)
    (hpos : ctx.Positive) (hp : 0<ctx.precision) :
    interpret ctx (baseTerm ctx z a t row column).words=
      if column.bit then SemiprimeD1UniversalModeData.entryValue ctx.precision
        (SemiprimeD1JetAlgebra.constants (SemiprimeD1JetBoxIndex.dims ctx.axes)) (interpret ctx z.words)
        (SemiprimeD1WireKernelOriginal.acquireOriginal a t row.slot column.slot) else 0 := by
  cases hb : column.bit
  · simpa only [baseTerm,hb,Bool.false_eq_true,ite_false] using SemiprimeD1JetAffineCoefficient.interpret_zero ctx
  · simpa only [baseTerm,hb,ite_true,borrow] using
      SemiprimeD1JetKernelBits.acquireOriginal_value ctx (borrow z) a t row.slot column.slot hpos hp

/-- Both row Boolean cases use the actual local sum: Y true gives base, false gives 1-base. -/
theorem rowBase_value (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun) (a : ℕ)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (row : Wire a) (columns : List (Wire a))
    (hpos : ctx.Positive) :
    interpret ctx (rowBase ctx z a t row columns).words=
      if row.bit then (columns.map (fun column => interpret ctx (baseTerm ctx z a t row column).words)).sum
      else 1-(columns.map (fun column => interpret ctx (baseTerm ctx z a t row column).words)).sum := by
  cases hb : row.bit
  · simp only [rowBase,hb,Bool.false_eq_true,ite_false]
    rw [SemiprimeD1JetOperations.interpret_add ctx _ _ hpos,
      SemiprimeD1JetAffineCoefficient.interpret_one ctx hpos,signed_value ctx _ _ hpos,
      SemiprimeD1JetAffineCoefficient.sumRuns_value ctx _ hpos]
    simp only [ite_true,List.map_map,Function.comp_def,sub_eq_add_neg]
  · simp only [rowBase,hb,ite_true]
    rw [SemiprimeD1JetAffineCoefficient.sumRuns_value ctx _ hpos]
    simp only [List.map_map,Function.comp_def]

/-- Source tile powers are computed from the literal column slot, with no power oracle. -/
theorem sourceTerm_value (ctx : Context) (a : ℕ) (i : Fin a)
    (item : SemiprimeD1PacketModeMask.Item) (column : Wire a) (hpos : ctx.Positive) :
    interpret ctx (sourceTerm ctx a i item column).words=
      if column.bit && (column.slot.val%2^(i.val+1) == item.tile) then
        (SemiprimeD1JetAlgebra.constants (SemiprimeD1JetBoxIndex.dims ctx.axes)
          ((column.slot.val/2^(i.val+1):ℕ):ZMod (2^ctx.precision)))^item.mode.order else 0 := by
  dsimp only [sourceTerm]
  split_ifs
  · rw [SemiprimeD1JetPolynomialBits.power_value ctx _ _ hpos,
      SemiprimeD1JetPolynomialBits.scalar_value ctx _ hpos,
      SemiprimeD1JetPolynomialBits.magnitude_value]
  · exact SemiprimeD1JetAffineCoefficient.interpret_zero ctx

/-- The source factor uses the ORIGINAL exponent, and empty-base exponent zero is one. -/
theorem sourceFactor_value (ctx : Context) (a : ℕ) (i : Fin a) (columns : List (Wire a))
    (beta : List ℕ) (index : ℕ) (item : SemiprimeD1PacketModeMask.Item) (hpos : ctx.Positive) :
    interpret ctx (sourceFactor ctx a i columns beta index item).words=
      if item.inPacket && item.sourceHere then
        (columns.map (fun column => interpret ctx (sourceTerm ctx a i item column).words)).sum^
          ((beta[index]?).getD 0)
      else 1 := by
  dsimp only [sourceFactor]
  split_ifs
  · rw [SemiprimeD1JetPolynomialBits.power_value ctx _ _ hpos,
      SemiprimeD1JetAffineCoefficient.sumRuns_value ctx _ hpos]
    rw [SemiprimeD1AffineCoefficient.read_value]
    simp only [List.map_map,Function.comp_def]
    rfl
  · exact SemiprimeD1JetAffineCoefficient.interpret_one ctx hpos

/-- The actual mode coefficient branch proves its own original same-bit condition. -/
theorem coefficient_value (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (a : ℕ) (i : Fin a) (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (row : Wire a)
    (item : SemiprimeD1PacketModeMask.Item) (hpos : ctx.Positive) (hp : 0<ctx.precision)
    (ht : SemiprimeD1WireKernelOriginal.point a t.val≠0)
    (hi : padicValInt 2 (SemiprimeD1WireKernelOriginal.point a t.val)=i.val) :
    let tile : Fin (2^a) := ⟨item.tile%2^a,Nat.mod_lt _ (by positivity)⟩
    interpret ctx (coefficient ctx z a i t row item).words=
      if item.inPacket && item.targetHere && !item.sourceHere &&
          (row.slot.val.testBit i.val == tile.val.testBit i.val) then
        let value := SemiprimeD1UniversalModeData.evaluate ctx.precision
          (SemiprimeD1JetAlgebra.constants (SemiprimeD1JetBoxIndex.dims ctx.axes)) (interpret ctx z.words)
          (SemiprimeD1UniversalModeData.acquireOriginal ctx.precision a i.val item.mode.order t row.slot tile)
        if row.bit then value else -value
      else 0 := by
  dsimp only [coefficient]
  rw [sameBit_value]
  by_cases h : (item.inPacket && item.targetHere && !item.sourceHere &&
      (row.slot.val.testBit i.val == (item.tile%2^a).testBit i.val))=true
  · simp only [h,ite_true]
    have hbit : row.slot.val.testBit i.val=(item.tile%2^a).testBit i.val :=
      beq_iff_eq.mp (Bool.and_eq_true_iff.mp h).2
    rw [signed_value ctx _ _ hpos,
      SemiprimeD1JetModeBits.acquireOriginal_value ctx (borrow z) a i.val item.mode.order t row.slot _ hpos hp ht hi hbit]
    cases row.bit <;> rfl
  · simp only [h]
    exact SemiprimeD1JetAffineCoefficient.interpret_zero ctx

end
end RiemannGaussian.SemiprimeD1PacketEntryComponents
