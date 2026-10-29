/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PacketEntryBits

/-! # Exact value of the physically assembled packet entry
This exposes the actually constructed row polynomial, restricted target query,
and original-beta source product. It supplies no desired coefficient or mode
value to the execution; the remaining global D16 identity is separate.
-/
set_option autoImplicit false
set_option maxHeartbeats 2800000
namespace RiemannGaussian.SemiprimeD1PacketEntryValue
open scoped BigOperators
open SemiprimeD1PacketEntryBits SemiprimeD1JetAxes SemiprimeD1JetInterpretation
open SemiprimeD1PacketEntryInputs
noncomputable section

/-- Borrowing a cache is literally the same current coefficient vector. -/
theorem borrow_words (z : SemiprimeD1JetAffineCoefficient.JetRun) : (borrow z).words=z.words := rfl

/-- Actual product execution supplies the concrete current-ring product. -/
theorem multiply_value (ctx : Context) (left right : SemiprimeD1JetAffineCoefficient.JetRun)
    (hpos : ctx.Positive) :
    interpret ctx (multiply ctx left right).words=interpret ctx left.words*interpret ctx right.words :=
  SemiprimeD1JetOperations.interpret_mul ctx _ _ hpos

/-- The literal physical sign is the original row Boolean sign. -/
theorem signed_value (ctx : Context) (negative : Bool) (value : SemiprimeD1JetAffineCoefficient.JetRun)
    (hpos : ctx.Positive) :
    interpret ctx (signed ctx negative value).words=
      if negative then -interpret ctx value.words else interpret ctx value.words := by
  cases negative
  · simp only [signed,Bool.false_eq_true,ite_false,copyVector_value]
  · simp only [signed,ite_true]
    rw [multiply_value ctx _ _ hpos,SemiprimeD1JetKernelBits.integerVector_value ctx (-1) hpos]
    simp only [Int.cast_neg,Int.cast_one,map_neg,map_one]
    ring

/-- Every actual coefficient recipe is acquired in unchanged catalogue order. -/
theorem coefficients_value (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (a : ℕ) (i : Fin a) (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (row : Wire a)
    (items : List SemiprimeD1PacketModeMask.Item) :
    (coefficients ctx z a i t row items).value=
      items.map (fun item => (coefficient ctx z a i t row item).words) := by
  induction items with
  | nil => rfl
  | cons item items ih => simp only [coefficients,ih,List.map_cons]

/-- Actual row recipes retain all actual real row multiplicities and order. -/
theorem recipes_value (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (a : ℕ) (i : Fin a) (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (columns rows : List (Wire a))
    (items : List SemiprimeD1PacketModeMask.Item) :
    (recipes ctx z a i t columns items rows).value=
      rows.map (fun row => (recipe ctx z a i t row columns items).value) := by
  induction rows with
  | nil => rfl
  | cons row rows ih => simp only [recipes,ih,List.map_cons]

/-- Source factors execute in original global exponent/index order. -/
theorem sourceProduct_value (ctx : Context) (a : ℕ) (i : Fin a) (columns : List (Wire a))
    (beta : List ℕ) (items : List SemiprimeD1PacketModeMask.Item) (index : ℕ)
    (hpos : ctx.Positive) :
    interpret ctx (sourceProduct ctx a i columns beta items index).words=
      ((items.zipIdx index).map (fun item =>
        interpret ctx (sourceFactor ctx a i columns beta item.2 item.1).words)).prod := by
  induction items generalizing index with
  | nil => exact SemiprimeD1JetAffineCoefficient.interpret_one ctx hpos
  | cons item items ih =>
    rw [sourceProduct,multiply_value ctx _ _ hpos,ih]
    simp only [List.zipIdx_cons,List.map_cons,List.prod_cons]

/-- Actual single-entry refinement. Only this packet's target exponents enter the
coefficient query; the source product uses each ORIGINAL global exponent. -/
theorem evaluate_value {V : ℕ} (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (a : ℕ) (i : Fin a) (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (items : SemiprimeD1PacketModeMask.Cache) (endpoints : List (SemiprimeD1ChildGraph.Endpoint V))
    (beta : List ℕ) (bits : List Bool) (hpos : ctx.Positive) :
    let input := gather a endpoints bits
    let rows := (recipes ctx (borrow z) a i t input.columns items.items input.rows).value
    interpret ctx (evaluate ctx z a i t items endpoints beta bits).words=
      (SemiprimeD1AffineCoefficient.polynomial items.items.length
        (rows.map (SemiprimeD1JetAffineCoefficient.rowValue ctx))).coeff
        (SemiprimeD1PacketModeMask.restrict items beta).value.toFinsupp *
      ((items.items.zipIdx 0).map (fun item =>
        interpret ctx (sourceFactor ctx a i input.columns beta item.2 item.1).words)).prod := by
  dsimp only
  change interpret ctx (multiply ctx
    (SemiprimeD1JetAffineCoefficient.evaluate ctx items.items.length _ _)
    (sourceProduct ctx a i _ beta items.items 0)).words=_
  rw [multiply_value ctx _ _ hpos,SemiprimeD1JetAffineCoefficient.evaluate_coefficient ctx _ _ _ hpos,
    sourceProduct_value ctx _ _ _ _ _ _ hpos]

/-- Whole entry output is structurally canonical without an intermediate Fits premise. -/
theorem evaluate_good {V : ℕ} (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (a : ℕ) (i : Fin a) (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (items : SemiprimeD1PacketModeMask.Cache) (endpoints : List (SemiprimeD1ChildGraph.Endpoint V))
    (beta : List ℕ) (bits : List Bool) :
    SemiprimeD1TensorTables.GoodWords ctx (evaluate ctx z a i t items endpoints beta bits).words := by
  refine ⟨SemiprimeD1JetRingBits.mul_shape _ _ _,?_⟩
  intro w hw
  exact ⟨SemiprimeD1JetRingBits.mul_compact _ _ _ w hw,SemiprimeD1JetRingBits.mul_bounded _ _ _ w hw⟩

end
end RiemannGaussian.SemiprimeD1PacketEntryValue
