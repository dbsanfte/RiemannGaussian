/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PacketSourceProductValues
import RiemannGaussian.SemiprimeD1PacketRowProducts

/-! # Executed packet entries are the acquired polynomial coefficient times source product
Borrowing affects only reports, never acquired coefficient data. The theorem
uses the actual physical row recipes and mask restriction; no row polynomial,
source-value family or coefficient answer is a caller input.
-/
set_option autoImplicit false
set_option maxHeartbeats 120000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1PacketEntryPolynomial
open SemiprimeD1JetAxes SemiprimeD1JetInterpretation
open SemiprimeD1PacketEntryInputs SemiprimeD1PacketEntryBits

/-- Physical local base terms ignore only the borrowed producer report. -/
theorem baseTerm_borrow (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (a : ℕ) (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (row column : Wire a) :
    baseTerm ctx (borrow z) a t row column=baseTerm ctx z a t row column := rfl

/-- Physical signed mode coefficients use the identical borrowed current word vector. -/
theorem coefficient_borrow (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (a : ℕ) (i : Fin a) (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (row : Wire a)
    (item : SemiprimeD1PacketModeMask.Item) :
    coefficient ctx (borrow z) a i t row item=coefficient ctx z a i t row item := rfl

/-- Acquired constant row data is unchanged by producer-report borrowing. -/
theorem rowBase_borrow (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (a : ℕ) (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (row : Wire a) (columns : List (Wire a)) :
    rowBase ctx (borrow z) a t row columns=rowBase ctx z a t row columns := rfl

/-- The actual entire cached coefficient list is unchanged. -/
theorem coefficients_borrow (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (a : ℕ) (i : Fin a) (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (row : Wire a)
    (items : List SemiprimeD1PacketModeMask.Item) :
    (coefficients ctx (borrow z) a i t row items).value=(coefficients ctx z a i t row items).value := by
  rw [SemiprimeD1PacketEntryValue.coefficients_value,SemiprimeD1PacketEntryValue.coefficients_value]
  simp only [coefficient_borrow]

/-- The literal acquired affine row, not just its interpretation, is unchanged. -/
theorem recipe_borrow (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (a : ℕ) (i : Fin a) (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (row : Wire a)
    (columns : List (Wire a)) (items : List SemiprimeD1PacketModeMask.Item) :
    (recipe ctx (borrow z) a i t row columns items).value=(recipe ctx z a i t row columns items).value := by
  dsimp only [recipe]
  rw [rowBase_borrow,coefficients_borrow]

/-- The entire literal row inventory is unchanged, with order and multiplicity retained. -/
theorem recipes_borrow (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (a : ℕ) (i : Fin a) (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (columns rows : List (Wire a)) (items : List SemiprimeD1PacketModeMask.Item) :
    (recipes ctx (borrow z) a i t columns items rows).value=
      (recipes ctx z a i t columns items rows).value := by
  rw [SemiprimeD1PacketEntryValue.recipes_value,SemiprimeD1PacketEntryValue.recipes_value]
  simp only [recipe_borrow]

/-- Borrowing leaves the actual packet polynomial unchanged, coefficient by coefficient. -/
theorem polynomial_borrow (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (a : ℕ) (i : Fin a) (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (columns rows : List (Wire a)) (cache : SemiprimeD1PacketModeMask.Cache) :
    SemiprimeD1PacketPolynomialAcquired.polynomial ctx (borrow z) a i t columns rows cache=
      SemiprimeD1PacketPolynomialAcquired.polynomial ctx z a i t columns rows cache := by
  unfold SemiprimeD1PacketPolynomialAcquired.polynomial
  rw [recipes_borrow]

/-- Executed coefficient acquisition uses exactly the acquired packet polynomial
and ORIGINAL global beta source exponents, over the concrete current quotient. -/
theorem evaluate_polynomial {V : ℕ} (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (a : ℕ) (i : Fin a) (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (cache : SemiprimeD1PacketModeMask.Cache) (endpoints : List (SemiprimeD1ChildGraph.Endpoint V))
    (beta : List ℕ) (bits : List Bool) (hpos : ctx.Positive) :
    let input:=gather a endpoints bits
    interpret ctx (evaluate ctx z a i t cache endpoints beta bits).words=
      (SemiprimeD1PacketPolynomialAcquired.polynomial ctx z a i t input.columns input.rows cache).coeff
        (SemiprimeD1SeparatedCoefficient.restrict (SemiprimeD1PacketModeProjection.targetSet cache) beta.toFinsupp)*
      interpret ctx (sourceProduct ctx a i input.columns beta cache.items 0).words := by
  dsimp only
  rw [SemiprimeD1PacketEntryValue.evaluate_value ctx z a i t cache endpoints beta bits hpos,
    recipes_borrow,SemiprimeD1PacketModeProjection.restrict_toFinsupp,
    ← SemiprimeD1PacketEntryValue.sourceProduct_value ctx a i _ beta cache.items 0 hpos]
  rfl
/-- Borrowed producer reports do not change interpreted executed entries;
this is a value theorem only and does not identify or discard either report. -/
theorem evaluate_borrow {V : ℕ} (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (a : ℕ) (i : Fin a) (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (cache : SemiprimeD1PacketModeMask.Cache) (endpoints : List (SemiprimeD1ChildGraph.Endpoint V))
    (beta : List ℕ) (bits : List Bool) (hpos : ctx.Positive) :
    interpret ctx (evaluate ctx (borrow z) a i t cache endpoints beta bits).words=
      interpret ctx (evaluate ctx z a i t cache endpoints beta bits).words := by
  rw [evaluate_polynomial ctx (borrow z) a i t cache endpoints beta bits hpos,
    evaluate_polynomial ctx z a i t cache endpoints beta bits hpos,polynomial_borrow]
end RiemannGaussian.SemiprimeD1PacketEntryPolynomial
