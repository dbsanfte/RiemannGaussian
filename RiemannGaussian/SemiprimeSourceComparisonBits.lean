/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceMemoryBits

/-! # Direct Boolean comparison of source rational scores
The two unreduced cross-products are compared as signed physical words.
No rational interpretation, GCD reduction or intermediate fit test controls
execution. Positive original denominators suffice for exact order, including
both encodings of zero and left-on-tie selection.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeSourceComparisonBits
open SemiprimeBitArithmetic SemiprimeBitDivision SemiprimeBitIndexClipping
open SemiprimeRationalBits

/-- Executed cross-products, complete signed order diagnostics and total work. -/
structure Report where
  /-- Left numerator times right denominator. -/
  left : SignedProductReport
  /-- Right numerator times left denominator. -/
  right : SignedProductReport
  /-- Both borrow comparisons and zero scans. -/
  order : SignedOrderReport
  /-- All product, order and record-construction work. -/
  clock : ℕ

/-- Rational order executes only signed Boolean products and comparison. -/
def compare (x y : RationalWord) : Report :=
  let left := mulSignedBits x.numerator ⟨false,y.denominator⟩
  let right := mulSignedBits y.numerator ⟨false,x.denominator⟩
  let order := leSignedBits left.word right.word
  ⟨left,right,order,left.clock+right.clock+order.clock+3⟩

/-- Exact order for arbitrary padded valid encodings; equality selects the left. -/
theorem compare_correct (x y : RationalWord) (hx : x.Valid) (hy : y.Valid) :
    (compare x y).order.le = true ↔ x.value ≤ y.value := by
  have hdx : (0:ℚ) < bitValue x.denominator := by exact_mod_cast hx
  have hdy : (0:ℚ) < bitValue y.denominator := by exact_mod_cast hy
  simp only [compare,leSignedBits_exact,mulSignedBits_value]
  change x.numerator.value*(bitValue y.denominator:ℤ) ≤
    y.numerator.value*(bitValue x.denominator:ℤ) ↔ _
  rw [RationalWord.value,RationalWord.value,div_le_div_iff₀ hdx hdy]
  exact_mod_cast (Iff.rfl :
    x.numerator.value*(bitValue y.denominator:ℤ) ≤ y.numerator.value*(bitValue x.denominator:ℤ) ↔
    x.numerator.value*(bitValue y.denominator:ℤ) ≤ y.numerator.value*(bitValue x.denominator:ℤ))

/-- Actual cross-product words retain at most three times the original width. -/
theorem compare_width (x y : RationalWord) (W : ℕ) (hx : Width x W) (hy : Width y W) :
    (compare x y).left.word.magnitude.length ≤ 3*W ∧
      (compare x y).right.word.magnitude.length ≤ 3*W := by
  exact ⟨(mulSignedBits_cost_width hx.1 (right:=⟨false,y.denominator⟩) hy.2).2,
    (mulSignedBits_cost_width hy.1 (right:=⟨false,x.denominator⟩) hx.2).2⟩

/-- Both full products, borrow comparisons and zero scans have quadratic work. -/
theorem compare_clock (x y : RationalWord) (W : ℕ) (hx : Width x W) (hy : Width y W) :
    (compare x y).clock ≤ 200*(W+1)^2 := by
  have hl := mulSignedBits_cost_width hx.1 (right:=⟨false,y.denominator⟩) hy.2
  have hr := mulSignedBits_cost_width hy.1 (right:=⟨false,x.denominator⟩) hx.2
  have hc := leSignedBits_cost hl.2 hr.2
  dsimp only [compare]
  nlinarith

/-- Concrete rational comparison controls a physical branch without loss on ties. -/
theorem compare_branch {α : Type} (x y : RationalWord) (hx : x.Valid) (hy : y.Valid)
    (a b : α) :
    (if (compare x y).order.le = true then a else b) =
      (if x.value ≤ y.value then a else b) := by
  simp only [compare_correct x y hx hy]

end RiemannGaussian.SemiprimeSourceComparisonBits
