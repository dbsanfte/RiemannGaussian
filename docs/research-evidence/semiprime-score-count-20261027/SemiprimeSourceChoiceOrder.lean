/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceChoiceRefinement

/-! # Exact source choice from order-equivalent physical integer scores
Only comparison order is required. Common positive factors and common offsets
may therefore be cancelled before candidate production. The original candidate
order and left-on-tie rule remain exact, through every dynamic assignment step.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RiemannGaussian.SemiprimeSourceChoiceOrder
open SemiprimeRationalBits SemiprimeMaterializedWords SemiprimeSourceChoiceBits

/-- Physical scores need preserve original order, rather than original scalar values. -/
theorem choose_decode {A : Type} (decode : List Bool → A)
    (physical : List Bool → RationalReport) (source : A → Run ℚ)
    (hv : ∀ w,(physical w).word.Valid)
    (hs : ∀ v w,(physical v).word.value ≤ (physical w).word.value ↔
      (source (decode v)).value ≤ (source (decode w)).value)
    (a : List Bool) (tail : List (List Bool)) :
    decode (SemiprimeSourceChoiceBits.choose physical a tail).value =
      (SemiprimeMaterializedWords.choose source (decode a) (tail.map decode)).value := by
  induction tail generalizing a with
  | nil => simp only [SemiprimeSourceChoiceBits.choose,copyID_value,List.map_nil,
      SemiprimeMaterializedWords.choose]
  | cons b bs ih =>
    simp only [SemiprimeSourceChoiceBits.choose,copyID_value,List.map_cons,
      SemiprimeMaterializedWords.choose]
    rw [SemiprimeSourceComparisonBits.compare_branch _ _ (hv a) (hv _)]
    simp only [apply_ite,hs,ih]
    split <;> simp_all

/-- Every dynamic step accepts a common order transformation of the source objective. -/
theorem assign_decode {A : Type} (decode : List Bool → A)
    (physical : List Bool → List (List Bool) → RationalReport)
    (source : ℕ → List A → Run ℚ)
    (hv : ∀ ts xs,(physical ts xs).word.Valid)
    (hs : ∀ ts xs v w,
      (physical ts (v::xs)).word.value ≤ (physical ts (w::xs)).word.value ↔
        (source ts.length (decode v::xs.map decode)).value ≤
          (source ts.length (decode w::xs.map decode)).value)
    (a : List Bool) (tail : List (List Bool)) (tokens : List Bool) (fixed : List (List Bool)) :
    (SemiprimeSourceChoiceBits.assign a tail physical tokens fixed).value.map decode =
      (SemiprimeMaterializedWords.assign (decode a) (tail.map decode) source tokens.length
        (fixed.map decode)).value := by
  induction tokens generalizing fixed with
  | nil => simp only [SemiprimeSourceChoiceBits.assign,copyIDs_value,List.length_nil,
      SemiprimeMaterializedWords.assign]
  | cons t tokens ih =>
    have hc := choose_decode decode (fun w => physical tokens (w::fixed))
      (fun w => source tokens.length (w::fixed.map decode))
      (fun w => hv tokens (w::fixed)) (hs tokens fixed) a tail
    simp only [SemiprimeSourceChoiceBits.assign,copyIDs_value,ih,List.map_cons,hc,
      List.length_cons,SemiprimeMaterializedWords.assign]

/-- Acquired unary control preserves exact original assignments under score-order refinement. -/
theorem run_decode {A : Type} (decode : List Bool → A)
    (physical : List Bool → List (List Bool) → RationalReport)
    (source : ℕ → List A → Run ℚ)
    (hv : ∀ ts xs,(physical ts xs).word.Valid)
    (hs : ∀ ts xs v w,
      (physical ts (v::xs)).word.value ≤ (physical ts (w::xs)).word.value ↔
        (source ts.length (decode v::xs.map decode)).value ≤
          (source ts.length (decode w::xs.map decode)).value)
    (a : List Bool) (tail : List (List Bool)) (n : ℕ) (fixed : List (List Bool)) :
    (SemiprimeSourceChoiceBits.run a tail physical n fixed).value.map decode =
      (SemiprimeMaterializedWords.assign (decode a) (tail.map decode) source n (fixed.map decode)).value := by
  simp only [SemiprimeSourceChoiceBits.run,acquireTokens_value,
    assign_decode decode physical source hv hs,List.length_replicate]

end RiemannGaussian.SemiprimeSourceChoiceOrder
