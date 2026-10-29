/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceChoiceBits
import RiemannGaussian.SemiprimeReportPolynomialGrowth

/-! # Composition of physical source control with an acquired score compiler
These theorems expose the exact score-producer interface and permit the original
source's finite labels to be represented by physical ID words. The decoder is
used only in the specification. No candidate table, branch tree or rational
score answer is executed by this control layer.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeSourceChoiceRefinement
open SemiprimeRationalBits SemiprimeMaterializedWords SemiprimeSourceChoiceBits
open SemiprimeReportPolynomialGrowth

/-- An actual score compiler with a value-refinement theorem composes with
physical choice over arbitrary represented original source labels. -/
theorem choose_decode {A : Type} (decode : List Bool → A)
    (physical : List Bool → RationalReport) (source : A → Run ℚ)
    (hv : ∀ w, (physical w).word.Valid)
    (hs : ∀ w, (physical w).word.value = (source (decode w)).value)
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

/-- The physical token-controlled loop agrees with the original label assignment.
The premise is the score compiler's correctness, not a supplied branch answer. -/
theorem assign_decode {A : Type} (decode : List Bool → A)
    (physical : List Bool → List (List Bool) → RationalReport)
    (source : ℕ → List A → Run ℚ)
    (hv : ∀ ts xs, (physical ts xs).word.Valid)
    (hs : ∀ ts xs, (physical ts xs).word.value = (source ts.length (xs.map decode)).value)
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
      (fun w => hv tokens (w::fixed))
      (fun w => by simpa only [List.map_cons] using hs tokens (w::fixed)) a tail
    simp only [SemiprimeSourceChoiceBits.assign,copyIDs_value,ih,List.map_cons,hc,
      List.length_cons,SemiprimeMaterializedWords.assign]

/-- The complete physical control wrapper includes token acquisition before
returning the same original label assignment, decoded only in this theorem. -/
theorem run_decode {A : Type} (decode : List Bool → A)
    (physical : List Bool → List (List Bool) → RationalReport)
    (source : ℕ → List A → Run ℚ)
    (hv : ∀ ts xs, (physical ts xs).word.Valid)
    (hs : ∀ ts xs, (physical ts xs).word.value = (source ts.length (xs.map decode)).value)
    (a : List Bool) (tail : List (List Bool)) (n : ℕ) (fixed : List (List Bool)) :
    (SemiprimeSourceChoiceBits.run a tail physical n fixed).value.map decode =
      (SemiprimeMaterializedWords.assign (decode a) (tail.map decode) source n
        (fixed.map decode)).value := by
  simp only [SemiprimeSourceChoiceBits.run,acquireTokens_value,
    assign_decode decode physical source hv hs,List.length_replicate]

/-- Fixed polynomial overhead in original finite dimensions and an acquired
producer envelope. This does not assume the score producer has been compiled. -/
theorem control_polynomial : ∃ C k : ℕ,∀ A F W B N n S,
    A ≤ S → F ≤ S → W ≤ S → B ≤ S → N ≤ S → n ≤ S →
    2*n+3+n*(A*(2*F+200*(W+1)^2+4*B+5)+4*B+2+N*(4*B+4)+4)+
      N*(4*B+4)+1 ≤ C*(S+1)^k := by
  have h : Bound (fun S =>
    2*S+3+S*(S*(2*S+200*(S+1)^2+4*S+5)+4*S+2+S*(4*S+4)+4)+S*(4*S+4)+1) := by
    boundArithmetic
  obtain ⟨C,k,h⟩ := h
  refine ⟨C,k,?_⟩
  intro A F W B N n S hA hF hW hB hN hn
  apply le_trans _ (h S)
  dsimp only
  gcongr

end RiemannGaussian.SemiprimeSourceChoiceRefinement
