/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceChoiceOrder

/-! # Physical score order with original finite source-label metadata
All score comparisons execute the Boolean comparator. Labels and finite loop
indices retain the original source metadata representation; their complete
encoding/allocation refinement is a separate whole-machine obligation. This
entry point permits an acquired physical score producer to replace the original
rational objective while preserving its exact deterministic labels.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RiemannGaussian.SemiprimeSourceScoreChoice
open SemiprimeRationalBits SemiprimeMaterializedWords

/-- Compare acquired score words and retain the original selected label reference. -/
def choose {A : Type} (score : A → RationalReport) (a : A) : List A → Run A
  | [] => ⟨a,1⟩
  | b::bs =>
    let next := choose score b bs
    let left := score a
    let right := score next.value
    let order := SemiprimeSourceComparisonBits.compare left.word right.word
    ⟨if order.order.le = true then a else next.value,
      next.work+left.clock+right.clock+order.clock+3⟩

/-- Order equivalence suffices to preserve the original chosen label and tie rule. -/
theorem choose_refines {A : Type} (physical : A → RationalReport) (source : A → Run ℚ)
    (hv : ∀ a,(physical a).word.Valid)
    (ho : ∀ a b,(physical a).word.value ≤ (physical b).word.value ↔
      (source a).value ≤ (source b).value) (a : A) (tail : List A) :
    (choose physical a tail).value=(SemiprimeMaterializedWords.choose source a tail).value := by
  induction tail generalizing a with
  | nil => rfl
  | cons b bs ih =>
    simp only [choose,SemiprimeMaterializedWords.choose]
    rw [SemiprimeSourceComparisonBits.compare_branch _ _ (hv a) (hv _)]
    simp only [ho,ih]

/-- Every actual score callback and physical comparator remains in the report. -/
theorem choose_work {A : Type} (physical : A → RationalReport) (a : A) (tail : List A)
    (F W : ℕ) (h : ∀ a,(physical a).clock ≤ F ∧ Width (physical a).word W) :
    (choose physical a tail).work ≤ tail.length*(2*F+200*(W+1)^2+3)+1 := by
  induction tail generalizing a with
  | nil => simp [choose]
  | cons b bs ih =>
    have hn := ih b
    have hl := h a
    have hr := h (choose physical b bs).value
    have hc := SemiprimeSourceComparisonBits.compare_clock _ _ W hl.2 hr.2
    simp only [choose,List.length_cons]
    nlinarith

/-- Source-label assignment follows only actual Boolean comparison decisions. -/
def assign {A : Type} (a : A) (tail : List A)
    (physical : ℕ → List A → RationalReport) : ℕ → List A → Run (List A)
  | 0,fixed => ⟨fixed,1⟩
  | n+1,fixed =>
    let next := choose (fun w => physical n (w::fixed)) a tail
    let rest := assign a tail physical n (next.value::fixed)
    ⟨rest.value,next.work+rest.work+3⟩

/-- Physical comparison order preserves every original finite assignment step. -/
theorem assign_refines {A : Type} (a : A) (tail : List A)
    (physical : ℕ → List A → RationalReport) (source : ℕ → List A → Run ℚ)
    (hv : ∀ n xs,(physical n xs).word.Valid)
    (ho : ∀ n xs v w,(physical n (v::xs)).word.value ≤ (physical n (w::xs)).word.value ↔
      (source n (v::xs)).value ≤ (source n (w::xs)).value)
    (n : ℕ) (fixed : List A) :
    (assign a tail physical n fixed).value=(SemiprimeMaterializedWords.assign a tail source n fixed).value := by
  induction n generalizing fixed with
  | zero => rfl
  | succ n ih =>
    have hc := choose_refines (fun w => physical n (w::fixed)) (fun w => source n (w::fixed))
      (fun w => hv n (w::fixed)) (ho n fixed) a tail
    simp only [assign,ih,hc,SemiprimeMaterializedWords.assign]

/-- Original metadata-prefix lengths bound the whole physical-comparison traversal. -/
theorem assign_work {A : Type} (a : A) (tail : List A)
    (physical : ℕ → List A → RationalReport) (F W N : ℕ)
    (h : ∀ n xs,n+xs.length ≤ N → (physical n xs).clock ≤ F ∧ Width (physical n xs).word W)
    (n : ℕ) (fixed : List A) (hlen : n+fixed.length ≤ N) :
    (assign a tail physical n fixed).work ≤ n*(tail.length*(2*F+200*(W+1)^2+3)+4)+1 := by
  induction n generalizing fixed with
  | zero => simp [assign]
  | succ n ih =>
    have hc := choose_work (fun w => physical n (w::fixed)) a tail F W
      (fun w => h n (w::fixed) (by simp only [List.length_cons] at hlen ⊢;omega))
    have hr := ih ((choose (fun w => physical n (w::fixed)) a tail).value::fixed)
      (by simp only [List.length_cons] at hlen ⊢;omega)
    simp only [assign]
    nlinarith

end RiemannGaussian.SemiprimeSourceScoreChoice
