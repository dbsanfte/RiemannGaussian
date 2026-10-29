/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimePaidFiniteEnumerations

/-! # Exact zero-first order of the original canonical word menu
This is an ordered-list identity. It permits the acquired head-major bank to
be consumed by the original zero-first/filter-tail caller without changing its
deterministic tie rule. All word functions in this module are specifications.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeSourceWordMenuOrder
open OAI.Algorithms.SubexponentialSAT.MulticolorTypes

/-- The actual canonical head-major list starts with the literal all-zero word. -/
theorem words_head_zero (r Q : ℕ) [NeZero r] :
    ∃ tail,(SemiprimeFiniteEnumerations.words r Q).values=(fun _ => 0)::tail := by
  induction Q with
  | zero =>
    refine ⟨[],?_⟩
    change [(fun i : Fin 0 => Fin.elim0 i)]=[fun _ => 0]
    congr 1
    funext i
    exact Fin.elim0 i
  | succ Q ih =>
    obtain ⟨tail,ht⟩ := ih
    obtain ⟨r',hr⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne r)
    subst r
    change ∃ rest,((List.finRange (r'+1)).product (SemiprimeFiniteEnumerations.words (r'+1) Q).values).map
      (fun p => (Fin.cons p.1 p.2 : Word (r'+1) (Q+1)))=(fun _ => 0)::rest
    rw [List.finRange_succ,ht]
    let rest := ((tail.map (fun w => ((0:Fin (r'+1)),w)))++
      ((List.finRange r').map Fin.succ).product ((fun _ => (0:Fin (r'+1)))::tail)).map
        (fun p => (Fin.cons p.1 p.2 : Word (r'+1) (Q+1)))
    refine ⟨rest,?_⟩
    change (Fin.cons (0:Fin (r'+1)) (fun _ : Fin Q => 0) : Word (r'+1) (Q+1))::rest=
      (fun _ => 0)::rest
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · rfl

/-- Filtering a duplicate-free list's first value leaves its exact ordered tail. -/
theorem filter_head {A : Type} [DecidableEq A] (a : A) (tail : List A)
    (hn : (a::tail).Nodup) :
    (a::tail).filter (fun x => decide (x ≠ a))=tail := by
  simp only [List.filter_cons,ne_eq,not_true_eq_false,decide_false,Bool.false_eq_true,ite_false]
  apply List.filter_eq_self.mpr
  intro x hx
  simp only [decide_eq_true_eq]
  intro heq
  subst x
  exact (List.nodup_cons.mp hn).1 hx

/-- The original indexed caller's zero-first/filter-tail list is the full canonical list. -/
theorem words_zero_first (r Q : ℕ) [NeZero r] :
    (SemiprimeFiniteEnumerations.words r Q).values=
      (fun _ => 0)::(SemiprimeFiniteEnumerations.words r Q).values.filter
        (fun w => decide (w ≠ fun _ => 0)) := by
  obtain ⟨tail,ht⟩ := words_head_zero r Q
  have hn := (SemiprimeFiniteEnumerations.words r Q).nodup
  rw [ht] at hn ⊢
  rw [filter_head _ tail hn]

/-- The fully acquired indexed enumeration retains exactly that ordered word menu. -/
theorem indexed_menu (n F r Q : ℕ) [NeZero r] (arity : Fin F → ℕ) :
    (SemiprimePaidFiniteEnumerations.indexed n F r Q arity).value.wordFirst::
      (SemiprimePaidFiniteEnumerations.indexed n F r Q arity).value.wordTail=
        (SemiprimeFiniteEnumerations.words r Q).values := by
  rw [SemiprimePaidFiniteEnumerations.indexed_value]
  exact (words_zero_first r Q).symm

end RiemannGaussian.SemiprimeSourceWordMenuOrder
