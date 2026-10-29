/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib

/-!
# Conditional-count witness recovery

The executed selector uses one zero-child query per requested bit, keeping the
original witness space and only restricting its predicate. The counting function
is an explicit input: its equality to the literal finite count is required for
correctness, and its bit cost is not treated as free. The attached counter counts
the calls on the same recursive branches.

This is the recovery component of the shared-summary factor route. It does not
assert that the tensor counter or multiplication network has been formalized.
-/

namespace RiemannGaussian.SemiprimeCountRecovery
open scoped BigOperators

variable {X I : Type*}

/-- Literal cardinality of the original finite acceptance set. -/
noncomputable def acceptedCount [Fintype X] (P : X → Bool) : ℕ :=
  ∑ x, if P x then 1 else 0

theorem acceptedCount_pos_iff [Fintype X] (P : X → Bool) :
    0 < acceptedCount P ↔ ∃ x, P x = true := by
  classical
  simp [acceptedCount, Finset.nonempty_def]

/-- Prefix restrictions remain data on the original witness space. -/
def restricted (bits : X → I → Bool) (P : X → Bool) (fixed : List (I × Bool)) :
    X → Bool := fun x => P x && fixed.all (fun pair => bits x pair.1 == pair.2)

theorem restricted_cons_true_iff (bits : X → I → Bool) (P : X → Bool)
    (fixed : List (I × Bool)) (i : I) (b : Bool) (x : X) :
    restricted bits P ((i, b) :: fixed) x = true ↔
      restricted bits P fixed x = true ∧ bits x i = b := by
  simp [restricted, and_comm, and_left_comm]

 /-- Selected bit labels and the number of conditional-count calls executed. -/
structure Selection (I : Type*) where
  /-- One chosen Boolean value for each requested index. -/
  values : List (I × Bool)
  /-- Count calls on the same branches that construct `values`. -/
  queries : ℕ

/-- The zero-first selector queries explicit prefixes of the original network.
It does not require a counter for arbitrary global predicates. -/
def select (count : List (I × Bool) → ℕ) :
    List I → List (I × Bool) → Selection I
  | [], _ => ⟨[], 0⟩
  | i :: rest, fixed =>
      let b := if 0 < count ((i, false) :: fixed) then false else true
      let tail := select count rest ((i, b) :: fixed)
      ⟨(i, b) :: tail.values, tail.queries + 1⟩

theorem select_queries (count : List (I × Bool) → ℕ)
    (indices : List I) (fixed : List (I × Bool)) :
    (select count indices fixed).queries = indices.length := by
  induction indices generalizing fixed with
  | nil => rfl
  | cons i rest ih => simp [select, ih]

theorem select_indices (count : List (I × Bool) → ℕ)
    (indices : List I) (fixed : List (I × Bool)) :
    (select count indices fixed).values.map Prod.fst = indices := by
  induction indices generalizing fixed with
  | nil => rfl
  | cons i rest ih => simp [select, ih]

/-- All returned bits belong to one accepted witness of the original prefix.
Only correctness of the original network's conditional counts is required. -/
theorem select_sound [Fintype X] (count : List (I × Bool) → ℕ)
    (bits : X → I → Bool) (P : X → Bool)
    (hcount : ∀ fixed, count fixed = acceptedCount (restricted bits P fixed))
    (indices : List I) (fixed : List (I × Bool))
    (hP : ∃ x, restricted bits P fixed x = true) :
    ∃ x, restricted bits P fixed x = true ∧
      ∀ pair ∈ (select count indices fixed).values, bits x pair.1 = pair.2 := by
  induction indices generalizing fixed with
  | nil =>
    obtain ⟨x, hx⟩ := hP
    exact ⟨x, hx, by simp [select]⟩
  | cons i rest ih =>
    by_cases hz : 0 < count ((i, false) :: fixed)
    · have hzero : ∃ x, restricted bits P ((i, false) :: fixed) x = true := by
        apply (acceptedCount_pos_iff _).mp
        simpa only [hcount] using hz
      obtain ⟨x, hx, htail⟩ := ih ((i, false) :: fixed) hzero
      obtain ⟨hp, hb⟩ := (restricted_cons_true_iff _ _ _ _ _ _).mp hx
      refine ⟨x, hp, ?_⟩
      simpa only [select, hz, ↓reduceIte, List.mem_cons, forall_eq_or_imp,
        Prod.fst, Prod.snd] using And.intro hb htail
    · have hone : ∃ x, restricted bits P ((i, true) :: fixed) x = true := by
        obtain ⟨x, hx⟩ := hP
        have hb : bits x i = true := by
          cases h : bits x i with
          | true => rfl
          | false =>
            have he : ∃ y, restricted bits P ((i, false) :: fixed) y = true :=
              ⟨x, (restricted_cons_true_iff _ _ _ _ _ _).mpr ⟨hx, h⟩⟩
            have hp := (acceptedCount_pos_iff _).mpr he
            rw [← hcount] at hp
            exact False.elim (hz hp)
        exact ⟨x, (restricted_cons_true_iff _ _ _ _ _ _).mpr ⟨hx, hb⟩⟩
      obtain ⟨x, hx, htail⟩ := ih ((i, true) :: fixed) hone
      obtain ⟨hp, hb⟩ := (restricted_cons_true_iff _ _ _ _ _ _).mp hx
      refine ⟨x, hp, ?_⟩
      simpa only [select, hz, ↓reduceIte, List.mem_cons, forall_eq_or_imp,
        Prod.fst, Prod.snd] using And.intro hb htail

/-- Existence-test result followed by optional conditional-bit selection. -/
structure SearchResult (I : Type*) where
  /-- `none` denotes an empty original acceptance set; otherwise selected bits. -/
  values : Option (List (I × Bool))
  /-- Initial existence query plus the executed conditional-count calls. -/
  queries : ℕ

/-- One initial empty-prefix count, followed by one zero-child count per bit. -/
def search (count : List (I × Bool) → ℕ) (indices : List I) : SearchResult I :=
  if 0 < count [] then
    let result := select count indices []
    ⟨some result.values, result.queries + 1⟩
  else ⟨none, 1⟩

theorem search_queries_le (count : List (I × Bool) → ℕ) (indices : List I) :
    (search count indices).queries ≤ indices.length + 1 := by
  unfold search
  split_ifs <;> simp [select_queries]

theorem search_none_iff [Fintype X] (count : List (I × Bool) → ℕ)
    (bits : X → I → Bool) (P : X → Bool)
    (hcount : ∀ fixed, count fixed = acceptedCount (restricted bits P fixed))
    (indices : List I) :
    (search count indices).values = none ↔ ¬ ∃ x, P x = true := by
  have hempty : restricted bits P [] = P := by funext x; simp [restricted]
  by_cases hp : 0 < count []
  · have he : ∃ x, P x = true :=
      (acceptedCount_pos_iff P).mp (by simpa only [hcount, hempty] using hp)
    simp [search, hp, he]
  · have he : ¬ ∃ x, P x = true := by
      intro he
      apply hp
      rw [hcount, hempty]
      exact (acceptedCount_pos_iff P).mpr he
    simp [search, hp, he]

theorem search_some_sound [Fintype X] (count : List (I × Bool) → ℕ)
    (bits : X → I → Bool) (P : X → Bool)
    (hcount : ∀ fixed, count fixed = acceptedCount (restricted bits P fixed))
    (indices : List I) (values : List (I × Bool))
    (h : (search count indices).values = some values) :
    values.map Prod.fst = indices ∧
      ∃ x, P x = true ∧ ∀ pair ∈ values, bits x pair.1 = pair.2 := by
  unfold search at h
  split_ifs at h with hp
  simp only [Option.some.injEq] at h
  subst values
  have he : ∃ x, restricted bits P [] x = true :=
    (acceptedCount_pos_iff _).mp (by simpa only [hcount] using hp)
  obtain ⟨x, hx, hbits⟩ := select_sound count bits P hcount indices [] he
  exact ⟨select_indices _ _ _, x, by simpa [restricted] using hx, hbits⟩

#print axioms acceptedCount_pos_iff
#print axioms select_queries
#print axioms select_indices
#print axioms select_sound
#print axioms search_queries_le
#print axioms search_none_iff
#print axioms search_some_sound

end RiemannGaussian.SemiprimeCountRecovery
