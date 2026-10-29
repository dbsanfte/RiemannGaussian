import OpenAISemiprime.Algorithms.SubexponentialSAT.LeanCompat

namespace OAI.Algorithms

/-!
# Finite Boolean-valued factor systems

This module formalizes the finite sum of products in Sections 2 and 3 of the
candidate exposition.  Factor tables have genuine local domains, so dependence
only on a scope is enforced by their type.  Counting is an actual finite sum of
natural-number products.  No running-time assertion is made here.
-/

namespace SubexponentialSAT.Factor

open scoped BigOperators

/-- A finite-scope pattern.  Finiteness of the index types is requested only by
those constructions which enumerate them. -/
structure Pattern (V E : Type*) [DecidableEq V] where
  scope : E → Finset V

/-- The nonempty-scope, arity, and incidence hypotheses of Lemma 3.1. -/
structure Pattern.Bounded {V E : Type*} [DecidableEq V] [Fintype E]
    (P : Pattern V E) (k Δ : ℕ) : Prop where
  nonempty_scope : ∀ e, (P.scope e).Nonempty
  arity_le : ∀ e, (P.scope e).card ≤ k
  incidence_le : ∀ v, (Finset.univ.filter fun e => v ∈ P.scope e).card ≤ Δ

/-- A factor reads exactly the coordinates in its declared scope. -/
structure System (V E A : Type*) [DecidableEq V] extends Pattern V E where
  table : (e : E) → ({v // v ∈ scope e} → A) → Bool

variable {V E A : Type*} [DecidableEq V]

/-- Evaluate one local table on a global assignment. -/
def evalFactor (F : System V E A) (e : E) (x : V → A) : Bool :=
  F.table e (fun v => x v.1)

/-- An assignment satisfies the system when every local table accepts it. -/
def Satisfies (F : System V E A) (x : V → A) : Prop :=
  ∀ e, evalFactor F e x = true

/-- Satisfaction is decidable by checking the explicitly finite factor index. -/
instance instDecidableSatisfies [Fintype E] (F : System V E A) (x : V → A) :
    Decidable (Satisfies F x) :=
  inferInstanceAs (Decidable (∀ e, evalFactor F e x = true))

/-- The natural-number indicator of one factor accepting an assignment. -/
def factorValue (F : System V E A) (e : E) (x : V → A) : ℕ :=
  if evalFactor F e x = true then 1 else 0

@[simp] theorem factorValue_eq_one_iff (F : System V E A) (e : E) (x : V → A) :
    factorValue F e x = 1 ↔ evalFactor F e x = true := by
  simp [factorValue]

@[simp] theorem factorValue_eq_zero_iff (F : System V E A) (e : E) (x : V → A) :
    factorValue F e x = 0 ↔ evalFactor F e x = false := by
  cases h : evalFactor F e x <;> simp [factorValue, h]

/-- Locality is enforced by the table domain, rather than assumed as an axiom. -/
theorem evalFactor_congr (F : System V E A) (e : E) {x y : V → A}
    (h : ∀ v ∈ F.scope e, x v = y v) : evalFactor F e x = evalFactor F e y := by
  unfold evalFactor
  congr 1
  funext v
  exact h v.1 v.2

section FiniteFactors

variable [Fintype E]

/-- The product appearing as one summand of the factor count. -/
def weight (F : System V E A) (x : V → A) : ℕ :=
  ∏ e, factorValue F e x

/-- The product of Boolean-valued indicators is the indicator of satisfaction. -/
theorem weight_eq_indicator (F : System V E A) (x : V → A) :
    weight F x = if Satisfies F x then 1 else 0 := by
  classical
  simp [weight, factorValue, Finset.prod_boole, Satisfies]
  rfl

@[simp] theorem weight_eq_one_iff (F : System V E A) (x : V → A) :
    weight F x = 1 ↔ Satisfies F x := by
  classical
  rw [weight_eq_indicator]
  simp

@[simp] theorem weight_eq_zero_iff (F : System V E A) (x : V → A) :
    weight F x = 0 ↔ ¬ Satisfies F x := by
  classical
  rw [weight_eq_indicator]
  simp

theorem weight_le_one (F : System V E A) (x : V → A) : weight F x ≤ 1 := by
  classical
  rw [weight_eq_indicator]
  split_ifs <;> simp

end FiniteFactors

section Counting

variable [Fintype V] [Fintype E] [Fintype A]

/-- The actual finite set of satisfying assignments. -/
def satisfyingAssignments (F : System V E A) : Finset (V → A) :=
  Finset.univ.filter (Satisfies F)

/-- The sum of products defining the exact integer factor count. -/
def count (F : System V E A) : ℕ :=
  ∑ x : V → A, weight F x

@[simp] theorem mem_satisfyingAssignments (F : System V E A) (x : V → A) :
    x ∈ satisfyingAssignments F ↔ Satisfies F x := by
  classical
  simp [satisfyingAssignments]

/-- The sum of products counts exactly the satisfying assignments. -/
theorem count_eq_card_satisfying (F : System V E A) :
    count F = (satisfyingAssignments F).card := by
  classical
  simp [count, weight_eq_indicator, satisfyingAssignments]

/-- A subtype-cardinality form convenient for transporting solutions by an
explicit equivalence. -/
theorem count_eq_card_subtype (F : System V E A) :
    count F = Fintype.card {x : V → A // Satisfies F x} := by
  classical
  rw [count_eq_card_satisfying]
  simpa only [satisfyingAssignments] using (Fintype.card_subtype (Satisfies F)).symm

/-- Positive count is equivalent to the existence of a satisfying assignment. -/
theorem count_pos_iff (F : System V E A) :
    0 < count F ↔ ∃ x : V → A, Satisfies F x := by
  classical
  rw [count_eq_card_satisfying, Finset.card_pos]
  simp [Finset.Nonempty]

/-- A zero count is equivalent to unsatisfiability. -/
theorem count_eq_zero_iff (F : System V E A) :
    count F = 0 ↔ ∀ x : V → A, ¬ Satisfies F x := by
  simpa only [not_lt, Nat.le_zero, not_exists] using not_congr (count_pos_iff F)

/-- The finite count is no larger than the number of assignments. -/
theorem count_le_card_assignments (F : System V E A) :
    count F ≤ Fintype.card (V → A) := by
  classical
  rw [count_eq_card_satisfying]
  exact Finset.card_le_univ _

/-- The bound used when selecting the prime-power counting modulus. -/
theorem count_le_pow (F : System V E A) :
    count F ≤ Fintype.card A ^ Fintype.card V := by
  simpa only [Fintype.card_fun] using count_le_card_assignments F

/-- Extensional equality of acceptance predicates preserves the exact count. -/
theorem count_congr {F G : System V E A}
    (h : ∀ x : V → A, Satisfies F x ↔ Satisfies G x) : count F = count G := by
  classical
  simp only [count_eq_card_satisfying]
  congr 1
  ext x
  simp only [mem_satisfyingAssignments]
  exact h x

end Counting

end SubexponentialSAT.Factor

end OAI.Algorithms
