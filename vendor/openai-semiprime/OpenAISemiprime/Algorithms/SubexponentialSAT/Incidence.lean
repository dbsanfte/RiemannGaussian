import OpenAISemiprime.Algorithms.SubexponentialSAT.LeanCompat
import OpenAISemiprime.Algorithms.SubexponentialSAT.Factor

namespace OAI.Algorithms

/-!
# Finite factor incidence bounds

Scopes are finite sets: a coordinate occurs at most once in any single factor,
while distinct factors may have equal scopes.  The results below count actual
incidences, bound the neighbors sharing a factor, and account for packing
Boolean variables into chunks followed by one unary validity factor per chunk.
-/

namespace SubexponentialSAT.Incidence

open scoped BigOperators

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype E]

/-- The factors whose scope contains a given coordinate. -/
def incident (scope : E → Finset V) (v : V) : Finset E :=
  Finset.univ.filter fun e => v ∈ scope e

/-- Number of distinct factors containing a coordinate. -/
def degree (scope : E → Finset V) (v : V) : ℕ :=
  (incident scope v).card

omit [DecidableEq E] in
@[simp] theorem mem_incident (scope : E → Finset V) (v : V) (e : E) :
    e ∈ incident scope v ↔ v ∈ scope e := by
  simp [incident]

omit [DecidableEq E] in
theorem degree_eq_sum (scope : E → Finset V) (v : V) :
    degree scope v = ∑ e, if v ∈ scope e then 1 else 0 := by
  simp [degree, incident]

omit [DecidableEq E] in
/-- Counting incidences by coordinates or by factors gives the same result. -/
theorem sum_degrees [Fintype V] (scope : E → Finset V) :
    ∑ v, degree scope v = ∑ e, (scope e).card := by
  simp_rw [degree_eq_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  simp

omit [DecidableEq E] in
/-- Nonempty scopes and maximum coordinate degree imply `m ≤ ΔD`. -/
theorem card_factors_le [Fintype V] (scope : E → Finset V) (Δ : ℕ)
    (hne : ∀ e, (scope e).Nonempty) (hdegree : ∀ v, degree scope v ≤ Δ) :
    Fintype.card E ≤ Δ * Fintype.card V := by
  calc
    Fintype.card E = ∑ _e : E, (1 : ℕ) := by simp
    _ ≤ ∑ e, (scope e).card := by
      apply Finset.sum_le_sum
      intro e _
      exact Finset.card_pos.mpr (hne e)
    _ = ∑ v, degree scope v := (sum_degrees scope).symm
    _ ≤ ∑ _v : V, Δ := Finset.sum_le_sum fun v _ => hdegree v
    _ = Δ * Fintype.card V := by simp [Nat.mul_comm]

/-- Other coordinates sharing at least one factor with `v`. -/
def dependencyNeighbors (scope : E → Finset V) (v : V) : Finset V :=
  (incident scope v).biUnion fun e => (scope e).erase v

omit [DecidableEq E] in
@[simp] theorem mem_dependencyNeighbors (scope : E → Finset V) (v w : V) :
    w ∈ dependencyNeighbors scope v ↔ w ≠ v ∧ ∃ e, v ∈ scope e ∧ w ∈ scope e := by
  simp only [dependencyNeighbors, Finset.mem_biUnion, mem_incident, Finset.mem_erase]
  aesop

omit [DecidableEq E] in
/-- Each incident factor contributes at most `k-1` other coordinates. -/
theorem card_dependencyNeighbors_le_degree_mul (scope : E → Finset V) (v : V) (k : ℕ)
    (harity : ∀ e, (scope e).card ≤ k) :
    (dependencyNeighbors scope v).card ≤ degree scope v * (k - 1) := by
  calc
    (dependencyNeighbors scope v).card ≤
        ∑ e ∈ incident scope v, ((scope e).erase v).card := Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ incident scope v, (k - 1) := by
      apply Finset.sum_le_sum
      intro e he
      rw [Finset.card_erase_of_mem ((mem_incident scope v e).mp he)]
      exact Nat.sub_le_sub_right (harity e) 1
    _ = degree scope v * (k - 1) := by simp [degree]

omit [DecidableEq E] in
/-- Arity at most `k` and degree at most `Δ` imply at most `Δ(k-1)` neighbors. -/
theorem card_dependencyNeighbors_le (scope : E → Finset V) (v : V) (k Δ : ℕ)
    (harity : ∀ e, (scope e).card ≤ k) (hdegree : degree scope v ≤ Δ) :
    (dependencyNeighbors scope v).card ≤ Δ * (k - 1) :=
  (card_dependencyNeighbors_le_degree_mul scope v k harity).trans
    (Nat.mul_le_mul_right (k - 1) hdegree)

section Packing

variable {X : Type*} [DecidableEq X] [Fintype X]

/-- The original variables assigned to one chunk. -/
def chunkFiber (chunk : X → V) (v : V) : Finset X :=
  Finset.univ.filter fun x => chunk x = v

/-- A packed factor reads each distinct chunk touched by its original scope. -/
def packedScope (scope : E → Finset X) (chunk : X → V) (e : E) : Finset V :=
  (scope e).image chunk

omit [DecidableEq X] in
@[simp] theorem mem_chunkFiber (chunk : X → V) (v : V) (x : X) :
    x ∈ chunkFiber chunk v ↔ chunk x = v := by
  simp [chunkFiber]

theorem incident_packedScope (scope : E → Finset X) (chunk : X → V) (v : V) :
    incident (packedScope scope chunk) v =
      (chunkFiber chunk v).biUnion fun x => incident scope x := by
  ext e
  simp only [mem_incident, packedScope, Finset.mem_image,
    Finset.mem_biUnion, mem_chunkFiber]
  constructor
  · rintro ⟨x, hx, hc⟩
    exact ⟨x, hc, hx⟩
  · rintro ⟨x, hc, hx⟩
    exact ⟨x, hx, hc⟩

omit [DecidableEq E] [Fintype E] [DecidableEq X] [Fintype X] in
/-- Packing cannot increase the arity of a factor. -/
theorem card_packedScope_le (scope : E → Finset X) (chunk : X → V) (e : E) :
    (packedScope scope chunk e).card ≤ (scope e).card := Finset.card_image_le

omit [DecidableEq E] [Fintype E] [DecidableEq X] [Fintype X] in
theorem packedScope_nonempty (scope : E → Finset X) (chunk : X → V) (e : E)
    (hne : (scope e).Nonempty) : (packedScope scope chunk e).Nonempty :=
  hne.image chunk

/-- At most `ell` variables of degree at most `B` give chunk degree at most `ell B`. -/
theorem degree_packedScope_le (scope : E → Finset X) (chunk : X → V)
    (v : V) (ell B : ℕ) (hfiber : (chunkFiber chunk v).card ≤ ell)
    (hdegree : ∀ x, degree scope x ≤ B) :
    degree (packedScope scope chunk) v ≤ ell * B := by
  unfold degree
  rw [incident_packedScope]
  calc
    ((chunkFiber chunk v).biUnion fun x => incident scope x).card ≤
        ∑ x ∈ chunkFiber chunk v, (incident scope x).card := Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ chunkFiber chunk v, B := by
      exact Finset.sum_le_sum fun x _ => hdegree x
    _ = (chunkFiber chunk v).card * B := by simp
    _ ≤ ell * B := Nat.mul_le_mul_right B hfiber

end Packing

/-- Add exactly one unary factor for every coordinate. -/
def withUnaryScope (scope : E → Finset V) : E ⊕ V → Finset V
  | .inl e => scope e
  | .inr v => {v}

omit [DecidableEq E] in
/-- The unary factors increase every coordinate degree by exactly one. -/
theorem degree_withUnaryScope [Fintype V] (scope : E → Finset V) (v : V) :
    degree (withUnaryScope scope) v = degree scope v + 1 := by
  rw [degree_eq_sum, Fintype.sum_sum_type]
  congr 1
  · exact (degree_eq_sum scope v).symm
  · simp [withUnaryScope]

/-- Chunk packing plus unary validity factors gives `Δ = 1 + ell B`. -/
theorem degree_packedScope_withUnary_le [Fintype V]
    {X : Type*} [DecidableEq X] [Fintype X]
    (scope : E → Finset X) (chunk : X → V) (v : V) (ell B : ℕ)
    (hfiber : (chunkFiber chunk v).card ≤ ell) (hdegree : ∀ x, degree scope x ≤ B) :
    degree (withUnaryScope (packedScope scope chunk)) v ≤ 1 + ell * B := by
  rw [degree_withUnaryScope]
  exact (Nat.add_le_add_right (degree_packedScope_le scope chunk v ell B hfiber hdegree) 1).trans_eq
    (Nat.add_comm (ell * B) 1)

section FactorPatterns

open SubexponentialSAT.Factor

omit [DecidableEq E] in
/-- The factor-count consequence of the common bounded-pattern interface. -/
theorem bounded_card_factors_le [Fintype V] (P : Pattern V E) (k Δ : ℕ)
    (hP : P.Bounded k Δ) : Fintype.card E ≤ Δ * Fintype.card V :=
  card_factors_le P.scope Δ hP.nonempty_scope hP.incidence_le

omit [DecidableEq E] in
/-- The dependency-neighbor consequence of the common bounded-pattern interface. -/
theorem bounded_card_dependencyNeighbors_le (P : Pattern V E) (v : V) (k Δ : ℕ)
    (hP : P.Bounded k Δ) : (dependencyNeighbors P.scope v).card ≤ Δ * (k - 1) :=
  card_dependencyNeighbors_le P.scope v k Δ hP.arity_le (hP.incidence_le v)

/-- Pack a pattern and add a distinct unary factor for each chunk. -/
def packedUnaryPattern {X : Type*} [DecidableEq X]
    (P : Pattern X E) (chunk : X → V) : Pattern V (E ⊕ V) where
  scope := withUnaryScope (packedScope P.scope chunk)

/-- The full bounded-pattern interface survives chunking and unary validity factors. -/
theorem packedUnaryPattern_bounded [Fintype V]
    {X : Type*} [DecidableEq X] [Fintype X]
    (P : Pattern X E) (chunk : X → V) (k ell B : ℕ)
    (hk : 1 ≤ k) (hP : P.Bounded k B)
    (hfiber : ∀ v, (chunkFiber chunk v).card ≤ ell) :
    (packedUnaryPattern P chunk).Bounded k (1 + ell * B) := by
  constructor
  · intro e
    cases e with
    | inl e => exact packedScope_nonempty P.scope chunk e (hP.nonempty_scope e)
    | inr v => exact Finset.singleton_nonempty v
  · intro e
    cases e with
    | inl e => exact (card_packedScope_le P.scope chunk e).trans (hP.arity_le e)
    | inr v => simpa [packedUnaryPattern, withUnaryScope] using hk
  · intro v
    change degree (withUnaryScope (packedScope P.scope chunk)) v ≤ 1 + ell * B
    exact degree_packedScope_withUnary_le P.scope chunk v ell B (hfiber v) hP.incidence_le

end FactorPatterns

end SubexponentialSAT.Incidence

end OAI.Algorithms
