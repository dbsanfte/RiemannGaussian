import OpenAISemiprime.Algorithms.SubexponentialSAT.LeanCompat
import OpenAISemiprime.Algorithms.SubexponentialSAT.SubexpBlockPacking

namespace OAI.Algorithms

/-!
# Executable complete-block packing

All execution definitions use supplied finite lists, filtering, minimum scans,
indexed list access, and index lookup. No execution definition uses classical
choice or an abstract inverse. Mathematical cardinalities occur only in proofs.
-/

namespace SubexponentialSAT.Subexp.ConstructivePacking

open scoped BigOperators

/-- A supplied, duplicate-free enumeration of the whole finite type. -/
structure FiniteEnumeration (α : Type*) where
  values : List α
  nodup : values.Nodup
  complete : ∀ x, x ∈ values

namespace FiniteEnumeration

variable {α : Type*} [DecidableEq α]

/-- Executable enumeration and inverse, implemented by `get` and `idxOf`. -/
def equivFin (E : FiniteEnumeration α) : Fin E.values.length ≃ α where
  toFun := E.values.get
  invFun x := ⟨E.values.idxOf x, List.idxOf_lt_length_iff.mpr (E.complete x)⟩
  left_inv i := Fin.ext (List.get_idxOf E.nodup i)
  right_inv _x := List.idxOf_get _

theorem length_eq_card [Fintype α] (E : FiniteEnumeration α) :
    E.values.length = Fintype.card α := by
  simpa only [Fintype.card_fin] using Fintype.card_congr E.equivFin

end FiniteEnumeration

/-- A concrete list enumerating a predicate gives a computable subtype equivalence.
The predicate itself need not have a decision procedure: the list is supplied. -/
def listSubtypeEquiv {α : Type*} [DecidableEq α] (xs : List α) (hn : xs.Nodup)
    (p : α → Prop) (hm : ∀ x, x ∈ xs ↔ p x) : Fin xs.length ≃ {x // p x} where
  toFun i := ⟨xs.get i, (hm _).mp (List.get_mem xs i)⟩
  invFun x := ⟨xs.idxOf x.val, List.idxOf_lt_length_iff.mpr ((hm x.val).mpr x.property)⟩
  left_inv i := Fin.ext (List.get_idxOf hn i)
  right_inv _x := Subtype.ext (List.idxOf_get _)

/-- All operational packing inputs are explicit finite data. -/
structure PackingData (V U : Type*) where
  vertices : FiniteEnumeration V
  types : FiniteEnumeration U
  label : V → U

namespace PackingData

variable {V U : Type*} [DecidableEq U]

/-- One scan of the vertex list extracts a type fiber in the original order. -/
def bucket (P : PackingData V U) (u : U) : List V :=
  P.vertices.values.filter fun v => decide (P.label v = u)

theorem bucket_nodup (P : PackingData V U) (u : U) : (P.bucket u).Nodup :=
  P.vertices.nodup.filter _

@[simp] theorem mem_bucket (P : PackingData V U) (u : U) (v : V) :
    v ∈ P.bucket u ↔ P.label v = u := by
  simp [bucket, P.vertices.complete v]

theorem bucket_length_le (P : PackingData V U) (u : U) :
    (P.bucket u).length ≤ P.vertices.values.length := List.length_filter_le _ _

/-- Explicit fiber enumeration, without `Fintype.equivFin`. -/
def bucketEquiv [DecidableEq V] (P : PackingData V U) (u : U) :
    Fin (P.bucket u).length ≃ {v // P.label v = u} :=
  listSubtypeEquiv (P.bucket u) (P.bucket_nodup u) (fun v => P.label v = u)
    (P.mem_bucket u)

/-- The minimum scan uses the vertex-list length as its initial cap. -/
def minCount (P : PackingData V U) : List U → ℕ
  | [] => P.vertices.values.length
  | u :: us => min (P.bucket u).length (P.minCount us)

def blockCount (P : PackingData V U) : ℕ := P.minCount P.types.values

theorem minCount_le_bucket (P : PackingData V U) (us : List U) (u : U) (hu : u ∈ us) :
    P.minCount us ≤ (P.bucket u).length := by
  induction us with
  | nil => simp at hu
  | cons v us ih =>
    rcases List.mem_cons.mp hu with huv | hu
    · subst v
      exact min_le_left _ _
    · exact (min_le_right _ _).trans (ih hu)

theorem blockCount_le_bucket (P : PackingData V U) (u : U) :
    P.blockCount ≤ (P.bucket u).length :=
  P.minCount_le_bucket P.types.values u (P.types.complete u)

/-- The selected portion of each bucket is the first `blockCount` coordinates. -/
def selected (P : PackingData V U) (u : U) : List V :=
  (P.bucket u).take P.blockCount

@[simp] theorem selected_length (P : PackingData V U) (u : U) :
    (P.selected u).length = P.blockCount := by
  simp only [selected, List.length_take, Nat.min_eq_left (P.blockCount_le_bucket u)]

/-- Indexed placement of a type in a block. -/
def vertexAt (P : PackingData V U) (i : Fin P.blockCount) (u : U) : V :=
  (P.bucket u).get ⟨i.val, lt_of_lt_of_le i.isLt (P.blockCount_le_bucket u)⟩

@[simp] theorem label_at (P : PackingData V U) (i : Fin P.blockCount) (u : U) :
    P.label (P.vertexAt i u) = u :=
  (P.mem_bucket u _).mp (List.get_mem _ _)

variable [DecidableEq V]

/-- Find the coordinate's position in its own bucket and check if it was selected. -/
def lookup (P : PackingData V U) (v : V) : Option (Fin P.blockCount × U) :=
  let u := P.label v
  let n := (P.bucket u).idxOf v
  if h : n < P.blockCount then some (⟨n, h⟩, u) else none

@[simp] theorem lookup_at (P : PackingData V U) (i : Fin P.blockCount) (u : U) :
    P.lookup (P.vertexAt i u) = some (i, u) := by
  dsimp only [lookup]
  rw [P.label_at i u]
  have hi : (P.bucket u).idxOf (P.vertexAt i u) = i.val :=
    List.get_idxOf (P.bucket_nodup u) _
  simp only [hi, dite_eq_left i.isLt]

theorem lookup_sound (P : PackingData V U) (v : V) (z : Fin P.blockCount × U)
    (h : P.lookup v = some z) : P.vertexAt z.1 z.2 = v := by
  dsimp only [lookup] at h
  split at h
  next hlt =>
    have hz := Option.some.inj h
    rw [← hz]
    exact List.idxOf_get _
  next hnot => cases h

/-- The old mathematical interface, now filled by the computed placement. -/
def completeBlocks (P : PackingData V U) : BlockPacking.CompleteBlocks P.label P.blockCount where
  embed := {
    toFun := fun z => P.vertexAt z.1 z.2
    inj' := by
      intro x y h
      have hi := congrArg P.lookup h
      simpa only [lookup_at, Option.some.injEq, Prod.eta] using hi }
  type_eq := P.label_at

@[simp] theorem completeBlocks_apply (P : PackingData V U) (z : Fin P.blockCount × U) :
    P.completeBlocks.embed z = P.vertexAt z.1 z.2 := rfl

/-- Exact correctness specification for the executable inverse lookup. -/
theorem lookup_some_iff (P : PackingData V U) (v : V) (z : Fin P.blockCount × U) :
    P.lookup v = some z ↔ P.completeBlocks.embed z = v := by
  constructor
  · exact P.lookup_sound v z
  · intro h
    rw [← h]
    exact P.lookup_at z.1 z.2

theorem lookup_none_iff (P : PackingData V U) (v : V) :
    P.lookup v = none ↔ v ∉ Set.range P.completeBlocks.embed := by
  constructor
  · intro hn ⟨z, hz⟩
    have hs := (P.lookup_some_iff v z).mpr hz
    rw [hn] at hs
    cases hs
  · intro hn
    cases hl : P.lookup v with
    | none => rfl
    | some z => exact False.elim (hn ⟨z, (P.lookup_some_iff v z).mp hl⟩)

/-- The original vertex order, filtered by executable lookup failure. -/
def leftovers (P : PackingData V U) : List V :=
  P.vertices.values.filter fun v => decide (P.lookup v = none)

theorem leftovers_nodup (P : PackingData V U) : P.leftovers.Nodup :=
  P.vertices.nodup.filter _

@[simp] theorem mem_leftovers (P : PackingData V U) (v : V) :
    v ∈ P.leftovers ↔ v ∉ Set.range P.completeBlocks.embed := by
  simp only [leftovers, List.mem_filter, P.vertices.complete v, true_and, decide_eq_true_eq]
  exact P.lookup_none_iff v

/-- Explicit leftover enumeration, with an `idxOf` inverse. -/
def leftoverEquiv (P : PackingData V U) :
    Fin P.leftovers.length ≃ {v // v ∉ Set.range P.completeBlocks.embed} :=
  listSubtypeEquiv P.leftovers P.leftovers_nodup
    (fun v => v ∉ Set.range P.completeBlocks.embed) P.mem_leftovers

/-- A filter implementation that also counts its label-equality tests. -/
def bucketCounted (P : PackingData V U) (u : U) : List V → List V × ℕ
  | [] => ([], 0)
  | v :: vs =>
    let rest := P.bucketCounted u vs
    (if P.label v = u then v :: rest.1 else rest.1, rest.2 + 1)

omit [DecidableEq V] in
theorem bucketCounted_eq (P : PackingData V U) (u : U) (vs : List V) :
    P.bucketCounted u vs =
      (vs.filter (fun v => decide (P.label v = u)), vs.length) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    by_cases h : P.label v = u <;> simp [bucketCounted, ih, h]

/-- The minimum scan with counters for label tests and minimum comparisons.
This does not charge the cost of evaluating the supplied label function. -/
def minCountCounted (P : PackingData V U) : List U → ℕ × ℕ
  | [] => (P.vertices.values.length, 0)
  | u :: us =>
    let fiber := P.bucketCounted u P.vertices.values
    let rest := P.minCountCounted us
    (min fiber.1.length rest.1, fiber.2 + rest.2 + 1)

omit [DecidableEq V] in
theorem minCountCounted_eq (P : PackingData V U) (us : List U) :
    P.minCountCounted us =
      (P.minCount us, us.length * (P.vertices.values.length + 1)) := by
  induction us with
  | nil => simp [minCountCounted, minCount]
  | cons u us ih =>
    simp [minCountCounted, bucketCounted_eq, ih, minCount, bucket, Nat.add_mul]
    omega

/-- Exactly one vertex scan and one minimum comparison per supplied type. -/
def blockCountCounted (P : PackingData V U) : ℕ × ℕ := P.minCountCounted P.types.values

omit [DecidableEq V] in
theorem blockCountCounted_eq (P : PackingData V U) :
    P.blockCountCounted =
      (P.blockCount, P.types.values.length * (P.vertices.values.length + 1)) :=
  P.minCountCounted_eq P.types.values

section Cardinalities

variable [Fintype V] [Fintype U]

omit [Fintype U] in
theorem bucket_length_eq_count (P : PackingData V U) (u : U) :
    (P.bucket u).length = BlockPacking.count P.label u := by
  simpa only [Fintype.card_fin, BlockPacking.count] using Fintype.card_congr (P.bucketEquiv u)

omit [DecidableEq V] [Fintype V] [Fintype U] in
theorem minCount_lower (P : PackingData V U) (us : List U) (L C : ℚ)
    (hstart : L ≤ C * P.vertices.values.length)
    (heach : ∀ u ∈ us, L ≤ C * (P.bucket u).length) :
    L ≤ C * P.minCount us := by
  induction us with
  | nil => exact hstart
  | cons u us ih =>
    have htail := ih (fun v hv => heach v (List.mem_cons_of_mem u hv))
    have hhead := heach u (by simp)
    dsimp only [minCount]
    rcases le_total (P.bucket u).length (P.minCount us) with h | h
    · rw [min_eq_left h]
      exact hhead
    · rw [min_eq_right h]
      exact htail

/-- The computed minimum and embedding have the same loss guarantee as the
abstract packing theorem. -/
theorem coverage_of_count_lower (P : PackingData V U) (ε : ℚ)
    (hN : 0 < Fintype.card U) (hε : 0 ≤ ε)
    (hlower : ∀ u, (1 - ε) * (Fintype.card V : ℚ) ≤
      (Fintype.card U : ℚ) * BlockPacking.count P.label u) :
    (1 - ε) * (Fintype.card V : ℚ) ≤ (P.blockCount : ℚ) * Fintype.card U := by
  have hstart : (1 - ε) * (Fintype.card V : ℚ) ≤
      (Fintype.card U : ℚ) * P.vertices.values.length := by
    rw [P.vertices.length_eq_card]
    have hNq : (1 : ℚ) ≤ Fintype.card U := by exact_mod_cast hN
    have hD : (0 : ℚ) ≤ Fintype.card V := by positivity
    have hprod := mul_nonneg (sub_nonneg.mpr hNq) hD
    have hloss := mul_nonneg hε hD
    nlinarith
  have heach : ∀ u ∈ P.types.values, (1 - ε) * (Fintype.card V : ℚ) ≤
      (Fintype.card U : ℚ) * (P.bucket u).length := by
    intro u _
    rw [P.bucket_length_eq_count]
    exact hlower u
  simpa only [blockCount, mul_comm (P.minCount P.types.values : ℚ)] using
    P.minCount_lower P.types.values ((1 - ε) * Fintype.card V) (Fintype.card U) hstart heach

theorem coverage_of_deviation_bound (P : PackingData V U) (a ε : ℚ)
    (hN : 0 < Fintype.card U) (hε : 0 ≤ ε)
    (hlarge : (Fintype.card U : ℚ) ^ 3 * a ≤ ε ^ 2 * Fintype.card V)
    (hdev : (∑ u, ((BlockPacking.count P.label u : ℚ) -
      (Fintype.card V : ℚ) / Fintype.card U) ^ 2) ≤
      (Fintype.card U : ℚ) * a * Fintype.card V) :
    (1 - ε) * (Fintype.card V : ℚ) ≤ (P.blockCount : ℚ) * Fintype.card U := by
  apply P.coverage_of_count_lower ε hN hε
  exact SubexpBlockPacking.count_lower_of_deviation_bound (BlockPacking.count P.label)
    (Fintype.card V) a ε hN hε hlarge hdev

/-- The computed leftover list is exactly the earlier mathematical leftover set. -/
theorem leftovers_toFinset (P : PackingData V U) :
    P.leftovers.toFinset = P.completeBlocks.leftovers := by
  ext v
  simp [BlockPacking.CompleteBlocks.leftovers, BlockPacking.CompleteBlocks.covered,
    Set.mem_range]

theorem leftovers_length_add_packed (P : PackingData V U) :
    P.leftovers.length + P.blockCount * Fintype.card U = Fintype.card V := by
  have h := P.completeBlocks.card_leftovers_add_covered
  rw [← P.leftovers_toFinset, List.toFinset_card_of_nodup P.leftovers_nodup,
    BlockPacking.CompleteBlocks.card_covered] at h
  exact h

end Cardinalities

end PackingData

end SubexponentialSAT.Subexp.ConstructivePacking

end OAI.Algorithms
