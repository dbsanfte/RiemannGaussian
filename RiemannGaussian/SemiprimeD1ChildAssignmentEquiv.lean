/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ChildPortBijection
import RiemannGaussian.SemiprimeD1PartitionedTensor
import Mathlib.Data.List.NodupEquivFin

/-! # Actual child assignments partition the original two-sided occurrence bits
The local bijection reads the ACTUALLY computed physical pullback cache and
inverts it by literal index search. Its range is the actual acquired colour
fibre, not an advised permutation. Empty children and isolated vertices are
handled without creating or duplicating a Boolean variable.
-/
set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace RiemannGaussian.SemiprimeD1ChildAssignmentEquiv
open scoped BigOperators
open SemiprimeD1ChildPortBijection SemiprimeD1ChildPortPullbackCorrectness
noncomputable section

/-- Original typed real occurrence together with its distinct endpoint side. -/
abbrev Tag {F : ℕ} (arity : Fin F → ℕ) := ((e : Fin F) × Fin (arity e)) × Bool

/-- Actual prepared child cache; no permutation or group-test answer is an input. -/
abbrev acquired (n F r a : ℕ) (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (q : Fin a) (g : Fin r) :=
  SemiprimeD1ChildPortPullback.acquire n F r a arity owner q g

/-- Literal computed original-tag stream in actual child factor-major order. -/
def tags (n F r a : ℕ) (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (q : Fin a) (g : Fin r) : List (Tag arity) :=
  (permutation (acquired n F r a arity owner q g)).value

/-- Proof-side original selected class of an old occurrence endpoint, justified
by the physical activation theorem below; no label function is a runtime input. -/
def colour (n F r a : ℕ) [NeZero r] (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (q : Fin a) (tag : Tag arity) : Fin r :=
  SemiprimeMaterializedScoreEnvironment.denote
    (SemiprimeSourceHistogramHeadOriginal.originalEnv r a
      (SemiprimeD1IncidenceSearch.run n F r a arity owner).value)
    (linkVertex owner tag).val q

/-- Actual cached pullback membership equals the actual original selected class. -/
theorem mem_tags (n F r a : ℕ) [NeZero r] (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (q : Fin a) (g : Fin r) (tag : Tag arity) :
    tag ∈ tags n F r a arity owner q g ↔ colour n F r a arity owner q tag = g := by
  have hmem : tag ∈ tags n F r a arity owner q g ↔
      tag ∈ targetLinks owner (SemiprimeD1ChildActivation.acquire n F r a arity owner q g)
        (originalPairs n F r a arity owner) := (permutation_perm n F r a arity owner q g).mem_iff
  exact hmem.trans ((target_mem n F r a arity owner q g tag).trans
    (SemiprimeD1ChildActivationOriginal.mask_value n F r a arity owner q g (linkVertex owner tag)))

/-- The actual child tag stream contains no duplicate original endpoint. -/
theorem tags_nodup (n F r a : ℕ) [NeZero r] (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (q : Fin a) (g : Fin r) :
    (tags n F r a arity owner q g).Nodup := permutation_nodup n F r a arity owner q g

private theorem filterMap_id_length {A : Type*} (xs : List (Option A)) (hn : none ∉ xs) :
    (xs.filterMap id).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have ht : none ∉ xs := fun h => hn (List.mem_cons_of_mem x h)
    cases x with
    | none => exact False.elim (hn List.mem_cons_self)
    | some x => simpa only [List.filterMap_cons,id_eq,List.length_cons] using congrArg Nat.succ (ih ht)

/-- Actual child scope counts precisely its cached factor-major endpoint records. -/
def scope (n F r a : ℕ) (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (q : Fin a) (g : Fin r) : ℕ :=
  (acquired n F r a arity owner q g).graph.factors.flatten.length

/-- Every actual child variable has exactly one successfully resolved cached tag. -/
theorem tags_length (n F r a : ℕ) [NeZero r] (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (q : Fin a) (g : Fin r) :
    (tags n F r a arity owner q g).length = scope n F r a arity owner q g := by
  change (SemiprimeD1ChildPortBijection.resolveCache (acquired n F r a arity owner q g).links).value.length = _
  rw [resolveCache_value,filterMap_id_length _ (no_missing n F r a arity owner q g)]
  change (SemiprimeD1ChildPortPullback.pull _ _).value.length = _
  rw [SemiprimeD1ChildPortPullback.pull_value,List.length_map]
  rfl

/-- Computed local finite-position bijection onto the actual original colour fibre. -/
def fibreEquiv (n F r a : ℕ) [NeZero r] (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (q : Fin a) (g : Fin r) :
    Fin (tags n F r a arity owner q g).length ≃ {tag // colour n F r a arity owner q tag = g} where
  toFun j := ⟨(tags n F r a arity owner q g)[j.val],
    (mem_tags n F r a arity owner q g _).mp (List.getElem_mem j.isLt)⟩
  invFun tag := ⟨(tags n F r a arity owner q g).idxOf tag.val,
    List.idxOf_lt_length_of_mem ((mem_tags n F r a arity owner q g tag.val).mpr tag.property)⟩
  left_inv j := by
    apply Fin.ext
    exact (tags_nodup n F r a arity owner q g).idxOf_getElem j.val j.isLt
  right_inv tag := by
    apply Subtype.ext
    exact List.getElem_idxOf (List.idxOf_lt_length_of_mem
      ((mem_tags n F r a arity owner q g tag.val).mpr tag.property))

/-- The actual graph's variable positions are exactly the actual computed colour fibre. -/
def childEquiv (n F r a : ℕ) [NeZero r] (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (q : Fin a) (g : Fin r) :
    Fin (scope n F r a arity owner q g) ≃ {tag // colour n F r a arity owner q tag = g} :=
  (finCongr (tags_length n F r a arity owner q g).symm).trans (fibreEquiv n F r a arity owner q g)

/-- The forward bijection reads the literal computed tag at that child position. -/
theorem childEquiv_value (n F r a : ℕ) [NeZero r] (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (q : Fin a) (g : Fin r)
    (j : Fin (scope n F r a arity owner q g)) :
    (childEquiv n F r a arity owner q g j).val =
      (tags n F r a arity owner q g)[j.val]'(by rw [tags_length]; exact j.isLt) := rfl

/-- The inverse is the actual native index search in the computed cache. -/
theorem childEquiv_inverse (n F r a : ℕ) [NeZero r] (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (q : Fin a) (g : Fin r)
    (tag : {tag // colour n F r a arity owner q tag = g}) :
    ((childEquiv n F r a arity owner q g).symm tag).val =
      (tags n F r a arity owner q g).idxOf tag.val := rfl

/-- Local Boolean assignment transport uses the computed forward and index-search inverse. -/
def localAssignments (n F r a : ℕ) [NeZero r] (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (q : Fin a) (g : Fin r) :
    ({tag // colour n F r a arity owner q tag = g} → Bool) ≃
      (Fin (scope n F r a arity owner q g) → Bool) where
  toFun bits j := bits (childEquiv n F r a arity owner q g j)
  invFun bits tag := bits ((childEquiv n F r a arity owner q g).symm tag)
  left_inv bits := by
    funext tag
    exact congrArg bits ((childEquiv n F r a arity owner q g).apply_symm_apply tag)
  right_inv bits := by
    funext j
    exact congrArg bits ((childEquiv n F r a arity owner q g).symm_apply_apply j)

/-- ALL original two-sided real-occurrence assignments biject with independent
assignments of the ACTUAL physical child graphs, one per acquired group. -/
def assignments (n F r a : ℕ) [NeZero r] (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (q : Fin a) :
    (Tag arity → Bool) ≃ ((g : Fin r) → Fin (scope n F r a arity owner q g) → Bool) :=
  (SemiprimeD1PartitionedTensor.assignments (colour n F r a arity owner q)).trans
    (Equiv.piCongrRight (localAssignments n F r a arity owner q))

/-- The global assignment view reads the exact original tag resolved at that
actual child position; it never changes an endpoint side or parallel port. -/
theorem assignments_value (n F r a : ℕ) [NeZero r] (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (q : Fin a) (bits : Tag arity → Bool)
    (g : Fin r) (j : Fin (scope n F r a arity owner q g)) :
    assignments n F r a arity owner q bits g j =
      bits (childEquiv n F r a arity owner q g j).val := rfl

/-- Complete finite assignment sums factor over the ACTUAL acquired child scopes,
not hypothetical independent bit blocks of an advised projection. -/
theorem sum_product {R : Type*} [CommRing R] (n F r a : ℕ) [NeZero r] (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (q : Fin a)
    (term : (g : Fin r) → (Fin (scope n F r a arity owner q g) → Bool) → R) :
    (∑ bits : Tag arity → Bool, ∏ g, term g (assignments n F r a arity owner q bits g)) =
      ∏ g, ∑ bits : Fin (scope n F r a arity owner q g) → Bool, term g bits := by
  classical
  rw [← (assignments n F r a arity owner q).symm.sum_comp]
  simp only [Equiv.apply_symm_apply]
  exact (Fintype.prod_sum term).symm

end
end RiemannGaussian.SemiprimeD1ChildAssignmentEquiv
