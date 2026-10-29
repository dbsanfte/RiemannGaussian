import OpenAISemiprime.Algorithms.SubexponentialSAT.LeanCompat

namespace OAI.Algorithms

/-!
# Literal incidence pullback

An incidence is sent to its original variable by `owner`. The pullback
duplicates a variable value; the dual operation adds row coefficients on
each fiber. No inverse matrix or new basis is used in these definitions.
-/

namespace SubexponentialSAT.SqrtLog.LayoutPullback

open scoped BigOperators

variable {I V R : Type*} [Fintype I] [Fintype V] [DecidableEq V]

def duplicate (owner : I → V) (x : V → R) : I → R := x ∘ owner

def row [AddCommMonoid R] (owner : I → V) (a : I → R) (v : V) : R :=
  ∑ i, if owner i = v then a i else 0

section Ring

variable [CommRing R]

theorem row_dot (owner : I → V) (a : I → R) (x : V → R) :
    (∑ v, row owner a v * x v) = ∑ i, a i * duplicate owner x i := by
  classical
  simp only [row, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp [duplicate]

omit [Fintype V] in
theorem row_apply_injective (owner : I → V) (hinj : Function.Injective owner)
    (a : I → R) (i : I) : row owner a (owner i) = a i := by
  classical
  simp only [row, hinj.eq_iff]
  simp

omit [Fintype V] in
theorem row_eq_zero (owner : I → V) (a : I → R) (v : V)
    (hv : v ∉ Set.range owner) : row owner a v = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  have hi : owner i ≠ v := fun h => hv ⟨i, h⟩
  simp [hi]

theorem row_right_dot (owner : I → V) (a : V → R) (z : I → R) :
    (∑ v, a v * row owner z v) = ∑ i, a (owner i) * z i := by
  simpa only [duplicate, Function.comp_def, mul_comm] using row_dot owner z a

omit [Fintype V] in
theorem row_map {S : Type*} [CommRing S] (f : R →+* S)
    (owner : I → V) (a : I → R) (v : V) :
    f (row owner a v) = row owner (fun i => f (a i)) v := by
  simp only [row, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

omit [Fintype V] in
theorem row_single [DecidableEq I] (owner : I → V) (i : I) (v : V) :
    row owner (Pi.single i (1 : R)) v = if v = owner i then 1 else 0 := by
  classical
  unfold row
  rw [Finset.sum_eq_single i]
  · simp [eq_comm]
  · intro j _ hji
    simp [ hji]
  · simp

end Ring

section Polynomial

variable [CommRing R]

omit [Fintype V] in
theorem row_eval (owner : I → V) (a : I → Polynomial R) (v : V) (z : R) :
    (row owner a v).eval z = row owner (fun i => (a i).eval z) v := by
  exact row_map (Polynomial.evalRingHom z) owner a v

omit [Fintype V] in
theorem row_origin [DecidableEq I] (owner : I → V)
    (a : I → Polynomial R) (i : I)
    (ha : ∀ j, (a j).eval 0 = (Pi.single i (1 : R) : I → R) j) (v : V) :
    (row owner a v).eval 0 = if v = owner i then 1 else 0 := by
  rw [row_eval]
  simp_rw [ha]
  exact row_single owner i v

omit [Fintype V] in
theorem row_degree (owner : I → V) (a : I → Polynomial R) (d : ℕ)
    (ha : ∀ i, (a i).natDegree ≤ d) (v : V) :
    (row owner a v).natDegree ≤ d := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  by_cases hi : owner i = v
  · simpa [hi] using ha i
  · simp [hi]

theorem row_eval_dot (owner : I → V) (a : I → Polynomial R)
    (z : R) (x : V → R) :
    (∑ v, (row owner a v).eval z * x v) =
      ∑ i, (a i).eval z * duplicate owner x i := by
  simp_rw [row_eval]
  exact row_dot owner (fun i => (a i).eval z) x

end Polynomial

end SubexponentialSAT.SqrtLog.LayoutPullback

end OAI.Algorithms
