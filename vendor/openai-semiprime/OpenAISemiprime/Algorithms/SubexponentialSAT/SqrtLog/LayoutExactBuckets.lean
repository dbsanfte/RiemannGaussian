import OpenAISemiprime.Algorithms.SubexponentialSAT.LeanCompat
import OpenAISemiprime.Algorithms.SubexponentialSAT.SqrtLog.LayoutPullback

namespace OAI.Algorithms

/-!
# Exact integer signatures survive every coefficient-ring reduction

The assignments in this module are integer vectors. In the counting
application they are Boolean vectors or differences of Boolean vectors.
Equality of signatures is an equality in `ℤ`, before any reduction.
No claim about the kernel of a matrix reduced modulo a prime is used.
-/

namespace SubexponentialSAT.SqrtLog.LayoutExactBuckets

open scoped BigOperators
open LayoutPullback

variable {V J R : Type*} [Fintype V] [CommRing R]

def signature (A : J → V → ℤ) (x : V → ℤ) (j : J) : ℤ :=
  ∑ v, A j v * x v

def value (a : V → R) (x : V → ℤ) : R :=
  ∑ v, a v * (x v : R)

def KillsIntegerKernel (a : V → R) (A : J → V → ℤ) : Prop :=
  ∀ z : V → ℤ, (∀ j, signature A z j = 0) → value a z = 0

theorem signature_sub (A : J → V → ℤ) (x y : V → ℤ) (j : J) :
    signature A (x - y) j = signature A x j - signature A y j := by
  simp [signature, mul_sub, Finset.sum_sub_distrib]

theorem value_sub (a : V → R) (x y : V → ℤ) :
    value a (x - y) = value a x - value a y := by
  simp [value, mul_sub, Finset.sum_sub_distrib]

theorem value_eq_of_signature_eq (a : V → R) (A : J → V → ℤ)
    (ha : KillsIntegerKernel a A) (x y : V → ℤ)
    (hxy : signature A x = signature A y) : value a x = value a y := by
  apply sub_eq_zero.mp
  rw [← value_sub]
  apply ha
  intro j
  rw [signature_sub, congrFun hxy j, sub_self]

section Pullback

variable {I : Type*} [Fintype I] [DecidableEq V]

def pulledConstraints (owner : I → V) (C : J → I → ℤ) : J → V → ℤ :=
  fun j => row owner (C j)

theorem signature_pullback (owner : I → V) (C : J → I → ℤ)
    (x : V → ℤ) (j : J) :
    signature (pulledConstraints owner C) x j =
      signature C (duplicate owner x) j :=
  row_dot owner (C j) x

theorem value_pullback (owner : I → V) (a : I → R) (x : V → ℤ) :
    value (row owner a) x = value a (duplicate owner x) := by
  exact row_dot owner a (fun v => (x v : R))

theorem killsIntegerKernel_pullback (owner : I → V)
    (C : J → I → ℤ) (a : I → R) (ha : KillsIntegerKernel a C) :
    KillsIntegerKernel (row owner a) (pulledConstraints owner C) := by
  intro z hz
  rw [value_pullback]
  apply ha
  intro j
  rw [← signature_pullback]
  exact hz j

/-- A concrete copy row remains exactly constant on the pulled-back buckets.
This is literal incidence duplication, with no inverse or field hypothesis. -/
theorem value_eq_on_pulled_bucket (owner : I → V)
    (C : J → I → ℤ) (a : I → R) (ha : KillsIntegerKernel a C)
    (x y : V → ℤ)
    (hxy : signature (pulledConstraints owner C) x =
      signature (pulledConstraints owner C) y) :
    value (row owner a) x = value (row owner a) y :=
  value_eq_of_signature_eq _ _ (killsIntegerKernel_pullback owner C a ha) x y hxy

end Pullback

section RationalRowReduction

variable {J' : Type*} [Fintype J']

/-- The selected rows rationally span every original integer row. This
condition can be verified over `ℚ`; it is never asserted after reduction. -/
def RationalRowSpan (C : J → V → ℤ) (A : J' → V → ℤ) : Prop :=
  ∀ j, ∃ c : J' → ℚ, ∀ v, (C j v : ℚ) = ∑ k, c k * (A k v : ℚ)

theorem integer_kernel_of_rational_span (C : J → V → ℤ) (A : J' → V → ℤ)
    (hspan : RationalRowSpan C A) (z : V → ℤ)
    (hz : ∀ j, signature A z j = 0) : ∀ j, signature C z j = 0 := by
  intro j
  obtain ⟨c, hc⟩ := hspan j
  have hA (k : J') : ∑ v, (A k v : ℚ) * (z v : ℚ) = 0 := by
    exact_mod_cast hz k
  have hC : ∑ v, (C j v : ℚ) * (z v : ℚ) = 0 := by
    simp_rw [hc, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [mul_assoc, ← Finset.mul_sum, hA, mul_zero]
    simp
  exact_mod_cast hC

/-- Selecting actual independent integer rows is safe for exact integer
buckets in every commutative target ring, including prime-power rings. -/
theorem killsIntegerKernel_of_rational_span
    (C : J → V → ℤ) (A : J' → V → ℤ) (hspan : RationalRowSpan C A)
    (a : V → R) (ha : KillsIntegerKernel a C) : KillsIntegerKernel a A := by
  intro z hz
  exact ha z (integer_kernel_of_rational_span C A hspan z hz)

end RationalRowReduction

end SubexponentialSAT.SqrtLog.LayoutExactBuckets

end OAI.Algorithms
