import OpenAISemiprime.Algorithms.SubexponentialSAT.LeanCompat
import OpenAISemiprime.Algorithms.SubexponentialSAT.SqrtLog.LayoutExactBuckets
import OpenAISemiprime.Algorithms.SubexponentialSAT.SubexpRowInterpolation

namespace OAI.Algorithms

/-!
# Exact integer-bucket interface for the new incidence layout

This interface does not assert existence or a running time. Concrete
construction is assembled from the new packing, integer numerator, and
incidence-pullback modules. Unlike the old residue-only interface, its
locality conclusion is an exact equality in the coefficient ring.
-/

namespace SubexponentialSAT.SqrtLog.Layout

open scoped BigOperators
open LayoutExactBuckets

variable {V I F G O : Type*}
variable [Fintype V] [DecidableEq V] [Fintype G] [DecidableEq G]
variable [CommRing O]

structure Data (owner : I → V) (factor : I → F) (Q R : ℕ) where
  node : Fin Q → O
  units : SubexponentialSAT.SubexpRowInterpolation.NodeUnits node
  head : Fin Q → V → G
  color : F → Fin Q → G
  row : I → V → Polynomial O
  row_origin : ∀ i v, (row i v).eval 0 = if v = owner i then 1 else 0
  row_degree : ∀ i v, (row i v).natDegree ≤ R
  rowCount : Fin Q → G → ℕ
  constraints : (t : Fin Q) → (g : G) → Fin (rowCount t g) →
    {v : V // head t v = g} → ℤ
  locality : ∀ (t : Fin Q) (i : I) (g : G), g ≠ color (factor i) t →
    KillsIntegerKernel
      (fun v : {v : V // head t v = g} => (row i v.val).eval (node t))
      (constraints t g)

namespace Data

variable {owner : I → V} {factor : I → F} {Q R : ℕ}
variable (L : Data (O := O) (G := G) owner factor Q R)

abbrev Head (t : Fin Q) (g : G) := {v : V // L.head t v = g}

def restrict (t : Fin Q) (g : G) (x : V → ℤ) : L.Head t g → ℤ :=
  fun v => x v.val

def bucketLabel (t : Fin Q) (g : G) (x : L.Head t g → ℤ) :
    Fin (L.rowCount t g) → ℤ := signature (L.constraints t g) x

def localValue (t : Fin Q) (i : I) (g : G) (x : L.Head t g → ℤ) : O :=
  value (fun v : L.Head t g => (L.row i v.val).eval (L.node t)) x

def nodeValue (t : Fin Q) (i : I) (x : V → ℤ) : O :=
  value (fun v => (L.row i v).eval (L.node t)) x

theorem nodeValue_eq_sum (t : Fin Q) (i : I) (x : V → ℤ) :
    L.nodeValue t i x = ∑ g, L.localValue t i g (L.restrict t g x) := by
  exact (Fintype.sum_fiberwise (L.head t)
    (fun v => (L.row i v).eval (L.node t) * (x v : O))).symm

omit [Fintype G] in
/-- A foreign local contribution is constant on its actual integer bucket,
with equality in the entire coefficient ring, not only its residue field. -/
theorem localValue_eq (t : Fin Q) (i : I) (g : G)
    (hg : g ≠ L.color (factor i) t) (x y : L.Head t g → ℤ)
    (hxy : L.bucketLabel t g x = L.bucketLabel t g y) :
    L.localValue t i g x = L.localValue t i g y :=
  value_eq_of_signature_eq _ _ (L.locality t i g hg) x y hxy

/-- Keeping the owned head fixed and all other bucket labels fixed keeps
the actual incidence-row evaluation fixed. -/
theorem nodeValue_eq_of_buckets (t : Fin Q) (i : I) (x y : V → ℤ)
    (hown : L.restrict t (L.color (factor i) t) x =
      L.restrict t (L.color (factor i) t) y)
    (hother : ∀ g, g ≠ L.color (factor i) t →
      L.bucketLabel t g (L.restrict t g x) =
        L.bucketLabel t g (L.restrict t g y)) :
    L.nodeValue t i x = L.nodeValue t i y := by
  rw [L.nodeValue_eq_sum, L.nodeValue_eq_sum]
  apply Finset.sum_congr rfl
  intro g _
  by_cases hg : g = L.color (factor i) t
  · subst g
    rw [hown]
  · exact L.localValue_eq t i g hg _ _ (hother g hg)

end Data

end SubexponentialSAT.SqrtLog.Layout

end OAI.Algorithms
