import OpenAISemiprime.Algorithms.SubexponentialSAT.LeanCompat
import OpenAISemiprime.Algorithms.SubexponentialSAT.SqrtLog.LayoutInterface

namespace OAI.Algorithms

/-! Pullback of a head-coherent incidence layout to the original variables. -/

namespace SubexponentialSAT.SqrtLog.LayoutHeadPullback

open scoped BigOperators
open LayoutPullback LayoutExactBuckets

variable {I V F G O : Type*}
variable [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]
variable [Fintype G] [DecidableEq G] [CommRing O]

/-- The owner map restricted to one original-variable head. -/
def headOwner (owner : I → V) (copyHead : I → G) (head : V → G)
    (hhead : ∀ i, copyHead i = head (owner i)) (g : G) :
    {i : I // copyHead i = g} → {v : V // head v = g} :=
  fun i => ⟨owner i.val, (hhead i.val).symm.trans i.property⟩

theorem sum_subtype_ite {A M : Type*} [Fintype A] [AddCommMonoid M]
    (p : A → Prop) [DecidablePred p] (f : A → M) :
    (∑ a : {a // p a}, f a.val) = ∑ a, if p a then f a else 0 := by
  rw [← Finset.sum_subtype (Finset.univ.filter p) (by simp)]
  exact Finset.sum_filter _ _

omit [DecidableEq I] [Fintype V] [Fintype G] in
/-- Pulling a row back and then restricting its columns to a head is the
same operation as pulling back along the restricted owner map. -/
theorem row_restrict (owner : I → V) (copyHead : I → G) (head : V → G)
    (hhead : ∀ i, copyHead i = head (owner i)) (g : G)
    (a : I → O) (v : {v : V // head v = g}) :
    row owner a v.val =
      row (headOwner owner copyHead head hhead g) (fun i => a i.val) v := by
  classical
  unfold row
  simp only [headOwner, Subtype.ext_iff]
  rw [sum_subtype_ite (fun i => copyHead i = g)
    (fun i => if owner i = v.val then a i else 0)]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : owner i = v.val
  · have hg : copyHead i = g := (hhead i).trans (hi ▸ v.property)
    simp [hi, hg]
  · simp [hi]

/-- An actual copy layout whose head labels are induced by `owner` gives an
original-variable layout. All constraints remain integer fiber sums. -/
noncomputable def pullback {Q R : ℕ} (owner : I → V) (factor : I → F)
    (head : Fin Q → V → G)
    (C : Layout.Data (O := O) (G := G) (id : I → I) factor Q R)
    (hhead : ∀ t i, C.head t i = head t (owner i)) :
    Layout.Data (O := O) (G := G) owner factor Q R where
  node := C.node
  units := C.units
  head := head
  color := C.color
  row := fun i => row owner (C.row i)
  row_origin := by
    intro i v
    apply LayoutPullback.row_origin owner (C.row i) i
    intro j
    simpa [Pi.single_apply, eq_comm] using C.row_origin i j
  row_degree := fun i v => LayoutPullback.row_degree owner (C.row i) R
    (C.row_degree i) v
  rowCount := C.rowCount
  constraints := fun t g => pulledConstraints
    (headOwner owner (C.head t) (head t) (hhead t) g) (C.constraints t g)
  locality := by
    intro t i g hg
    have h := killsIntegerKernel_pullback
      (headOwner owner (C.head t) (head t) (hhead t) g)
      (C.constraints t g)
      (fun j : {j : I // C.head t j = g} => (C.row i j.val).eval (C.node t))
      (C.locality t i g hg)
    convert h using 1
    funext v
    rw [row_eval, row_restrict owner (C.head t) (head t) (hhead t) g]

end SubexponentialSAT.SqrtLog.LayoutHeadPullback

end OAI.Algorithms
