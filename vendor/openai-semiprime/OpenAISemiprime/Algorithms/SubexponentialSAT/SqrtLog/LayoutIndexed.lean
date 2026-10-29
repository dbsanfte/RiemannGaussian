import OpenAISemiprime.Algorithms.SubexponentialSAT.LeanCompat
import OpenAISemiprime.Algorithms.SubexponentialSAT.SqrtLog.LayoutInterface

namespace OAI.Algorithms

/-! A finite row-indexed constructor for the exact layout interface. -/
namespace SubexponentialSAT.SqrtLog.Layout

open LayoutExactBuckets

variable {V I F G O : Type*}
variable [Fintype V] [DecidableEq V] [Fintype G] [DecidableEq G]
variable [CommRing O]

/-- Reindex a concrete finite integer row family by its exact cardinality.
This changes no row values or bucket equivalence. -/
noncomputable def ofIndexed {owner : I → V} {factor : I → F} {Q R : ℕ}
    (node : Fin Q → O) (units : SubexponentialSAT.SubexpRowInterpolation.NodeUnits node)
    (head : Fin Q → V → G) (color : F → Fin Q → G)
    (row : I → V → Polynomial O)
    (origin : ∀ i v, (row i v).eval 0 = if v = owner i then 1 else 0)
    (degree : ∀ i v, (row i v).natDegree ≤ R)
    (J : Fin Q → G → Type*) [∀ t g, Fintype (J t g)]
    (constraints : (t : Fin Q) → (g : G) → J t g → {v : V // head t v = g} → ℤ)
    (locality : ∀ (t : Fin Q) (i : I) (g : G), g ≠ color (factor i) t →
      KillsIntegerKernel (fun v : {v : V // head t v = g} =>
        (row i v.val).eval (node t)) (constraints t g)) :
    Data (O := O) (G := G) owner factor Q R where
  node := node
  units := units
  head := head
  color := color
  row := row
  row_origin := origin
  row_degree := degree
  rowCount := fun t g => Fintype.card (J t g)
  constraints := fun t g j => constraints t g ((Fintype.equivFin (J t g)).symm j)
  locality := by
    intro t i g hg z hz
    apply locality t i g hg z
    intro j
    simpa [signature] using hz ((Fintype.equivFin (J t g)) j)

end SubexponentialSAT.SqrtLog.Layout

end OAI.Algorithms
