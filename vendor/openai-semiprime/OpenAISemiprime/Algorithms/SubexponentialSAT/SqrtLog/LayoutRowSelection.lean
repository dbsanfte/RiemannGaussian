import OpenAISemiprime.Algorithms.SubexponentialSAT.LeanCompat
import OpenAISemiprime.Algorithms.SubexponentialSAT.SqrtLog.LayoutExactBuckets

namespace OAI.Algorithms

/-!
# Selecting actual integer constraint rows

This module isolates the semantic certificate for row selection. A later finite
minor search may produce the certificate; rational spanning is used only before
reduction, so the actual rows and their integer coefficient bounds are retained.
-/

namespace SubexponentialSAT.SqrtLog.LayoutRowSelection

open scoped BigOperators
open LayoutExactBuckets

universe u v

variable {J : Type u} {V : Type v} [Fintype J] [Fintype V]

def rationalRows (C : J → V → ℤ) : J → (V → ℚ) :=
  fun j v => (C j v : ℚ)

omit [Fintype J] [Fintype V] in
theorem rationalRowSpan_of_span_eq {K : Type*} [Fintype K]
    (C : J → V → ℤ) (select : K → J)
    (hspan : Submodule.span ℚ (Set.range (rationalRows C ∘ select)) =
      Submodule.span ℚ (Set.range (rationalRows C))) :
    RationalRowSpan C (fun k => C (select k)) := by
  intro j
  have hj : rationalRows C j ∈
      Submodule.span ℚ (Set.range (rationalRows C ∘ select)) := by
    rw [hspan]
    exact Submodule.subset_span ⟨j, rfl⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hj
  refine ⟨c, fun v => ?_⟩
  have hv := congrFun hc v
  simpa [rationalRows, Function.comp_def] using hv.symm

omit [Fintype V] in
/-- The number of selected actual rows is exactly the rational constraint rank.
No coefficient rescaling and no modular row-space assertion is involved. -/
theorem exists_actual_row_basis (C : J → V → ℤ) :
    ∃ (K : Type u) (_ : Fintype K) (select : K → J),
      Function.Injective select ∧
      RationalRowSpan C (fun k => C (select k)) ∧
      Fintype.card K = Module.finrank ℚ
        (Submodule.span ℚ (Set.range (rationalRows C))) := by
  obtain ⟨K, select, hinj, hspan, hli⟩ :=
    exists_linearIndependent' ℚ (rationalRows C)
  let _ : Fintype K := Fintype.ofInjective select hinj
  refine ⟨K, inferInstance, select, hinj,
    rationalRowSpan_of_span_eq C select hspan, ?_⟩
  rw [← hspan]
  exact (finrank_span_eq_card hli).symm

omit [Fintype J] [Fintype V] in
/-- Any height bound on the original integer rows remains literally true. -/
theorem selected_bound {K : Type*} (C : J → V → ℤ) (select : K → J)
    (W : ℤ) (hC : ∀ j v, |C j v| ≤ W) :
    ∀ k v, |C (select k) v| ≤ W := fun k v => hC (select k) v

end SubexponentialSAT.SqrtLog.LayoutRowSelection

end OAI.Algorithms
