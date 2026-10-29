/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PacketPolynomialWeight

/-! # Actual packet recipes evaluated through the acquired weighted menu
All possibly useful mode coefficients are covered by the actual enumerator.
The polynomial below is an erased specification of concrete recipes, never
a runtime polynomial/matrix input or a coefficient supplier.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace RiemannGaussian.SemiprimeD1PacketPolynomialAcquired
open scoped BigOperators
open SemiprimeD1JetAxes SemiprimeD1JetInterpretation
open SemiprimeD1PacketEntryInputs SemiprimeD1PacketEntryBits
open SemiprimeD1PacketModeProjection SemiprimeD1PacketPolynomialWeight
open SemiprimeD1SeparatedCoefficient
noncomputable section

/-- Actual acquired target masks contain no index beyond the acquired cache. -/
theorem targetSet_finite (cache : SemiprimeD1PacketModeMask.Cache) :
    targetSet cache ⊆ {j | j < cache.items.length} := by
  intro j hj
  change j < cache.items.length
  by_contra hn
  have hz : cache.items[j]? = none := List.getElem?_eq_none (by omega)
  change targetEnabled cache.items j = true at hj
  simp only [targetEnabled, hz, Bool.false_eq_true] at hj

/-- Erased polynomial specification of the actual physically acquired row recipes. -/
def polynomial (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (a : ℕ) (i : Fin a) (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (columns rows : List (Wire a)) (cache : SemiprimeD1PacketModeMask.Cache) :
    MvPolynomial ℕ (Carrier ctx) :=
  SemiprimeD1AffineCoefficient.polynomial cache.items.length
    ((recipes ctx z a i t columns cache.items rows).value.map
      (SemiprimeD1JetAffineCoefficient.rowValue ctx))

/-- Every actual polynomial mode index lies in the literal acquired cache. -/
theorem polynomial_finite (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (a : ℕ) (i : Fin a) (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (columns rows : List (Wire a)) (cache : SemiprimeD1PacketModeMask.Cache) :
    On {j | j < cache.items.length} (polynomial ctx z a i t columns rows cache) :=
  on_mono _ _ (targetSet_finite cache) _
    (SemiprimeD1PacketPolynomialSupport.packet_polynomial_on ctx z a i t columns rows cache)

/-- The ACTUAL weighted-menu execution covers the entire useful evaluation of
the ACTUAL acquired packet recipes. Weights, support, finite shape and modular
nilpotence are derived; only the original grid/node conditions are premises. -/
theorem eval_acquired (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (a : ℕ) (i : Fin a) (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (columns rows : List (Wire a)) (cache : SemiprimeD1PacketModeMask.Cache)
    (hpos : ctx.Positive) (hp : 0 < ctx.precision)
    (ht : SemiprimeD1WireKernelOriginal.point a t.val ≠ 0)
    (hi : padicValInt 2 (SemiprimeD1WireKernelOriginal.point a t.val) = i.val)
    (values : ℕ → Carrier ctx) :
    MvPolynomial.eval values (polynomial ctx z a i t columns rows cache) =
      ((SemiprimeD1WeightedTuples.acquire (weights cache) (ctx.precision-1)).values.map
        (fun beta => (polynomial ctx z a i t columns rows cache).coeff beta.toFinsupp *
          beta.toFinsupp.prod (fun j exponent => values j ^ exponent))).sum := by
  apply SemiprimeD1AcquiredModeSum.eval_acquired (weights cache) _ ctx.precision hp _
    (packet_polynomial_weighted ctx z a i t columns rows cache hpos hp ht hi) _
    (SemiprimeD1JetAlgebra.constants (SemiprimeD1JetBoxIndex.dims ctx.axes))
  · intro w hw
    obtain ⟨item, _, rfl⟩ := List.mem_map.mp hw
    omega
  · simpa only [weights, List.length_map, polynomial] using polynomial_finite ctx z a i t columns rows cache

end
end RiemannGaussian.SemiprimeD1PacketPolynomialAcquired
