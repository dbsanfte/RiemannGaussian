/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PacketCatalogueReindex

/-! # Evaluation of an actual acquired affine row
This expands the erased specification of the executed row recipe into its
actual acquired base and actual acquired coefficient vector. No row-value
callback, coefficient table or evaluation answer is assumed.
-/
set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace RiemannGaussian.SemiprimeD1PacketAffineRowEvaluation
open scoped BigOperators
open SemiprimeD1PacketEntryInputs SemiprimeD1PacketEntryBits
open SemiprimeD1PacketEntryValue SemiprimeD1JetAxes SemiprimeD1JetInterpretation
noncomputable section

/-- Literal range-list sum equals its complete finite-index scan. -/
theorem range_sum {A : Type*} [AddCommMonoid A] (K : ℕ) (f : ℕ→A) :
    ((List.range K).map f).sum=∑j : Fin K,f j.val := by
  rw [←List.sum_toFinset f List.nodup_range,List.toFinset_range,Fin.sum_univ_eq_sum_range]

/-- Exact evaluation of a finite affine row, including its constant term. -/
theorem rowPolynomial_eval {R : Type*} [CommRing R] (K : ℕ)
    (row : SemiprimeD1AffineCoefficient.Row R) (values : ℕ→R) :
    MvPolynomial.eval values (SemiprimeD1AffineCoefficient.rowPolynomial K row)=
      row.base+∑j : Fin K,row.coefficients.getD j.val 0*values j.val := by
  unfold SemiprimeD1AffineCoefficient.rowPolynomial
  rw [map_add,map_list_sum]
  simp only [MvPolynomial.eval_C,List.map_map,Function.comp_def,MvPolynomial.eval_mul,MvPolynomial.eval_X]
  rw [range_sum]

/-- An actual physical row recipe evaluates using its literal acquired mode
coefficients in their original global vector order. -/
theorem recipe_eval (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (a : ℕ) (i : Fin a) (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (row : Wire a) (columns : List (Wire a)) (cache : SemiprimeD1PacketModeMask.Cache)
    (values : ℕ→Carrier ctx) :
    MvPolynomial.eval values
      (SemiprimeD1AffineCoefficient.rowPolynomial cache.items.length
        (SemiprimeD1JetAffineCoefficient.rowValue ctx (recipe ctx z a i t row columns cache.items).value))=
      interpret ctx (rowBase ctx z a t row columns).words+
        ∑j : Fin cache.items.length,
          interpret ctx (coefficient ctx z a i t row cache.items[j.val]).words*values j.val := by
  rw [rowPolynomial_eval]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  change ((coefficients ctx z a i t row cache.items).value.map (interpret ctx)).getD j.val 0*values j.val=_
  rw [coefficients_value,List.map_map]
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using j.isLt),List.getElem_map]
  rfl

/-- The actual descriptor cache is the literal acquired global catalogue with
its executed classifier applied once per label, preserving original order. -/
theorem fromModes_items {n F r a : ℕ} {arity : Fin F→ℕ}
    (source : SemiprimeD1OriginalModeAcquisition.Acquired n F a arity)
    (packet : Fin source.packets.state.packets.length) (i : Fin a) (g : Fin r) :
    (SemiprimeD1PacketModeMask.fromModes source packet i g).items=
      (SemiprimeD1ModeCatalog.catalog (source.packets.state.packets.length*2^(i.val+1))
        (source.precision-1)).map (SemiprimeD1PacketModeMask.acquireOne source.packets packet i
          (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits) := by
  unfold SemiprimeD1PacketModeMask.fromModes
  dsimp only
  rw [SemiprimeD1PacketModeMask.scan_items,SemiprimeD1ModeCatalog.acquireCatalog_value]


end
end RiemannGaussian.SemiprimeD1PacketAffineRowEvaluation
