/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PackedMomentPrecision
import RiemannGaussian.SemiprimeD1PackedMomentSemiprime
import RiemannGaussian.SemiprimePublicAcquiredExecution
/-! # Exact weighted public reindexing before the final scalar reduction
The full natural contraction retains every higher moment. These identities
use the original public vertex and wire enumerations; they add no evaluator
or supplied scalar to the finite source.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
noncomputable section
namespace RiemannGaussian.SemiprimeD1PackedNetworkReindex
open scoped BigOperators
open SemiprimePublicAcquiredExecution SemiprimeMacroGraph SemiprimeMacroGraphSemantics SemiprimeMacroParameters
open SemiprimeD1PackedMomentOriginal SemiprimeD1PackedMomentPrecision
attribute [local instance] Classical.propDecidable
/-- The actual finite wire and vertex enumerations preserve arbitrary local weights. -/
theorem indexed_sum {R : Type*} [CommSemiring R] (N : ℕ) (hN : 0<N)
    (table : (v : PublicVertex N)→(Fin (subdividedArity v)→Bool)→R) :
    (∑a : Fin (wireCount N)→Bool,∏e : Fin (factorCount N),
      table ((vertexEnumeration N).equivFin e) (fun i => a (indexedCoordinate N hN e i)))=
      ∑a : PublicEdge N→Bool,∏v : PublicVertex N,
        table v (fun i => a (SemiprimeScheduledCounter.publicCoordinate (bitLength_pos hN) v i)) := by
  apply Fintype.sum_equiv (assignmentEquiv N)
  intro a
  exact (vertexEnumeration N).equivFin.prod_comp
    (fun v => table v (fun i => a ((edgeEnumeration N).equivFin.symm
      (SemiprimeScheduledCounter.publicCoordinate (bitLength_pos hN) v i))))
/-- Exact natural coefficient casts at every target semiring, without early truncation. -/
theorem coefficient_cast {R : Type*} [CommSemiring R] (N : ℕ) (hN : 0<N)
    (v : PublicVertex N) (input : Fin (subdividedArity v)→Bool) :
    (coefficient N hN v input : R)=
      markedTable (SemiprimePublicFactorCount.publicConfig N hN) ((2^bitLength N : ℕ) : R) v input := by
  unfold coefficient markedTable
  split <;> simp only [Nat.cast_add,Nat.cast_one,Nat.cast_mul,Nat.cast_zero]
/-- Full indexed natural contraction, including ALL higher powers of the marker. -/
def full (N : ℕ) (hN : 0<N) : ℕ :=
  ∑a : Fin (wireCount N)→Bool,∏e : Fin (factorCount N),
    coefficient N hN ((vertexEnumeration N).equivFin e) (fun i => a (indexedCoordinate N hN e i))
/-- Cast finite sums and products before inserting concrete public metadata. -/
theorem cast_sum_product {R I J : Type*} [CommSemiring R] [Fintype I] [Fintype J]
    (f : I→J→ℕ) : ((∑i,∏j,f i j : ℕ) : R)=∑i,∏j,(f i j : R) := by
  simp only [Nat.cast_sum,Nat.cast_prod]
/-- Full natural contraction is the same original weighted public graph, over ANY semiring. -/
theorem cast_full {R : Type*} [CommSemiring R] (N : ℕ) (hN : 0<N) :
    (full N hN : R)=contraction (SemiprimePublicFactorCount.publicConfig N hN) ((2^bitLength N : ℕ) : R) := by
  unfold full
  rw [cast_sum_product]
  refine Eq.trans ?_ (indexed_sum N hN
    (markedTable (SemiprimePublicFactorCount.publicConfig N hN) ((2^bitLength N : ℕ) : R)))
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.prod_congr rfl
  intro e _
  exact coefficient_cast N hN ((vertexEnumeration N).equivFin e) (fun i => a (indexedCoordinate N hN e i))
/-- A proved equality of final moduli preserves the decoded residue of the SAME integer. -/
theorem val_modulus (a p q : ℕ) (h : p=q) :
    (a : ZMod p).val=(a : ZMod q).val := by cases h;rfl
/-- The actual public 2ell-bit scalar readout is obtained ONLY at this final reduction. -/
theorem packed_value (N : ℕ) (hN : 0<N) :
    ((full N hN : ZMod (2^precision N))).val=SemiprimeD1PackedMomentSemiprime.packedValue N hN := by
  calc
    _ = (full N hN : ZMod ((2^bitLength N)^2)).val := val_modulus _ _ _ (modulus N)
    _ = _ := congrArg ZMod.val (cast_full (R:=ZMod ((2^bitLength N)^2)) N hN)
end RiemannGaussian.SemiprimeD1PackedNetworkReindex
