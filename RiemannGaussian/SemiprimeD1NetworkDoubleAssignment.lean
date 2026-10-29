/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1NetworkIntegralDeformation
import RiemannGaussian.SemiprimeD1TensorNetworkLayout
import RiemannGaussian.SemiprimeD1JetEmbedding

/-! # Actual literal-network deformation as two original endpoint assignments
Individual current entries are reduced separately before their products. The
wire forms use original acquired sparse placements, not an advised matrix.
-/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace RiemannGaussian.SemiprimeD1NetworkDoubleAssignment
open scoped BigOperators
open SemiprimeD1TensorNetwork SemiprimeD1JetAlgebra SemiprimeD1JetBoxIndex
open SemiprimeD1JetScalarMap SemiprimeD1DyadicInteger SemiprimeD1OriginalDeformation
open SemiprimeD1LeafCounter SemiprimeD1NetworkIntegralDeformation
noncomputable section

/-- The actual quotient embedding preserves coefficient constants, including
all old nilpotent coordinates. No higher-precision ring lift is used. -/
theorem outerEmbedding_constants {R : Type*} [CommRing R] {m : ℕ}
    (q : ℕ) (ds : Fin m→ℕ) (c : R) :
    SemiprimeD1JetAlgebra.outerEmbedding q ds (constants ds c)=
      constants (SemiprimeD1JetAlgebra.outerDims q ds) c := by
  change SemiprimeD1JetAlgebra.outerEmbedding q ds (project ds (MvPowerSeries.C c))=
    project (SemiprimeD1JetAlgebra.outerDims q ds) (MvPowerSeries.C c)
  rw [SemiprimeD1JetAlgebra.outerEmbedding_project,MvPowerSeries.rename_C]

/-- Constants square for the actual same-precision fresh-axis embedding. -/
theorem outerEmbedding_constants_comp {R : Type*} [CommRing R] {m : ℕ}
    (q : ℕ) (ds : Fin m→ℕ) :
    (SemiprimeD1JetAlgebra.outerEmbedding (R:=R) q ds).comp (constants ds)=
      constants (SemiprimeD1JetAlgebra.outerDims q ds) := by
  ext c
  exact outerEmbedding_constants q ds c

/-- Original modular local deformation of the actual network's literal caches
is the finite X/Y sum with its full original acquired kernel row product. -/
theorem network_double_sum {S : Type*} [CommRing S] (axes : List ℕ) (p : ℕ)
    (f : Algebra (dims axes) (ZMod (2^p))→+*S) (z : S)
    (net : Network) (r a : ℕ) [NeZero r]
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) :
    ((networkPolynomial axes net.leftCount net.rows.length r a (arity net.rows) (owner net.rows) t
      net.left.toList net.right.toList).map (scalarMap (dims axes) (reduction p))).eval₂ f z=
      ∑x : Fin (Placements net.leftCount net.rows.length r a (arity net.rows) (owner net.rows)).length→Bool,
      ∑y : Fin (Placements net.leftCount net.rows.length r a (arity net.rows) (owner net.rows)).length→Bool,
        f ((net.right.toList.map (fun v => SemiprimeD1JetInterpretation.interpret ⟨axes,p⟩
          (SemiprimeD1TensorTables.valueAt v.table (localAssignment x v)))).prod)*
        f ((net.left.toList.map (fun v => SemiprimeD1JetInterpretation.interpret ⟨axes,p⟩
          (SemiprimeD1TensorTables.valueAt v.table (localAssignment y v)))).prod)*
        ∏i, (if y i then
          (∑j,(if packet net.leftCount net.rows.length r a (arity net.rows) (owner net.rows) i=
              packet net.leftCount net.rows.length r a (arity net.rows) (owner net.rows) j then
            SemiprimeD1UniversalModeData.entryValue p (f.comp (constants (dims axes))) z
              (SemiprimeD1WireKernelOriginal.acquireOriginal a t
                (slot net.leftCount net.rows.length r a (arity net.rows) (owner net.rows) i)
                (slot net.leftCount net.rows.length r a (arity net.rows) (owner net.rows) j)) else 0)*
            SemiprimeStreamingTensor.bit (x j))
          else 1-(∑j,(if packet net.leftCount net.rows.length r a (arity net.rows) (owner net.rows) i=
              packet net.leftCount net.rows.length r a (arity net.rows) (owner net.rows) j then
            SemiprimeD1UniversalModeData.entryValue p (f.comp (constants (dims axes))) z
              (SemiprimeD1WireKernelOriginal.acquireOriginal a t
                (slot net.leftCount net.rows.length r a (arity net.rows) (owner net.rows) i)
                (slot net.leftCount net.rows.length r a (arity net.rows) (owner net.rows) j)) else 0)*
            SemiprimeStreamingTensor.bit (x j))) := by
  classical
  rw [network_modular_contraction]
  apply Finset.sum_congr rfl
  intro x _
  rw [SemiprimeStreamingTensor.evaluate_eq_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  exact (mul_assoc _ _ _).symm

end
end RiemannGaussian.SemiprimeD1NetworkDoubleAssignment
