/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1OriginalPacketKernelRows
import RiemannGaussian.SemiprimeD1NetworkDoubleAssignment

/-! # Actual literal-network deformation equals the original packet polynomial sum
Every packet/group polynomial and source value is acquired from the actual
original sparse replay and one common original X/Y endpoint assignment. This
is the deformation-to-mode-polynomial identity; coefficient separation and
independent child contractions are separate subsequent steps.
-/
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace RiemannGaussian.SemiprimeD1NetworkPacketPolynomial
open scoped BigOperators
open SemiprimeD1TensorNetwork SemiprimeD1JetAxes SemiprimeD1JetInterpretation
open SemiprimeD1JetAlgebra SemiprimeD1JetBoxIndex SemiprimeD1JetScalarMap SemiprimeD1DyadicInteger
open SemiprimeD1LeafCounter SemiprimeD1NetworkIntegralDeformation
open SemiprimeD1PacketAssignmentRows SemiprimeD1ChildAssignmentEndpoint
open SemiprimeD1PacketRowProducts SemiprimeD1AllPacketRowProducts SemiprimeD1OriginalPacketKernelRows
noncomputable section

/-- The exact original occurrence assignment type of the ACTUAL network. -/
abbrev Bits (net : Network) (r a : ℕ) :=
  Fin (SemiprimeD1PacketReplayOriginal.acquire net.leftCount net.rows.length r a
    (arity net.rows) (owner net.rows)).placements.length→Bool

/-- Closed original-network deformation/actual-mode-polynomial identity. The
coefficient map preserves constants (proved for the actual fresh-axis map),
not arbitrary source tables, row lists, polynomials or source values. -/
theorem network_packet_polynomial (axes : List ℕ) (ctx : Context)
    (f : Algebra (dims axes) (ZMod (2^ctx.precision))→+*Carrier ctx)
    (hconstants : f.comp (constants (dims axes))=constants (dims ctx.axes))
    (z : SemiprimeD1JetAffineCoefficient.JetRun) (net : Network) (r a u p : ℕ) [NeZero r]
    (i : Fin a) (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (hprecision : ctx.precision=(SemiprimeD1GlobalModeFibres.node net.leftCount net.rows.length r a u p
      (arity net.rows) (owner net.rows) i).precision)
    (hpos : ctx.Positive) (hp : 0<ctx.precision) (ht : SemiprimeD1WireKernelOriginal.point a t.val≠0)
    (hi : padicValInt 2 (SemiprimeD1WireKernelOriginal.point a t.val)=i.val) :
    ((networkPolynomial axes net.leftCount net.rows.length r a (arity net.rows) (owner net.rows) t
      net.left.toList net.right.toList).map (scalarMap (dims axes) (reduction ctx.precision))).eval₂ f (interpret ctx z.words)=
      ∑x : Bits net r a,∑y : Bits net r a,
        f ((net.right.toList.map (fun v => interpret ⟨axes,ctx.precision⟩
          (SemiprimeD1TensorTables.valueAt v.table (localAssignment x v)))).prod)*
        f ((net.left.toList.map (fun v => interpret ⟨axes,ctx.precision⟩
          (SemiprimeD1TensorTables.valueAt v.table (localAssignment y v)))).prod)*
        MvPolynomial.eval
          (SemiprimeD1PacketSourceVector.values ctx net.leftCount net.rows.length r a (ctx.precision-1)
            (arity net.rows) (owner net.rows) i
            (originalEndpointBit net.leftCount net.rows.length r a (arity net.rows) (owner net.rows)
              (tagBits net.leftCount net.rows.length r a (arity net.rows) (owner net.rows) x y)))
          (∏packet : Fin (SemiprimeD1PacketReplayOriginal.acquire net.leftCount net.rows.length r a
            (arity net.rows) (owner net.rows)).state.packets.length,
            ∏g : Fin r,packetPolynomial ctx z net.leftCount net.rows.length r a u p
              (arity net.rows) (owner net.rows) i packet g
              (originalEndpointBit net.leftCount net.rows.length r a (arity net.rows) (owner net.rows)
                (tagBits net.leftCount net.rows.length r a (arity net.rows) (owner net.rows) x y)) t) := by
  classical
  rw [SemiprimeD1NetworkDoubleAssignment.network_double_sum]
  simp_rw [hconstants]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  rw [all_packet_eval ctx z net.leftCount net.rows.length r a u p (arity net.rows) (owner net.rows) i _ t
    hprecision hpos hp ht hi]
  apply Finset.prod_congr rfl
  intro j _
  exact (wireRow_kernel ctx z net.leftCount net.rows.length r a (arity net.rows) (owner net.rows) i
    ⟨0,NeZero.pos r⟩ x y j t hpos hp).symm

end
end RiemannGaussian.SemiprimeD1NetworkPacketPolynomial
