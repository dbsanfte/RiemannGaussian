/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RecursivePhaseControl
import RiemannGaussian.SemiprimeD1NetworkRecoveryLicence

/-! # Actual retained-block D.5 assembly for the concrete controller
One proof-side postcondition concerns the blocks actually returned by phase.
All node/count/precision/read/width and recovery-integrality facts are derived
from original data. No runtime solver or weight/coefficient answer is supplied.
-/
set_option autoImplicit false
set_option maxHeartbeats 120000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1RecursiveRecovery
open scoped BigOperators
open SemiprimeD1JetAxes SemiprimeD1TensorNetwork SemiprimeD1RecursiveCounter
open SemiprimeD1JetInterpretation SemiprimeD1JetBoxIndex
open SemiprimeD1JetAlgebra SemiprimeD1JetScalarMap SemiprimeD1DyadicInteger
open SemiprimeD1NetworkIntegralDeformation SemiprimeD1NetworkRecoveryLicence
open SemiprimeD1HermiteNodes SemiprimeD1JetRecoveryGrid
open SemiprimeD1JetAffineCoefficient (JetRun)

/-- The controller's literal original-grid retained phase array. -/
def retained (next : Context→Network→JetRun) (ctx : Context) (net : Network) (a u : ℕ) : Array PhaseRun :=
  ((List.finRange (SemiprimeD1WireKernelOriginal.size a)).map (phase next ctx net a u)).toArray

/-- The ONLY conditional semantic input: every actually retained physical block
is the corresponding coefficient of the original individual-entry integral polynomial,
reduced at that actual phase's computed precision. -/
def PhaseCorrect (next : Context→Network→JetRun) (ctx : Context) (net : Network) (a u : ℕ) : Prop :=
  ∀t : Fin (SemiprimeD1WireKernelOriginal.size a),
    t.val∈active a (SemiprimeD1TaperedLoss.height (edgeCount net) u) u →
    ∀j<nodeMultiplicity a (SemiprimeD1TaperedLoss.height (edgeCount net) u) u t.val,
    interpret ⟨ctx.axes,(phase next ctx net a u t).precision⟩
      (((phase next ctx net a u t).blocks[j]?).getD [])=
      ((networkPolynomial ctx.axes net.leftCount net.rows.length 64 a (arity net.rows) (owner net.rows)
          t net.left.toList net.right.toList).map
        (scalarMap (dims ctx.axes) (reduction (phase next ctx net a u t).precision))).coeff j

/-- Original placement count is the ACTUAL literal network edge count. -/
theorem placements_length (net : Network) (a : ℕ) :
    (SemiprimeD1OriginalDeformation.Placements net.leftCount net.rows.length 64 a
      (arity net.rows) (owner net.rows)).length=edgeCount net := by
  rw [SemiprimeD1OriginalModeAcquisition.original_size,SemiprimeD1TensorNetworkLayout.original_ports]
  rfl

/-- Literal retained-array reads return the actual phase at the original grid index. -/
theorem retained_read (next : Context→Network→JetRun) (ctx : Context) (net : Network)
    (a u : ℕ) (t : Fin (SemiprimeD1WireKernelOriginal.size a)) :
    (retained next ctx net a u)[t.val]?=some (phase next ctx net a u t) := by
  simp [retained,List.finRange,t.isLt]

/-- Every actual two-dimensional recovery word is this retained block's original old-coordinate read. -/
theorem coordinate_read (next : Context→Network→JetRun) (ctx : Context) (net : Network)
    (a u k j : ℕ) (t : Fin (SemiprimeD1WireKernelOriginal.size a)) :
    (((((coordinate (retained next ctx net a u) k).values[t.val]?).getD #[])[j]?).getD [])=
      (((((phase next ctx net a u t).blocks[j]?).getD [])[k]?).getD []) := by
  rw [SemiprimeD1RecursivePhaseBounds.coordinate_read,retained_read]
  rfl

/-- Every required active block is a REAL stored block with derived old-coordinate shape,
compactness and actual precision width; the default branch is not used there. -/
theorem active_block_good (next : Context→Network→JetRun) (ctx : Context) (net : Network)
    (a u : ℕ) (hua : u≤a) (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (ht : t.val∈active a (SemiprimeD1TaperedLoss.height (edgeCount net) u) u)
    (j : ℕ) (hj : j<nodeMultiplicity a (SemiprimeD1TaperedLoss.height (edgeCount net) u) u t.val) :
    SemiprimeD1TensorTables.GoodWords ⟨ctx.axes,(phase next ctx net a u t).precision⟩
      (((phase next ctx net a u t).blocks[j]?).getD []) := by
  have hsize:=SemiprimeD1RecursivePhaseControl.active_blocks_size next ctx net a u t hua ht
  have hlt : j<(phase next ctx net a u t).blocks.size := by rw [hsize];exact hj
  rw [Array.getElem?_eq_getElem hlt]
  exact SemiprimeD1RecursivePhaseBounds.phase_blocks_good next ctx net a u t _ (Array.getElem_mem hlt)

/-- A concrete coordinate of the actual block postcondition supplies the precise
original D.11 child residue needed by the cached integer recovery licence. -/
theorem coordinate_post (next : Context→Network→JetRun) (ctx : Context) (net : Network)
    (a u : ℕ) (hpos : ctx.Positive) (hua : u≤a) (hphase : PhaseCorrect next ctx net a u)
    (k : ℕ) (hk : k<ctx.rank) (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (ht : t.val∈active a (SemiprimeD1TaperedLoss.height (edgeCount net) u) u)
    (j : ℕ) (hj : j<nodeMultiplicity a (SemiprimeD1TaperedLoss.height (edgeCount net) u) u t.val) :
    coefficient (dims ctx.axes) (exponent ctx.axes k) (exponent_inBox ctx.axes k hpos hk)
      (scalarMap (dims ctx.axes) (reduction (SemiprimeD1WeightPrecision.precision a (edgeCount net) u ctx.precision t.val))
        ((networkPolynomial ctx.axes net.leftCount net.rows.length 64 a (arity net.rows) (owner net.rows)
          t net.left.toList net.right.toList).coeff j))=
      (SemiprimeBitArithmetic.bitValue
        (((((coordinate (retained next ctx net a u) k).values[t.val]?).getD #[])[j]?).getD []):
          ZMod (2^SemiprimeD1WeightPrecision.precision a (edgeCount net) u ctx.precision t.val)) := by
  have h:=congrArg (coefficient (dims ctx.axes) (exponent ctx.axes k)
    (exponent_inBox ctx.axes k hpos hk)) (hphase t ht j hj)
  rw [coefficient_interpret ⟨ctx.axes,(phase next ctx net a u t).precision⟩ _ hpos k hk,
    Polynomial.coeff_map] at h
  have hp:=SemiprimeD1RecursivePhaseControl.active_precision next ctx net a u t hua ht
  rw [hp] at h
  rw [coordinate_read]
  simpa only [SemiprimeD1JetRingBits.coefficient] using h.symm

/-- Scalar-reference modular sum equals the actual parent leaf contraction.
The single count equality is derived at the concrete wrapper below. -/
theorem split_sum_leaf (ctx : Context) (hpos : ctx.Positive) (net : Network)
    (M : ℕ) (hM : M=edgeCount net) :
    (∑bits : Fin M→Bool,
      (net.left.toList.map (fun v => interpret ctx
        (SemiprimeD1TensorTables.valueAt v.table (SemiprimeD1LeafCounter.localAssignment bits v)))).prod*
      (net.right.toList.map (fun v => interpret ctx
        (SemiprimeD1TensorTables.valueAt v.table (SemiprimeD1LeafCounter.localAssignment bits v)))).prod)=
      interpret ctx (leaf ctx net).words := by
  subst M
  rw [leaf_value ctx hpos net]
  simp only [vertices,List.map_append,List.prod_append]

/-- Original degree/integrality/individual-lift recovery target is exactly the parent coordinate. -/
theorem reference_residue_leaf (ctx : Context) (hpos : ctx.Positive) (net : Network) (a : ℕ)
    (k : ℕ) (hk : k<ctx.rank) :
    SemiprimeD1RecoveryResidue.reduce ctx.precision
      ((networkReference ctx.axes net.leftCount net.rows.length 64 a (arity net.rows) (owner net.rows)
        net.left.toList net.right.toList (exponent ctx.axes k) (exponent_inBox ctx.axes k hpos hk)).eval 0)=
      SemiprimeD1JetRingBits.coefficient ctx (leaf ctx net).words k := by
  rw [network_reference_zero_residue ctx.axes net.leftCount net.rows.length 64 a ctx.precision
    (arity net.rows) (owner net.rows) net.left.toList net.right.toList
    (exponent ctx.axes k) (exponent_inBox ctx.axes k hpos hk),
    split_sum_leaf ctx hpos net _ (placements_length net a),coefficient_interpret ctx _ hpos k hk]
/-- The actual EXECUTED coordinate recovery equals the parent leaf coordinate,
from the sole actual-block postcondition and original schedule inequalities. -/
theorem recoverCoordinate_correct (next : Context→Network→JetRun) (ctx : Context) (net : Network)
    (a u : ℕ) (hpos : ctx.Positive) (hu : 0<u) (huM : u≤edgeCount net) (hua : u≤a)
    (hphase : PhaseCorrect next ctx net a u) (k : ℕ) (hk : k<ctx.rank) :
    (SemiprimeBitArithmetic.bitValue
      (recoverCoordinate ctx a (edgeCount net) u
        (SemiprimeD1ModeRate.workingPrecision (edgeCount net) u a 0 ctx.precision)
        (retained next ctx net a u) k).bits:ZMod (2^ctx.precision))=
      SemiprimeD1JetRingBits.coefficient ctx (leaf ctx net).words k := by
  have hr:=network_word_recovery ctx.axes net.leftCount net.rows.length 64 a u ctx.precision
    (arity net.rows) (owner net.rows) net.left.toList net.right.toList
    (exponent ctx.axes k) (exponent_inBox ctx.axes k hpos hk) hu
  rw [placements_length net a] at hr
  have h:=hr huM (fun t => ((coordinate (retained next ctx net a u) k).values[t]?).getD #[])
    (fun t ht j hj => coordinate_post next ctx net a u hpos hua hphase k hk t ht j hj)
  rw [SemiprimeD1IntegerRecoveryAcquisition.run_result,
    reference_residue_leaf ctx hpos net a k hk] at h
  exact (SemiprimeD1RecursivePhaseBounds.recoverCoordinate_value next ctx net a u k huM).trans h
end RiemannGaussian.SemiprimeD1RecursiveRecovery
