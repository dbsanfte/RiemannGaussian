/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackVertexProductLoop
/-! # Exact original assignment bytes of the actual vertex-product order -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RiemannGaussian.SemiprimeD1StackVertexProductValue
open SemiprimeD1StackVertexProductLoop
open SemiprimeD1JetInterpretation (interpret)
open SemiprimeD1TensorTables (GoodWords)

/-- The actually executed accumulator order represents the same commutative
product; no vertex table or coefficient is replaced during execution. -/
theorem folded_interpret (ctx : SemiprimeD1JetAxes.Context) (hp : ctx.Positive)
    (vertices : List SemiprimeD1LeafCounter.Vertex) (bits : List Bool) (acc : List (List Bool)) :
    interpret ctx (folded ctx bits vertices acc)=
      (vertices.map (fun v=>interpret ctx (SemiprimeD1TensorTapeLeaf.evaluateVertex v bits).words)).prod*
        interpret ctx acc := by
  induction vertices generalizing acc with
  | nil => simp [folded]
  | cons v vs ih =>
    simp only [folded,ih,List.map_cons,List.prod_cons,SemiprimeD1JetOperations.interpret_mul ctx _ _ hp]
    ac_rfl

/-- The frozen original right-recursive assignment evaluation has that same
literal-table product value on every physical assignment word. -/
theorem assignment_interpret (ctx : SemiprimeD1JetAxes.Context) (hp : ctx.Positive)
    (vertices : List SemiprimeD1LeafCounter.Vertex) (bits : List Bool) :
    interpret ctx (SemiprimeD1TensorTapeLeaf.evaluateAssignment ctx vertices bits).words=
      (vertices.map (fun v=>interpret ctx (SemiprimeD1TensorTapeLeaf.evaluateVertex v bits).words)).prod := by
  induction vertices with
  | nil => simpa only [SemiprimeD1TensorTapeLeaf.evaluateAssignment,List.map_nil,List.prod_nil] using
      SemiprimeD1JetAffineCoefficient.interpret_one ctx hp
  | cons v vs ih =>
    change interpret ctx (SemiprimeD1JetRingBits.mul ctx
      (SemiprimeD1TensorTapeLeaf.evaluateVertex v bits).words
      (SemiprimeD1TensorTapeLeaf.evaluateAssignment ctx vs bits).words).words=_
    rw [SemiprimeD1JetOperations.interpret_mul ctx _ _ hp,ih]
    rfl

/-- Every actual accumulator remains canonical, including the empty network. -/
theorem folded_good (ctx : SemiprimeD1JetAxes.Context)
    (vertices : List SemiprimeD1LeafCounter.Vertex) (bits : List Bool) (acc : List (List Bool))
    (ha : GoodWords ctx acc) : GoodWords ctx (folded ctx bits vertices acc) := by
  induction vertices generalizing acc with
  | nil => exact ha
  | cons v vs ih => exact ih _ (SemiprimeD1LeafCounterBounds.mul_good ctx _ _)

/-- Canonical physical byte equality to the SAME frozen leaf assignment routine;
this is a semantic/canonicality proof, never a clock equality transfer. -/
theorem folded_original (ctx : SemiprimeD1JetAxes.Context) (hp : ctx.Positive)
    (vertices : List SemiprimeD1LeafCounter.Vertex) (bits : List Bool) :
    folded ctx bits vertices (SemiprimeD1JetAffineCoefficient.one ctx).words=
      (SemiprimeD1TensorTapeLeaf.evaluateAssignment ctx vertices bits).words := by
  have ha:=folded_good ctx vertices bits _ (SemiprimeD1LeafCounterBounds.one_good ctx)
  have hb:=SemiprimeD1TensorTapeLeaf.evaluateAssignment_good ctx vertices bits
  apply SemiprimeD1JetInterpretation.interpret_injective ctx _ _ hp ha.1 hb.1
    (fun w hw=>(ha.2 w hw).1) (fun w hw=>(hb.2 w hw).1)
    (fun w hw=>(ha.2 w hw).2) (fun w hw=>(hb.2 w hw).2)
  rw [folded_interpret ctx hp,SemiprimeD1JetAffineCoefficient.interpret_one ctx hp,
    mul_one,assignment_interpret ctx hp]

end RiemannGaussian.SemiprimeD1StackVertexProductValue
