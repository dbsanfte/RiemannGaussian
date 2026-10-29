/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackLeafLoop
/-! # Exact original eager-leaf bytes of the actual assignment-sum order -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace RiemannGaussian.SemiprimeD1StackLeafValue
open scoped BigOperators
open SemiprimeD1StackLeafLoop
open SemiprimeD1JetInterpretation (interpret)
open SemiprimeD1TensorTables (GoodWords)

/-- The actual counter-generated catalogue is a permutation of precisely the
original finite Boolean assignments. Order differences require only addition. -/
theorem catalogue_perm (M : ℕ) :
    (SemiprimeD1StackAssignmentOrder.assignments (2^M) (List.replicate M false)).Perm
      ((Finset.univ : Finset (Fin M→Bool)).toList.map List.ofFn) := by
  apply (List.perm_ext_iff_of_nodup (SemiprimeD1StackAssignmentOrder.zero_nodup M)
    (List.Nodup.map List.ofFn_injective (Finset.nodup_toList (Finset.univ : Finset (Fin M→Bool))))).mpr
  intro word
  rw [SemiprimeD1StackAssignmentOrder.zero_complete]
  constructor
  · intro hlen
    let f : Fin M→Bool := fun i=>word[i.val]'(by omega)
    have he : List.ofFn f=word := by
      apply List.ext_getElem (by simp [hlen])
      intro i hi hj
      simp only [List.getElem_ofFn]
      rfl
    exact List.mem_map.mpr ⟨f,by simp,he⟩
  · intro h
    obtain ⟨f,_,rfl⟩:=List.mem_map.mp h
    simp

/-- The reached physical dense sum represents exactly the sum of all parsed
assignment-product values plus the previous accumulator. -/
theorem summed_interpret (ctx : SemiprimeD1JetAxes.Context) (hp : ctx.Positive)
    (vertices : List SemiprimeD1LeafCounter.Vertex) (assignments : List (List Bool)) (acc : List (List Bool)) :
    interpret ctx (summed ctx vertices assignments acc)=
      (assignments.map (fun bits=>interpret ctx (SemiprimeD1TensorTapeLeaf.evaluateAssignment ctx vertices bits).words)).sum+
        interpret ctx acc := by
  induction assignments generalizing acc with
  | nil => simp [summed]
  | cons bits rest ih =>
    simp only [summed,ih,List.map_cons,List.sum_cons,SemiprimeD1JetOperations.interpret_add ctx _ _ hp]
    ac_rfl

/-- Every actual sum prefix after a canonical accumulator is canonical. -/
theorem summed_good (ctx : SemiprimeD1JetAxes.Context) (vertices : List SemiprimeD1LeafCounter.Vertex)
    (assignments : List (List Bool)) (acc : List (List Bool)) (ha : GoodWords ctx acc) :
    GoodWords ctx (summed ctx vertices assignments acc) := by
  induction assignments generalizing acc with
  | nil => exact ha
  | cons bits rest ih => exact ih _ (SemiprimeD1LeafCounterBounds.add_good ctx _ _)

/-- The complete real enumeration/dense-fold bytes equal the SAME frozen
TensorTapeLeaf.run words, independently of its materialized-table sum order. -/
theorem summed_original (M : ℕ) (ctx : SemiprimeD1JetAxes.Context) (hp : ctx.Positive)
    (vertices : List SemiprimeD1LeafCounter.Vertex) :
    summed ctx vertices (SemiprimeD1StackAssignmentOrder.assignments (2^M) (List.replicate M false)) []=
      (SemiprimeD1TensorTapeLeaf.run M ctx vertices).words := by
  let catalogue:=SemiprimeD1StackAssignmentOrder.assignments (2^M) (List.replicate M false)
  have hnon : catalogue ≠ [] := by
    have hl:=SemiprimeD1StackAssignmentOrder.assignments_length (2^M) (List.replicate M false)
    have hp : 0<2^M := by positivity
    intro he
    change catalogue.length=2^M at hl
    rw [he] at hl
    simp only [List.length_nil] at hl
    omega
  have ha : GoodWords ctx (summed ctx vertices catalogue []) := by
    cases he : catalogue with
    | nil => exact (hnon he).elim
    | cons bits rest =>
      exact summed_good ctx vertices rest _ (SemiprimeD1LeafCounterBounds.add_good ctx _ _)
  have hb : GoodWords ctx (SemiprimeD1TensorTapeLeaf.run M ctx vertices).words := by
    rw [SemiprimeD1TensorTapeLeaf.run_words]
    exact SemiprimeD1LeafCounterBounds.run_good M ctx vertices
  apply SemiprimeD1JetInterpretation.interpret_injective ctx _ _ hp ha.1 hb.1
    (fun w hw=>(ha.2 w hw).1) (fun w hw=>(hb.2 w hw).1)
    (fun w hw=>(ha.2 w hw).2) (fun w hw=>(hb.2 w hw).2)
  rw [summed_interpret ctx hp]
  have hz : interpret ctx []=0 := by simp [SemiprimeD1JetInterpretation.interpret,SemiprimeD1JetInterpretation.basis,
    SemiprimeD1JetRingBits.coefficient,SemiprimeBitArithmetic.bitValue]
  rw [hz,add_zero]
  have hs:=(catalogue_perm M).map
    (fun bits=>interpret ctx (SemiprimeD1TensorTapeLeaf.evaluateAssignment ctx vertices bits).words)
  rw [hs.sum_eq,List.map_map]
  rw [←List.sum_toFinset _ (Finset.nodup_toList (Finset.univ : Finset (Fin M→Bool)))]
  simp only [Finset.toList_toFinset]
  rw [SemiprimeD1TensorTapeLeaf.run_words,SemiprimeD1LeafCounter.run_value M ctx hp vertices]
  apply Finset.sum_congr rfl
  intro bits _
  dsimp only [Function.comp_def]
  rw [SemiprimeD1TensorTapeLeaf.evaluateAssignment_words,
    SemiprimeD1LeafCounter.evaluateAssignment_value ctx hp vertices bits]

end RiemannGaussian.SemiprimeD1StackLeafValue
