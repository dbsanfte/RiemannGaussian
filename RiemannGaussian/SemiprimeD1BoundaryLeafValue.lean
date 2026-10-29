import RiemannGaussian.SemiprimeD1BoundaryTensorRep
import RiemannGaussian.SemiprimeD1BoundaryLeafLoad

/-! Closed actual boundary-leaf byte correctness and paid fallback correctness. -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1BoundaryLeaf
open SemiprimeD1BoundaryTensorRep
open SemiprimeD1BoundaryLeafPorts
open SemiprimeD1BoundaryRefinement
open SemiprimeD1BoundaryRecordsShape
open SemiprimeD1BoundaryRecordsReduction
open SemiprimeD1BoundaryPlan (Work)
open SemiprimeD1JetAxes (Context)

theorem acquire_represents (ctx : Context) (hp : ctx.Positive) (net : Network)
    (hw : SemiprimeD1TensorNetwork.WellFormed net) :
    Represents ctx net (fullVertices net) (acquire ctx net).tensor := by
  let g := SemiprimeD1BoundaryPlan.graph net
  let vs := SemiprimeD1TensorNetwork.vertices net
  let plan := SemiprimeD1BoundaryPlan.acquire g
  have hk : 0 < plan.k := by
    have h := (SemiprimeD1BoundaryChoice.chooseK_bounds g).1
    exact lt_of_lt_of_le (by omega : 0 < 2) h
  have hs := SemiprimeD1BoundaryLeafLoad.buckets_split ctx g vs plan.colours plan.k hk
  have hm := mergeAll_represents ctx hp net hw plan.colours (List.range' 1 (plan.k-1))
    (List.nodup_range') (colourClass net plan.colours 0)
    (bucket ctx g vs plan.colours 0).value (bucket_represents ctx hp net hw plan.colours 0)
    (by
      intro c hc
      obtain ⟨i,_,hc'⟩ := List.mem_range'.mp hc
      exact colourClass_disjoint net plan.colours 0 c (by omega))
  have hrange : List.range plan.k = 0 :: List.range' 1 (plan.k-1) := by
    cases h : plan.k with
    | zero => omega
    | succ n => simp only [List.range_eq_range',List.range'_succ,Nat.add_sub_cancel,Nat.zero_add]
  have hcover : colourClass net plan.colours 0 ∪
      (List.range' 1 (plan.k-1)).toFinset.biUnion (colourClass net plan.colours) = fullVertices net := by
    have hc := acquired_cover net
    change (Finset.range plan.k).biUnion (colourClass net plan.colours) = fullVertices net at hc
    rw [←List.toFinset_range,hrange] at hc
    simpa only [List.toFinset_cons,Finset.biUnion_insert] using hc
  rw [hcover] at hm
  change Represents ctx net (fullVertices net)
    (mergeAll ctx (((List.range plan.k).map (bucket ctx g vs plan.colours)).headD ⟨⟨[],[]⟩,1⟩).value
      ((((List.range plan.k).map (bucket ctx g vs plan.colours)).tail).map Work.value)).value
  rw [hs]
  simpa only [List.headD_cons,List.tail_cons,List.map_map,Function.comp_def] using hm

/-- Exact old whole-jet bytes from the closed acquired bucket/merge execution. -/
theorem run_words (ctx : Context) (net : Network) (hp : ctx.Positive)
    (hw : SemiprimeD1TensorNetwork.WellFormed net) :
    (run ctx net).words = (SemiprimeD1TensorNetwork.leaf ctx net).words := by
  apply words_eq_leaf_of_boundary ctx net hp _ (SemiprimeD1BoundaryLeafCanonical.run_good ctx net)
  have hr := acquire_represents ctx hp net hw
  rw [run_interpret_scalar ctx net (SemiprimeD1BoundaryLeafLoad.acquired_empty_ports ctx net)]
  have he := hr.value (∅ : Finset (Fin (SemiprimeD1TensorNetwork.edgeCount net)))
  simp only [address,SemiprimeD1BoundaryLeafLoad.acquired_empty_ports,List.map_nil] at he
  rw [he]
  change SemiprimeD1BoundarySemantics.value (networkGraph net) (vertexValue ctx net) (fullVertices net) ∅ =
    SemiprimeD1BoundarySemantics.value (networkGraph net) (vertexValue ctx net) (fullVertices net)
      (SemiprimeD1BoundarySemantics.bitsEquiv.symm (fun _ => false))
  have hb : SemiprimeD1BoundarySemantics.bitsEquiv.symm
      (fun _ : Fin (SemiprimeD1TensorNetwork.edgeCount net) => false) = ∅ := by
    ext e
    simp [SemiprimeD1BoundarySemantics.bitsEquiv]
  rw [hb]

/-- The executed validity guard and paid old-leaf fallback give total byte
correctness under positive axes alone, including precision zero. -/
theorem checked_words (ctx : Context) (net : Network) (hp : ctx.Positive) :
    (checked ctx net).words = (SemiprimeD1TensorNetwork.leaf ctx net).words := by
  simp only [checked]
  split_ifs with h
  ·
    exact run_words ctx net hp ((validate_correct ctx net).mp h).1
  · exact SemiprimeD1TensorTapeLeaf.leaf_words ctx net

end RiemannGaussian.SemiprimeD1BoundaryLeaf
