import RiemannGaussian.SemiprimeD1BoundaryBucketValue
import RiemannGaussian.SemiprimeD1BoundaryRecordsShape

/-! Semantic invariant for actual acquired tensors and their executed merges. -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1BoundaryTensorRep
open scoped BigOperators
open SemiprimeD1BoundaryRecords
open SemiprimeD1BoundaryRecordsLookup
open SemiprimeD1BoundaryRecordsReduction
open SemiprimeD1BoundaryRecordsShape
open SemiprimeD1BoundaryLeaf
open SemiprimeD1BoundaryLeafPorts
open SemiprimeD1BoundaryCatalogue
open SemiprimeD1BoundaryRefinement
open SemiprimeD1BoundarySemantics
open SemiprimeD1JetAxes (Context)
open SemiprimeD1JetInterpretation (interpret)

/-- Actual Boolean address obtained by retaining the given ordered ports. -/
def address (ports : List Nat) {m : Nat} (x : Finset (Fin m)) : List Bool :=
  ports.map (fun p => decide (p ∈ x.image Fin.val))

/-- Proof-side invariant of the literal record tensor, with no runtime supplier. -/
structure Represents (ctx : Context) (net : Network) (s : Finset Nat) (tensor : Tensor) : Prop where
  bound : ∀ p ∈ tensor.ports, p < SemiprimeD1TensorNetwork.edgeCount net
  ports : lift (SemiprimeD1TensorNetwork.edgeCount net) tensor.ports.toFinset =
    boundary (networkGraph net) s
  sorted : tensor.entries.Pairwise SemiprimeD1BoundaryRecordsOrder.EntryLE
  unique : tensor.entries.Pairwise (fun a b => a.key ≠ b.key)
  value : ∀ x, weighted ctx tensor.entries (address tensor.ports x) =
    SemiprimeD1BoundarySemantics.value (networkGraph net) (vertexValue ctx net) s x

theorem bucket_represents (ctx : Context) (hp : ctx.Positive) (net : Network)
    (hw : SemiprimeD1TensorNetwork.WellFormed net) (colours : List Nat) (c : Nat) :
    Represents ctx net (colourClass net colours c)
      (bucket ctx (SemiprimeD1BoundaryPlan.graph net) (SemiprimeD1TensorNetwork.vertices net)
        colours c).value := by
  refine ⟨?_,SemiprimeD1BoundaryBucketValue.lift_boundary net colours c,
    bucket_sorted ctx _ _ _ _,bucket_unique ctx _ _ _ _,?_⟩
  · intro p hp
    simpa only [SemiprimeD1BoundaryPlan.graph_edges_length] using
      (classPorts_lt (SemiprimeD1BoundaryPlan.graph net) colours c p).2 hp
  · exact SemiprimeD1BoundaryBucketValue.bucket_value ctx hp net hw colours c

theorem union_bound (net : Network) (left right : Tensor)
    (hl : ∀ p ∈ left.ports, p < SemiprimeD1TensorNetwork.edgeCount net)
    (hr : ∀ p ∈ right.ports, p < SemiprimeD1TensorNetwork.edgeCount net) :
    ∀ p ∈ unionPorts left.ports right.ports, p < SemiprimeD1TensorNetwork.edgeCount net := by
  intro p hp
  exact (unionPorts_mem _ _ p).mp hp |>.elim (hl p) (hr p)

theorem merge_ports (ctx : Context) (net : Network) (s t : Finset Nat)
    (left right : Tensor) (hl : Represents ctx net s left) (hr : Represents ctx net t right)
    (hst : Disjoint s t) :
    lift (SemiprimeD1TensorNetwork.edgeCount net)
      (remainingPorts left.ports right.ports).toFinset = boundary (networkGraph net) (s ∪ t) := by
  rw [SemiprimeD1BoundaryIdentity.boundary_union _ _ _ hst]
  ext e
  have hleft := Finset.ext_iff.mp hl.ports e
  have hright := Finset.ext_iff.mp hr.ports e
  simp only [mem_lift,List.mem_toFinset] at hleft hright
  simp only [mem_lift,List.mem_toFinset,remainingPorts_mem,
    Finset.mem_union,Finset.mem_sdiff,←hleft,←hright]

theorem projected_lookup (ctx : Context) (net : Network) (s : Finset Nat) (tensor : Tensor)
    (hr : Represents ctx net s tensor) (source : List Nat) (hn : source.Nodup)
    (hb : ∀ p ∈ source, p < SemiprimeD1TensorNetwork.edgeCount net)
    (ht : ∀ p ∈ tensor.ports, p ∈ source) (bits : List Bool) (hlen : bits.length = source.length) :
    interpret ctx (lookupWords tensor.entries (project bits source tensor.ports).value) =
      value (networkGraph net) (vertexValue ctx net) s
        (lift (SemiprimeD1TensorNetwork.edgeCount net) (selected source bits)) := by
  rw [project_selected source tensor.ports hn bits hlen ht]
  have hsel : ∀ p ∈ selected source bits, p < SemiprimeD1TensorNetwork.edgeCount net := by
    intro p hp
    exact hb p (List.mem_toFinset.mp (selected_subset source bits hp))
  have ha : address tensor.ports (lift (SemiprimeD1TensorNetwork.edgeCount net)
      (selected source bits)) = tensor.ports.map (fun p => decide (p ∈ selected source bits)) := by
    rw [address,image_lift _ _ hsel]
  rw [←ha,←weighted_eq_lookup ctx tensor.entries hr.unique,hr.value]

theorem merge_natural_sum (ctx : Context) (hp : ctx.Positive) (net : Network)
    (s t : Finset Nat) (left right : Tensor) (hl : Represents ctx net s left)
    (hr : Represents ctx net t right) (x : Finset (Fin (SemiprimeD1TensorNetwork.edgeCount net))) :
    weighted ctx (SemiprimeD1BoundaryLeaf.merge ctx left right).value.entries
      (address (remainingPorts left.ports right.ports) x) =
    ∑ z ∈ (unionPorts left.ports right.ports).toFinset.powerset,
      if z ∩ (remainingPorts left.ports right.ports).toFinset =
        x.image Fin.val ∩ (remainingPorts left.ports right.ports).toFinset then
        value (networkGraph net) (vertexValue ctx net) s (lift _ z) *
          value (networkGraph net) (vertexValue ctx net) t (lift _ z) else 0 := by
  rw [SemiprimeD1BoundaryLeafCorrectness.merge_weighted ctx hp left right hl.sorted hr.sorted]
  simp only [seed,List.map_map,Function.comp_def,
    SemiprimeD1JetAffineCoefficient.interpret_one ctx hp,one_mul]
  rw [←assignments_selected_sum _ (unionPorts_nodup _ _)]
  congr 1
  apply List.map_congr_left
  intro bits hbits
  have hlen := (SemiprimeD1BoundaryAddresses.assignments_mem _ bits).mp hbits
  have hb := union_bound net left right hl.bound hr.bound
  have hleft : ∀ p ∈ left.ports, p ∈ unionPorts left.ports right.ports := by
    intro p hp
    exact (unionPorts_mem _ _ _).mpr (Or.inl hp)
  have hright : ∀ p ∈ right.ports, p ∈ unionPorts left.ports right.ports := by
    intro p hp
    exact (unionPorts_mem _ _ _).mpr (Or.inr hp)
  have htarget : ∀ p ∈ remainingPorts left.ports right.ports,
      p ∈ unionPorts left.ports right.ports := by
    intro p hp
    rcases (remainingPorts_mem _ _ p).mp hp with hp | hp
    · exact hleft p hp.1
    · exact hright p hp.1
  rw [projected_lookup ctx net s left hl _ (unionPorts_nodup _ _) hb hleft bits hlen,
    projected_lookup ctx net t right hr _ (unionPorts_nodup _ _) hb hright bits hlen,
    project_selected _ _ (unionPorts_nodup _ _) bits hlen htarget]
  simp only [address,address_eq_iff]

theorem merge_represents (ctx : Context) (hp : ctx.Positive) (net : Network)
    (hw : SemiprimeD1TensorNetwork.WellFormed net) (s t : Finset Nat)
    (left right : Tensor) (hl : Represents ctx net s left) (hr : Represents ctx net t right)
    (hst : Disjoint s t) :
    Represents ctx net (s ∪ t) (SemiprimeD1BoundaryLeaf.merge ctx left right).value := by
  have htarget : ∀ p ∈ remainingPorts left.ports right.ports,
      p < SemiprimeD1TensorNetwork.edgeCount net := by
    intro p hp
    rcases (remainingPorts_mem _ _ p).mp hp with hp | hp
    · exact hl.bound p hp.1
    · exact hr.bound p hp.1
  refine ⟨htarget,merge_ports ctx net s t left right hl hr hst,
    merge_sorted ctx left right,merge_unique ctx left right,?_⟩
  intro x
  change weighted ctx (SemiprimeD1BoundaryLeaf.merge ctx left right).value.entries
    (address (remainingPorts left.ports right.ports) x) = _
  rw [merge_natural_sum ctx hp net s t left right hl hr]
  rw [sum_constrained_lift _ _ _
    (fun p hp => union_bound net left right hl.bound hr.bound p (List.mem_toFinset.mp hp))
    (fun p hp => htarget p (List.mem_toFinset.mp hp)) x
    (fun z => value (networkGraph net) (vertexValue ctx net) s z *
      value (networkGraph net) (vertexValue ctx net) t z)]
  have hsource : lift (SemiprimeD1TensorNetwork.edgeCount net)
      (unionPorts left.ports right.ports).toFinset =
      boundary (networkGraph net) s ∪ boundary (networkGraph net) t := by
    ext e
    have hleft := Finset.ext_iff.mp hl.ports e
    have hright := Finset.ext_iff.mp hr.ports e
    simpa only [mem_lift,List.mem_toFinset,unionPorts_mem,Finset.mem_union] using
      or_congr hleft hright
  rw [hsource,merge_ports ctx net s t left right hl hr hst]
  exact SemiprimeD1BoundaryFiber.boundary_fiber _ _ (vertexValue_local ctx net hw) s t hst x

theorem mergeAll_represents (ctx : Context) (hp : ctx.Positive) (net : Network)
    (hw : SemiprimeD1TensorNetwork.WellFormed net) (colours : List Nat)
    (cs : List Nat) (hn : cs.Nodup) (s : Finset Nat) (first : Tensor)
    (hf : Represents ctx net s first)
    (hd : ∀ c ∈ cs, Disjoint s (colourClass net colours c)) :
    Represents ctx net (s ∪ cs.toFinset.biUnion (colourClass net colours))
      (mergeAll ctx first (cs.map (fun c =>
        (bucket ctx (SemiprimeD1BoundaryPlan.graph net) (SemiprimeD1TensorNetwork.vertices net)
          colours c).value))).value := by
  induction cs generalizing s first with
  | nil => simpa only [List.map_nil,List.toFinset_nil,Finset.biUnion_empty,Finset.union_empty,
      mergeAll] using hf
  | cons c cs ih =>
    have hn' := List.nodup_cons.mp hn
    have hm := merge_represents ctx hp net hw s (colourClass net colours c) first _ hf
      (bucket_represents ctx hp net hw colours c) (hd c List.mem_cons_self)
    have hd' : ∀ d ∈ cs, Disjoint (s ∪ colourClass net colours c) (colourClass net colours d) := by
      intro d hmem
      apply Finset.disjoint_union_left.mpr
      exact ⟨hd d (List.mem_cons_of_mem c hmem),colourClass_disjoint net colours c d
        (fun he => hn'.1 (he ▸ hmem))⟩
    have hresult := ih hn'.2 (s ∪ colourClass net colours c) _ hm hd'
    simpa only [List.map_cons,mergeAll,List.toFinset_cons,Finset.biUnion_insert,
      Finset.union_assoc] using hresult

end RiemannGaussian.SemiprimeD1BoundaryTensorRep
