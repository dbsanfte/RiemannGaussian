/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1BoundaryLeafReport
import RiemannGaussian.SemiprimeD1BoundaryLeafPorts
import RiemannGaussian.SemiprimeD1BoundaryPotential

/-! # Actual leaf dimensions and acquired partition loads -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1BoundaryLeafLoad
open SemiprimeD1BoundaryPlan (Graph Load loadValue)
open SemiprimeD1BoundaryLeaf
open SemiprimeD1BoundaryLeafPorts

/-- Removing index metadata does not change a source predicate's selected count. -/
theorem selected_length {α : Type} (xs : List α) (f : α → Bool) :
    (selectedIndices xs (fun x => f x.1)).length=(xs.filter f).length := by
  unfold selectedIndices
  rw [List.length_map,←List.length_map (f:=Prod.fst)]
  have h : ((xs.zipIdx.filter (fun x => f x.1)).map Prod.fst)=xs.filter f := by
    change List.map Prod.fst (List.filter (f ∘ Prod.fst) xs.zipIdx)=_
    rw [←List.filter_map]
    simp
  rw [h]

/-- Every actual class incident catalogue is exactly its acquired load count. -/
theorem bucket_load (g : Graph) (colours : List Nat) (c : Nat) :
    (classPorts g colours c).1.length=loadValue g colours (.bucket c) := by
  exact selected_length g.edges (fun e => colours.getD e.1 0==c || colours.getD e.2 0==c)

/-- A generic source-ordinal scan for a colour endpoint predicate. -/
def scan (g : Graph) (f : Nat → Nat → Bool) (colours : List Nat) : List Nat :=
  selectedIndices g.edges (fun x => f (colours.getD x.1.1 0) (colours.getD x.1.2 0))

/-- The actual prefix boundary predicate. -/
def prefixBoundary (j a b : Nat) : Bool := (a<j)!=(b<j)

/-- One colour's actual boundary predicate. -/
def colourBoundary (c a b : Nat) : Bool := (a==c)!=(b==c)

/-- Prefix and next-colour membership are exclusive at each endpoint. -/
theorem boundary_step (j a b : Nat) :
    (prefixBoundary j a b != colourBoundary j a b)=prefixBoundary (j+1) a b := by
  unfold prefixBoundary colourBoundary
  by_cases ha : a<j <;> by_cases hb : b<j <;>
    by_cases hea : a=j <;> by_cases heb : b=j <;>
      simp [ha,hb,hea,heb,show (a<j+1 ↔ a<j ∨ a=j) by omega,
        show (b<j+1 ↔ b<j ∨ b=j) by omega]

/-- Endpoints in different prefix/next/future regions are exactly the union
of the two old boundaries. -/
theorem union_step (j a b : Nat) :
    (prefixBoundary j a b || colourBoundary j a b)=
      SemiprimeD1BoundaryPlan.indicator (.merge (j+1)) a b := by
  unfold prefixBoundary colourBoundary SemiprimeD1BoundaryPlan.indicator SemiprimeD1BoundaryPlan.region
  simp only [Nat.add_sub_cancel]
  by_cases ha : a<j <;> by_cases hb : b<j <;>
    by_cases hea : a=j <;> by_cases heb : b=j <;> simp [ha,hb,hea,heb]

/-- Original endpoints at an ordinal, with the runtime's actual defaults. -/
def endpoints (g : Graph) (colours : List Nat) (p : Nat) : Nat × Nat :=
  let e:=g.edges.getD p (0,0)
  (colours.getD e.1 0,colours.getD e.2 0)

theorem scan_mem (g : Graph) (f : Nat → Nat → Bool) (colours : List Nat) (p : Nat) :
    p∈scan g f colours ↔ p<g.edges.length ∧ f (endpoints g colours p).1 (endpoints g colours p).2=true := by
  by_cases hp : p<g.edges.length
  · simp only [scan,selectedIndices_mem _ _ p hp,endpoints,List.getD_eq_getElem _ _ hp,true_and,hp]
  · constructor
    · intro h
      exact False.elim (hp (selectedIndices_lt _ _ p h))
    · exact fun h => False.elim (hp h.1)

/-- Two boundary lists model a particular actual endpoint predicate. -/
def Models (g : Graph) (colours : List Nat) (f : Nat → Nat → Bool) (xs : List Nat) : Prop :=
  xs.Nodup ∧ ∀p,p∈xs ↔ p∈scan g f colours

theorem colour_models (g : Graph) (colours : List Nat) (c : Nat) :
    Models g colours (colourBoundary c) (classPorts g colours c).2 := by
  exact ⟨(classPorts_nodup g colours c).2,fun _ => Iff.rfl⟩

/-- Actual symmetric difference updates the precise prefix boundary. -/
theorem remaining_models (g : Graph) (colours : List Nat) (j : Nat) (left right : List Nat)
    (hl : Models g colours (prefixBoundary j) left)
    (hr : Models g colours (colourBoundary j) right) :
    Models g colours (prefixBoundary (j+1)) (remainingPorts left right) := by
  refine ⟨remainingPorts_nodup left right,?_⟩
  intro p
  rw [remainingPorts_mem,hl.2,hr.2]
  simp only [scan_mem]
  by_cases hp : p<g.edges.length
  · simp only [hp,true_and]
    have h:=boundary_step j (endpoints g colours p).1 (endpoints g colours p).2
    cases hleft : prefixBoundary j (endpoints g colours p).1 (endpoints g colours p).2 <;>
      cases hright : colourBoundary j (endpoints g colours p).1 (endpoints g colours p).2 <;>
        simp_all
  · simp [hp]

/-- The physically enumerated union has precisely its three-region load size. -/
theorem union_load (g : Graph) (colours : List Nat) (j : Nat) (left right : List Nat)
    (hl : Models g colours (prefixBoundary j) left)
    (hr : Models g colours (colourBoundary j) right) :
    (unionPorts left right).length=loadValue g colours (.merge (j+1)) := by
  have hn:=selectedIndices_nodup g.edges
    (fun x => SemiprimeD1BoundaryPlan.indicator (.merge (j+1)) (colours.getD x.1.1 0) (colours.getD x.1.2 0))
  have hperm : (unionPorts left right).Perm
      (scan g (SemiprimeD1BoundaryPlan.indicator (.merge (j+1))) colours) := by
    apply (List.perm_ext_iff_of_nodup (unionPorts_nodup left right) hn).mpr
    intro p
    change p∈unionPorts left right ↔ p∈scan g (SemiprimeD1BoundaryPlan.indicator (.merge (j+1))) colours
    rw [unionPorts_mem,hl.2,hr.2]
    simp only [scan_mem]
    by_cases hp : p<g.edges.length
    · simp only [hp,true_and]
      rw [←union_step]
      simp
    · simp [hp]
  exact hperm.length_eq.trans (selected_length g.edges
    (fun e => SemiprimeD1BoundaryPlan.indicator (.merge (j+1))
      (colours.getD e.1 0) (colours.getD e.2 0)))

/-- The runtime's actual chain keeps the prefix boundary at each step. -/
theorem mergeWidth_chain (ctx : SemiprimeD1JetAxes.Context) (g : Graph) (vs : List Vertex)
    (colours : List Nat) (j n W : Nat) (first : SemiprimeD1BoundaryRecords.Tensor)
    (hfirst : Models g colours (prefixBoundary j) first.ports)
    (hloads : ∀i,j≤ i → i<j+n → loadValue g colours (.merge (i+1))≤ W) :
    SemiprimeD1BoundaryLeafBounds.mergeWidth ctx first
      ((List.range' j n).map (fun c => (bucket ctx g vs colours c).value))≤ W := by
  induction n generalizing j first with
  | zero => simp only [List.range'_zero,List.map_nil,SemiprimeD1BoundaryLeafBounds.mergeWidth]; omega
  | succ n ih =>
    have hr:=colour_models g colours j
    have hu:=union_load g colours j first.ports (classPorts g colours j).2 hfirst hr
    have hrem:=remaining_models g colours j first.ports (classPorts g colours j).2 hfirst hr
    have htail:=ih (j+1) (SemiprimeD1BoundaryLeaf.merge ctx first (bucket ctx g vs colours j).value).value
      hrem (fun i hi hj => hloads i (by omega) (by omega))
    rw [List.range'_succ,List.map_cons,SemiprimeD1BoundaryLeafBounds.mergeWidth]
    apply max_le
    · exact hu.le.trans (hloads j (by omega) (by omega))
    · exact htail

/-- A list maximum fold dominates every stored measured load. -/
theorem member_le_foldl (xs : List Nat) (x a : Nat) (hx : x∈xs) : x≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · have aux : ∀(xs : List Nat) (a : Nat),a≤ xs.foldl max a := by
        intro xs a
        induction xs generalizing a with
        | nil => rfl
        | cons x xs ih => exact (Nat.le_max_left _ _).trans (ih _)
      exact (Nat.le_max_right a x).trans (aux ys (max a x))
    · exact ih _ hx

/-- Every load measured by actual acquisition is below its retained width. -/
theorem load_le_width (g : Graph) (l : Load)
    (hl : l∈SemiprimeD1BoundaryPlan.loads (SemiprimeD1BoundaryPlan.acquire g).k) :
    loadValue g (SemiprimeD1BoundaryPlan.acquire g).colours l≤
      (SemiprimeD1BoundaryPlan.acquire g).width := by
  apply member_le_foldl _ _ 0
  exact List.mem_map.mpr ⟨l,hl,rfl⟩

/-- Every actual bucket incident dimension is one of the acquired loads. -/
theorem acquired_bucket_le (g : Graph) (c : Nat)
    (hc : c<(SemiprimeD1BoundaryPlan.acquire g).k) :
    (classPorts g (SemiprimeD1BoundaryPlan.acquire g).colours c).1.length≤
      (SemiprimeD1BoundaryPlan.acquire g).width := by
  rw [bucket_load]
  apply load_le_width
  exact List.mem_append_left _ (List.mem_map.mpr ⟨c,List.mem_range.mpr hc,rfl⟩)

/-- Exact final prefix metadata for the executed consecutive merge chain. -/
theorem mergeAll_models (ctx : SemiprimeD1JetAxes.Context) (g : Graph) (vs : List Vertex)
    (colours : List Nat) (j n : Nat) (first : SemiprimeD1BoundaryRecords.Tensor)
    (hfirst : Models g colours (prefixBoundary j) first.ports) :
    Models g colours (prefixBoundary (j+n))
      (mergeAll ctx first ((List.range' j n).map (fun c => (bucket ctx g vs colours c).value))).value.ports := by
  induction n generalizing j first with
  | zero => simpa only [List.range'_zero,List.map_nil,mergeAll,Nat.add_zero] using hfirst
  | succ n ih =>
    have hr:=colour_models g colours j
    have hrem:=remaining_models g colours j first.ports (classPorts g colours j).2 hfirst hr
    have ht:=ih (j+1) (SemiprimeD1BoundaryLeaf.merge ctx first (bucket ctx g vs colours j).value).value hrem
    simpa only [List.range'_succ,List.map_cons,mergeAll,Nat.add_assoc,Nat.add_comm 1 n] using ht

/-- The first actual class is exactly the first prefix boundary. -/
theorem initial_models (g : Graph) (colours : List Nat) :
    Models g colours (prefixBoundary 1) (classPorts g colours 0).2 := by
  have h:=colour_models g colours 0
  have he : colourBoundary 0=prefixBoundary 1 := by
    funext a b
    by_cases ha : a=0 <;> by_cases hb : b=0 <;> simp [colourBoundary,prefixBoundary,ha,hb]
  rw [he] at h
  exact h

/-- The acquired class list has its literal first bucket and consecutive tail. -/
theorem buckets_split (ctx : SemiprimeD1JetAxes.Context) (g : Graph) (vs : List Vertex)
    (colours : List Nat) (k : Nat) (hk : 0<k) :
    (List.range k).map (bucket ctx g vs colours)=
      bucket ctx g vs colours 0::(List.range' 1 (k-1)).map (bucket ctx g vs colours) := by
  cases k with
  | zero => omega
  | succ n => simp only [List.range_eq_range',List.range'_succ,List.map_cons,Nat.add_sub_cancel,Nat.zero_add]

/-- Actual closed leaf output metadata models the entire acquired prefix. -/
theorem acquired_models (ctx : SemiprimeD1JetAxes.Context) (net : Network) :
    Models (SemiprimeD1BoundaryPlan.graph net)
      (SemiprimeD1BoundaryPlan.acquire (SemiprimeD1BoundaryPlan.graph net)).colours
      (prefixBoundary (SemiprimeD1BoundaryPlan.acquire (SemiprimeD1BoundaryPlan.graph net)).k)
      (acquire ctx net).tensor.ports := by
  let g:=SemiprimeD1BoundaryPlan.graph net
  let vs:=SemiprimeD1TensorNetwork.vertices net
  let plan:=SemiprimeD1BoundaryPlan.acquire g
  have hk : 0<plan.k := by have h:=(SemiprimeD1BoundaryChoice.chooseK_bounds g).1; exact lt_of_lt_of_le (by omega : 0<2) h
  have hs:=buckets_split ctx g vs plan.colours plan.k hk
  have hm:=mergeAll_models ctx g vs plan.colours 1 (plan.k-1)
    (bucket ctx g vs plan.colours 0).value (initial_models g plan.colours)
  have hk':1+(plan.k-1)=plan.k := by omega
  rw [hk'] at hm
  change Models g plan.colours (prefixBoundary plan.k)
    (mergeAll ctx (((List.range plan.k).map (bucket ctx g vs plan.colours)).headD ⟨⟨[],[]⟩,1⟩).value
      ((((List.range plan.k).map (bucket ctx g vs plan.colours)).tail).map SemiprimeD1BoundaryPlan.Work.value)).value.ports
  rw [hs]
  simpa only [List.headD_cons,List.tail_cons,List.map_map,Function.comp_def] using hm

/-- Closed acquisition colours every endpoint inside its own actual menu. -/
theorem acquired_endpoint_colours (g : Graph) (hvalid : SemiprimeD1BoundaryPotential.Valid g)
    (p : Nat) (hp : p<g.edges.length) :
    (endpoints g (SemiprimeD1BoundaryPlan.acquire g).colours p).1<(SemiprimeD1BoundaryPlan.acquire g).k ∧
    (endpoints g (SemiprimeD1BoundaryPlan.acquire g).colours p).2<(SemiprimeD1BoundaryPlan.acquire g).k := by
  have he:=hvalid g.edges[p] (List.getElem_mem hp)
  have hl:=SemiprimeD1BoundaryChoice.acquire_length g
  unfold endpoints
  rw [List.getD_eq_getElem _ _ hp]
  dsimp only
  constructor
  · have hi : g.edges[p].1<(SemiprimeD1BoundaryPlan.acquire g).colours.length := by omega
    rw [List.getD_eq_getElem _ _ hi]
    exact SemiprimeD1BoundaryChoice.acquire_colours g _ (List.getElem_mem hi)
  · have hi : g.edges[p].2<(SemiprimeD1BoundaryPlan.acquire g).colours.length := by omega
    rw [List.getD_eq_getElem _ _ hi]
    exact SemiprimeD1BoundaryChoice.acquire_colours g _ (List.getElem_mem hi)

/-- Every actual merge is exhausted: the closed leaf's final port list is empty. -/
theorem acquired_empty_ports (ctx : SemiprimeD1JetAxes.Context) (net : Network) :
    (acquire ctx net).tensor.ports=[] := by
  have hm:=acquired_models ctx net
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro p hp
  have hscan:=(hm.2 p).mp hp
  obtain ⟨hbound,hpred⟩:= (scan_mem _ _ _ p).mp hscan
  have hc:=acquired_endpoint_colours _ (SemiprimeD1BoundaryPotential.graph_valid net) p hbound
  simp [prefixBoundary,hc.1,hc.2] at hpred

/-- Every consecutive merge event is in the acquired measurement list. -/
theorem merge_load_member (k j : Nat) (hj : 1≤ j) (hk : j<k) :
    Load.merge (j+1)∈SemiprimeD1BoundaryPlan.loads k := by
  apply List.mem_append_right
  apply List.mem_map.mpr
  refine ⟨j-1,List.mem_range.mpr (by omega),?_⟩
  congr 1
  omega

/-- The closed actual merge maximum is bounded by the acquired measured maximum. -/
theorem acquired_mergeWidth_le (ctx : SemiprimeD1JetAxes.Context) (net : Network) :
    let bs:=SemiprimeD1BoundaryLeafReport.buckets ctx net
    SemiprimeD1BoundaryLeafBounds.mergeWidth ctx (bs.headD ⟨⟨[],[]⟩,1⟩).value
      (bs.tail.map SemiprimeD1BoundaryPlan.Work.value)≤
      (SemiprimeD1BoundaryPlan.acquire (SemiprimeD1BoundaryPlan.graph net)).width := by
  let g:=SemiprimeD1BoundaryPlan.graph net
  let vs:=SemiprimeD1TensorNetwork.vertices net
  let plan:=SemiprimeD1BoundaryPlan.acquire g
  have hk : 0<plan.k := by have h:=(SemiprimeD1BoundaryChoice.chooseK_bounds g).1; exact lt_of_lt_of_le (by omega : 0<2) h
  have hs:=buckets_split ctx g vs plan.colours plan.k hk
  have hm:=mergeWidth_chain ctx g vs plan.colours 1 (plan.k-1) plan.width
    (bucket ctx g vs plan.colours 0).value (initial_models g plan.colours)
    (fun j hj hlast => load_le_width g (.merge (j+1)) (merge_load_member plan.k j hj (by omega)))
  change SemiprimeD1BoundaryLeafBounds.mergeWidth ctx
    (((List.range plan.k).map (bucket ctx g vs plan.colours)).headD ⟨⟨[],[]⟩,1⟩).value
    ((((List.range plan.k).map (bucket ctx g vs plan.colours)).tail).map SemiprimeD1BoundaryPlan.Work.value)≤ plan.width
  rw [hs]
  simpa only [List.headD_cons,List.tail_cons,List.map_map,Function.comp_def] using hm

/-- Each stored vertex is selected by its actual acquired colour. -/
theorem acquired_vertex_le (net : Network) (hw : SemiprimeD1TensorNetwork.WellFormed net)
    (v : Vertex) (hv : v∈SemiprimeD1TensorNetwork.vertices net) :
    v.ports.length≤(SemiprimeD1BoundaryPlan.acquire (SemiprimeD1BoundaryPlan.graph net)).width := by
  let g:=SemiprimeD1BoundaryPlan.graph net
  let vs:=SemiprimeD1TensorNetwork.vertices net
  let plan:=SemiprimeD1BoundaryPlan.acquire g
  obtain ⟨i,hi,he⟩:=List.mem_iff_getElem.mp hv
  let c:=plan.colours.getD i 0
  have hic : i<plan.colours.length := by rw [SemiprimeD1BoundaryChoice.acquire_length]; exact hi
  have hc : c<plan.k := by
    unfold c
    rw [List.getD_eq_getElem _ _ hic]
    exact SemiprimeD1BoundaryChoice.acquire_colours g _ (List.getElem_mem hic)
  have hsel : v∈classVertices vs plan.colours c := by
    apply List.mem_map.mpr
    refine ⟨(v,i),List.mem_filter.mpr ⟨?_,?_⟩,rfl⟩
    · exact List.mk_mem_zipIdx_iff_getElem?.mpr (by rw [List.getElem?_eq_getElem hi,he])
    · simp only [c,beq_self_eq_true]
  exact (class_vertex_arity net hw plan.colours c v hsel).trans (acquired_bucket_le g c hc)

/-- A maximum of intrinsically bounded metadata stays bounded. -/
theorem maximum_le (ns : List Nat) (W : Nat) (h : ∀n∈ns,n≤ W) :
    SemiprimeD1BoundaryLeafReport.maximum ns≤ W := by
  induction ns with
  | nil => exact Nat.zero_le _
  | cons n ns ih =>
    exact max_le (h n List.mem_cons_self) (ih (fun x hx => h x (List.mem_cons_of_mem _ hx)))

/-- The runtime's own complete class/vertex/merge width is bounded by its own
acquired measured partition. No partition or width advice is an input. -/
theorem width_le_plan (ctx : SemiprimeD1JetAxes.Context) (net : Network)
    (hw : SemiprimeD1TensorNetwork.WellFormed net) :
    SemiprimeD1BoundaryLeafReport.width ctx net≤
      (SemiprimeD1BoundaryPlan.acquire (SemiprimeD1BoundaryPlan.graph net)).width := by
  unfold SemiprimeD1BoundaryLeafReport.width
  apply max_le
  · apply maximum_le
    intro n hn
    obtain ⟨c,hc,rfl⟩:=List.mem_map.mp hn
    exact acquired_bucket_le _ c (List.mem_range.mp hc)
  · apply max_le
    · apply maximum_le
      intro n hn
      obtain ⟨v,hv,rfl⟩:=List.mem_map.mp hn
      exact acquired_vertex_le net hw v hv
    · exact acquired_mergeWidth_le ctx net

/-- Complete current-context inventory and actual metadata polynomial factor.
The axis sum pays each stored bound even for arbitrarily many rank-one axes. -/
def reportFactor (ctx : SemiprimeD1JetAxes.Context) (net : Network) : Nat :=
  SemiprimeD1BoundaryLeafReport.polynomial ctx net (SemiprimeD1BoundaryLeafReport.width ctx net)+
    ctx.axes.length+ctx.axes.sum+ctx.rank+ctx.precision+1

/-- The closed native retained report has a single exponential in its own
acquired partition width. All coefficient delimiters, scalar precision,
axis metadata, and the actual full-jet arithmetic budget are retained. -/
theorem run_clock_acquired (ctx : SemiprimeD1JetAxes.Context) (net : Network)
    (hw : SemiprimeD1TensorNetwork.WellFormed net)
    (hg : SemiprimeD1LeafCounter.Good ctx (SemiprimeD1TensorNetwork.vertices net)) :
    (run ctx net).clock≤
      (SemiprimeD1BoundaryPlan.acquire (SemiprimeD1BoundaryPlan.graph net)).clock+
      10*inputMass (SemiprimeD1TensorNetwork.vertices net)+
      reportFactor ctx net*(2^(SemiprimeD1BoundaryPlan.acquire (SemiprimeD1BoundaryPlan.graph net)).width+1) := by
  apply (SemiprimeD1BoundaryLeafReport.run_clock ctx net hg).trans
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul
  · unfold reportFactor
    omega
  · exact Nat.add_le_add_right (Nat.pow_le_pow_right (by omega) (width_le_plan ctx net hw)) 1

end RiemannGaussian.SemiprimeD1BoundaryLeafLoad
