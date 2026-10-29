/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1BoundaryLeafBounds

/-! # Closed retained native leaf report in actual measured width -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1BoundaryLeafReport
open SemiprimeD1BoundaryLeaf
open SemiprimeD1BoundaryLeafBounds
open SemiprimeD1BoundaryRecordsGroupBounds
open SemiprimeD1JetAxes (Context)

/-- Actual maximum, with zero as the empty-list default. -/
def maximum : List Nat → Nat
  | [] => 0
  | n::ns => max n (maximum ns)

theorem member_le_maximum (ns : List Nat) (n : Nat) (h : n∈ns) : n≤ maximum ns := by
  induction ns with
  | nil => simp at h
  | cons a ns ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact (ih h).trans (Nat.le_max_right _ _)

/-- Actual class tensors acquired by the closed deterministic source. -/
def buckets (ctx : Context) (net : Network) :=
  let g:=SemiprimeD1BoundaryPlan.graph net
  let plan:=SemiprimeD1BoundaryPlan.acquire g
  (List.range plan.k).map (bucket ctx g (SemiprimeD1TensorNetwork.vertices net) plan.colours)

/-- Intrinsic execution width, read from actual classes and consecutive merges.
It is never accepted as advice by the runtime. -/
def width (ctx : Context) (net : Network) : Nat :=
  let g:=SemiprimeD1BoundaryPlan.graph net
  let vs:=SemiprimeD1TensorNetwork.vertices net
  let plan:=SemiprimeD1BoundaryPlan.acquire g
  let bs:=buckets ctx net
  max (maximum ((List.range plan.k).map (fun c => (classPorts g plan.colours c).1.length)))
    (max (maximum (vs.map (fun v => v.ports.length)))
      (mergeWidth ctx (bs.headD ⟨⟨[],[]⟩,1⟩).value (bs.tail.map SemiprimeD1BoundaryPlan.Work.value)))

/-- Polynomial metadata factor retains every actual class/merge port list.
Partition acquisition and literal input acquisition are kept additive. -/
def polynomial (ctx : Context) (net : Network) (W : Nat) : Nat :=
  let g:=SemiprimeD1BoundaryPlan.graph net
  let vs:=SemiprimeD1TensorNetwork.vertices net
  let plan:=SemiprimeD1BoundaryPlan.acquire g
  let bs:=buckets ctx net
  ((List.range plan.k).map (fun c => bucketPolynomial ctx g vs plan.colours c W)).sum+
  mergeChainPolynomial ctx W (bs.headD ⟨⟨[],[]⟩,1⟩).value
    (bs.tail.map SemiprimeD1BoundaryPlan.Work.value)+ctx.rank*(3*ctx.precision+4)+1+
  (g.vertices+g.edges.length+1)^4+11

/-- Selected colour vertices are literal members of the stored input. -/
theorem classVertices_member (vs : List Vertex) (colours : List Nat) (c : Nat)
    (v : Vertex) (h : v∈classVertices vs colours c) : v∈vs := by
  obtain ⟨pair,hp,rfl⟩:=List.mem_map.mp h
  have hz:= (List.mem_filter.mp hp).1
  exact List.fst_mem_of_mem_zipIdx hz

/-- Exact full native retained report, with a single measured exponential.
This is not a primitive finite-machine certification theorem. -/
theorem run_clock (ctx : Context) (net : Network)
    (hgood : SemiprimeD1LeafCounter.Good ctx (SemiprimeD1TensorNetwork.vertices net)) :
    (run ctx net).clock≤
      (SemiprimeD1BoundaryPlan.acquire (SemiprimeD1BoundaryPlan.graph net)).clock+
      10*inputMass (SemiprimeD1TensorNetwork.vertices net)+
      polynomial ctx net (width ctx net)*(2^(width ctx net)+1) := by
  let g:=SemiprimeD1BoundaryPlan.graph net
  let vs:=SemiprimeD1TensorNetwork.vertices net
  let plan:=SemiprimeD1BoundaryPlan.acquire g
  let bs:=buckets ctx net
  let first:=(bs.headD ⟨⟨[],[]⟩,1⟩).value
  let rest:=bs.tail.map SemiprimeD1BoundaryPlan.Work.value
  let W:=width ctx net
  have hclass : ∀c∈List.range plan.k,(classPorts g plan.colours c).1.length≤ W := by
    intro c hc
    apply (member_le_maximum
      ((List.range plan.k).map (fun c => (classPorts g plan.colours c).1.length))
      ((classPorts g plan.colours c).1.length) (List.mem_map.mpr ⟨c,hc,rfl⟩)).trans
    exact Nat.le_max_left _ _
  have hdegree : ∀v∈vs,v.ports.length≤ W := by
    intro v hv
    apply (member_le_maximum (vs.map (fun v => v.ports.length)) v.ports.length
      (List.mem_map.mpr ⟨v,hv,rfl⟩)).trans
    exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hbs : bs≠[] := SemiprimeD1BoundaryLeafCanonical.buckets_nonempty ctx net
  have hready : ∀b∈bs,Ready ctx W b.value := by
    intro b hb
    obtain ⟨c,hc,rfl⟩:=List.mem_map.mp hb
    exact bucket_ready ctx g vs plan.colours c W (hclass c hc)
  have hf : Ready ctx W first := hready _
    (SemiprimeD1BoundaryLeafCanonical.headD_member bs ⟨⟨[],[]⟩,1⟩ hbs)
  have hr : ∀t∈rest,Ready ctx W t := by
    intro t ht
    obtain ⟨b,hb,rfl⟩:=List.mem_map.mp ht
    exact hready b (List.mem_of_mem_tail hb)
  have hw : mergeWidth ctx first rest≤ W :=
    (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hm:=mergeAll_clock ctx W first rest hf hr hw
  have hb : (bs.map SemiprimeD1BoundaryPlan.Work.clock).sum≤
      (((List.range plan.k).map (fun c => bucketPolynomial ctx g vs plan.colours c W)).sum)*(2^W+1) := by
    have aux : ∀cs : List Nat, (∀c∈cs,c∈List.range plan.k) →
        ((cs.map (bucket ctx g vs plan.colours)).map SemiprimeD1BoundaryPlan.Work.clock).sum≤
        ((cs.map (fun c => bucketPolynomial ctx g vs plan.colours c W)).sum)*(2^W+1) := by
      intro cs hc
      induction cs with
      | nil => simp
      | cons c cs ih =>
        have hh:=bucket_clock ctx g vs plan.colours c W
          (fun v hv => hgood v (classVertices_member vs plan.colours c v hv))
          (fun v hv => hdegree v (classVertices_member vs plan.colours c v hv)) (hclass c (hc c List.mem_cons_self))
        have ht:=ih (fun x hx => hc x (List.mem_cons_of_mem _ hx))
        simp only [List.map_cons,List.sum_cons]
        nlinarith only [hh,ht]
    exact aux _ (fun _ h => h)
  have hout:=SemiprimeD1BoundaryLeafCanonical.acquire_tensor ctx net
  have headgood : SemiprimeD1TensorTables.GoodWords ctx
      ((acquire ctx net).tensor.entries.headD ⟨[],[]⟩).words :=
    hout.1 _ (SemiprimeD1BoundaryLeafCanonical.headD_member _ ⟨[],[]⟩ hout.2)
  have hcopy:=SemiprimeD1JetAxes.copyVector_clock_le
    (((acquire ctx net).tensor.entries.headD ⟨[],[]⟩).words) ctx.precision
    (fun w hw => (headgood.2 w hw).2)
  rw [headgood.1] at hcopy
  have hcopy' := hcopy.trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos (2^W)))
  have hpad : (g.vertices+g.edges.length+1)^4+11≤
      ((g.vertices+g.edges.length+1)^4+11)*(2^W+1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos (2^W))
  change plan.clock+(bs.map SemiprimeD1BoundaryPlan.Work.clock).sum+(mergeAll ctx first rest).clock+
    (SemiprimeD1JetAxes.copyVector (((acquire ctx net).tensor.entries.headD ⟨[],[]⟩).words)).2+
    10*inputMass vs+(g.vertices+g.edges.length+1)^4+11≤_
  change _≤ plan.clock+10*inputMass vs+
    ((((List.range plan.k).map (fun c => bucketPolynomial ctx g vs plan.colours c W)).sum)+
      mergeChainPolynomial ctx W first rest+ctx.rank*(3*ctx.precision+4)+1+
      (g.vertices+g.edges.length+1)^4+11)*(2^W+1)
  nlinarith only [hb,hm,hcopy',hpad]

end RiemannGaussian.SemiprimeD1BoundaryLeafReport
