/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1BoundaryBudgetEnvelope
import RiemannGaussian.SemiprimeD1BoundaryPlanBudget

/-! # Uniform polynomial domination of the retained leaf metadata factor -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1BoundaryLeafPolynomial
open SemiprimeD1BoundaryLeaf
open SemiprimeD1BoundaryLeafBounds
open SemiprimeD1BoundaryLeafPorts
open SemiprimeD1BoundaryLeafLoad
open SemiprimeD1BoundaryBudgetEnvelope
open SemiprimeD1BoundaryRecordsGroupBounds
open SemiprimeD1BoundaryRecordsContractBounds
open SemiprimeD1BoundaryRecordsAttachBounds
open SemiprimeD1BoundaryRecordsSeedBounds
open SemiprimeD1BoundaryRecordsTableBounds
open SemiprimeD1JetAxes (Context)

/-- Literal original ordinals, each stored once. -/
def Ports (M : Nat) (xs : List Nat) : Prop := xs.Nodup ∧ ∀p∈xs,p<M

theorem ports_length (M : Nat) (xs : List Nat) (h : Ports M xs) : xs.length≤ M := by
  simpa only [List.length_range] using h.1.length_le_of_subset
    (fun p hp => List.mem_range.mpr (h.2 p hp))

theorem ports_mass (M : Nat) (xs : List Nat) (h : Ports M xs) : portMass xs≤ M*(M+1) := by
  have aux : ∀xs : List Nat, (∀p∈xs,p<M) → portMass xs≤ xs.length*(M+1) := by
    intro xs hh
    induction xs with
    | nil => simp [portMass]
    | cons p ps ih =>
      have hp:=hh p List.mem_cons_self
      have hs : Nat.size p≤ p := Nat.size_le.mpr p.lt_two_pow_self
      have ht:=ih (fun p hp => hh p (List.mem_cons_of_mem _ hp))
      simp only [portMass,List.map_cons,List.sum_cons,List.length_cons] at ht ⊢
      nlinarith
  exact (aux xs h.2).trans (Nat.mul_le_mul_right _ (ports_length M xs h))

theorem union_ports (M : Nat) (xs ys : List Nat) (hx : Ports M xs) (hy : Ports M ys) :
    Ports M (unionPorts xs ys) := by
  refine ⟨unionPorts_nodup xs ys,?_⟩
  intro p hp
  exact (unionPorts_mem xs ys p).mp hp |>.elim (hx.2 p) (hy.2 p)

theorem remaining_ports (M : Nat) (xs ys : List Nat) (hx : Ports M xs) (hy : Ports M ys) :
    Ports M (remainingPorts xs ys) := by
  refine ⟨remainingPorts_nodup xs ys,?_⟩
  intro p hp
  exact (union_ports M xs ys hx hy).2 p (List.mem_filter.mp hp).1

theorem class_ports (g : SemiprimeD1BoundaryPlan.Graph) (colours : List Nat) (c : Nat) :
    Ports g.edges.length (classPorts g colours c).1 ∧ Ports g.edges.length (classPorts g colours c).2 := by
  exact ⟨⟨(classPorts_nodup g colours c).1,fun p hp => (classPorts_lt g colours c p).1 hp⟩,
    ⟨(classPorts_nodup g colours c).2,fun p hp => (classPorts_lt g colours c p).2 hp⟩⟩

theorem attachment_mono (ctx : Context) (M P W : Nat) (hw : W≤ M) :
    attachment ctx M P W≤ attachment ctx M P M := by unfold attachment; gcongr

theorem contraction_mono (ctx : Context) (M P W : Nat) (hw : W≤ M) :
    contraction ctx M P W≤ contraction ctx M P M := by unfold contraction; gcongr

theorem seed_mono (ctx : Context) (n M : Nat) (h : n≤ M) : seedBudget ctx n≤ seedBudget ctx M := by
  unfold seedBudget recordBudget
  gcongr

/-- Uniform per-vertex factor, involving no table storage or assignment count. -/
def vertexFactor (ctx : Context) (M : Nat) : Nat :=
  tableBudget ctx M*(ctx.rank*(3*ctx.precision+4)+3)+
    2*attachment ctx M (M*(M+1)) M+M+5

/-- Uniform per-merge factor in original ordinal/context dimensions. -/
def mergeFactor (ctx : Context) (M : Nat) : Nat :=
  seedBudget ctx M+4*attachment ctx M (M*(M+1)) M+
    contraction ctx M (M*(M+1)) M+(2*M+1)^4+7

/-- Uniform per-class factor; every original vertex remains paid. -/
def bucketFactor (ctx : Context) (V M : Nat) : Nat :=
  seedBudget ctx M+V*vertexFactor ctx M+1+
    contraction ctx M (M*(M+1)) M+(2*V+M+1)^3+3

theorem table_mono (ctx : Context) (n M : Nat) (h : n≤ M) : tableBudget ctx n≤ tableBudget ctx M := by
  unfold tableBudget recordBudget
  gcongr

/-- Actual stage metadata is uniformly bounded by original ordinals. -/
theorem vertex_le (ctx : Context) (ports : List Nat) (K W M : Nat) (v : Vertex)
    (hp : Ports M ports) (hv : Ports M v.ports) (hk : K≤ M) (hw : W≤ M) :
    vertexPolynomial ctx ports K W v≤ vertexFactor ctx M := by
  have hlen:=ports_length M v.ports hv
  have ht:=table_mono ctx v.ports.length M hlen
  have ha:=(attach_le ctx ports v.ports K (recordBudget ctx v.ports.length) M (M*(M+1)) W
    (ports_mass M ports hp) (ports_mass M v.ports hv) hlen hk (record_le ctx _ _ hlen)).trans
      (attachment_mono ctx M (M*(M+1)) W hw)
  unfold vertexPolynomial vertexFactor
  gcongr

/-- Uniform actual merge factor in original source dimensions. -/
theorem merge_le (ctx : Context) (left right : SemiprimeD1BoundaryRecords.Tensor) (W M : Nat)
    (hl : Ports M left.ports) (hr : Ports M right.ports) (hw : W≤ M) :
    mergePolynomial ctx left right W≤ mergeFactor ctx M := by
  have hu:=union_ports M left.ports right.ports hl hr
  have hb:=remaining_ports M left.ports right.ports hl hr
  have hlen:=ports_length M _ hu
  have hleft:=ports_length M _ hl
  have hright:=ports_length M _ hr
  have htarget:=ports_length M _ hb
  have hs:=seed_mono ctx _ M hlen
  have hf:=(attach_le ctx _ _ _ _ M (M*(M+1)) W (ports_mass M _ hu) (ports_mass M _ hl)
    hleft hlen (record_le ctx _ _ hleft)).trans (attachment_mono ctx M (M*(M+1)) W hw)
  have hn:=(attach_le ctx _ _ _ _ M (M*(M+1)) W (ports_mass M _ hu) (ports_mass M _ hr)
    hright hlen (record_le ctx _ _ hright)).trans (attachment_mono ctx M (M*(M+1)) W hw)
  have hc:=(contract_le ctx _ _ _ M (M*(M+1)) W (ports_mass M _ hu) (ports_mass M _ hb)
    htarget hlen).trans (contraction_mono ctx M (M*(M+1)) W hw)
  unfold mergePolynomial mergeFactor
  have hp : (left.ports.length+right.ports.length+1)^4≤(2*M+1)^4 := by gcongr; omega
  nlinarith only [hs,hf,hn,hc,hp]

/-- Every actual merge output still uses each original ordinal at most once. -/
theorem merge_ports (ctx : Context) (left right : SemiprimeD1BoundaryRecords.Tensor) (M : Nat)
    (hl : Ports M left.ports) (hr : Ports M right.ports) :
    Ports M (SemiprimeD1BoundaryLeaf.merge ctx left right).value.ports := remaining_ports M _ _ hl hr

/-- Uniform consecutive-chain domination depends on merge count, never N. -/
theorem chain_le (ctx : Context) (W M : Nat) (first : SemiprimeD1BoundaryRecords.Tensor)
    (rest : List SemiprimeD1BoundaryRecords.Tensor) (hf : Ports M first.ports)
    (hr : ∀t∈rest,Ports M t.ports) (hw : W≤ M) :
    mergeChainPolynomial ctx W first rest≤ rest.length*(mergeFactor ctx M+3)+1 := by
  induction rest generalizing first with
  | nil => simp [mergeChainPolynomial]
  | cons next rest ih =>
    have hn:=hr next List.mem_cons_self
    have hm:=merge_le ctx first next W M hf hn hw
    have ht:=ih _ (merge_ports ctx first next M hf hn) (fun t ht => hr t (List.mem_cons_of_mem _ ht))
    simp only [mergeChainPolynomial,List.length_cons]
    nlinarith only [hm,ht]

/-- Complete selected-class local metadata inherits literal original bounds. -/
theorem selected_vertex_ports (net : Network) (hw : SemiprimeD1TensorNetwork.WellFormed net)
    (colours : List Nat) (c : Nat) (v : Vertex)
    (hv : v∈classVertices (SemiprimeD1TensorNetwork.vertices net) colours c) :
    Ports (SemiprimeD1BoundaryPlan.graph net).edges.length v.ports := by
  refine ⟨vertex_ports_nodup net hw v (SemiprimeD1BoundaryLeafReport.classVertices_member _ colours c v hv),?_⟩
  intro p hp
  exact (classPorts_lt _ colours c p).1 (class_vertex_ports_subset net hw colours c v hv p hp)

/-- Selection retains at most the original number of vertices, including isolates. -/
theorem selected_length (vs : List Vertex) (colours : List Nat) (c : Nat) :
    (classVertices vs colours c).length≤ vs.length := by
  unfold classVertices
  rw [List.length_map]
  exact (List.length_filter_le _ _).trans_eq (List.length_zipIdx)

/-- Uniform class domination in original graph and current-context dimensions. -/
theorem bucket_le (ctx : Context) (net : Network) (hwf : SemiprimeD1TensorNetwork.WellFormed net)
    (colours : List Nat) (c W : Nat) (hcol : colours.length=(SemiprimeD1BoundaryPlan.graph net).vertices)
    (hw : W≤(SemiprimeD1BoundaryPlan.graph net).edges.length) :
    bucketPolynomial ctx (SemiprimeD1BoundaryPlan.graph net) (SemiprimeD1TensorNetwork.vertices net) colours c W≤
      bucketFactor ctx (SemiprimeD1BoundaryPlan.graph net).vertices (SemiprimeD1BoundaryPlan.graph net).edges.length := by
  let g:=SemiprimeD1BoundaryPlan.graph net
  let vs:=SemiprimeD1TensorNetwork.vertices net
  let ports:=classPorts g colours c
  let selected:=classVertices vs colours c
  obtain ⟨hi,hb⟩:=class_ports g colours c
  have hlen:=ports_length _ _ hi
  have htarget:=ports_length _ _ hb
  have hs:=seed_mono ctx _ _ hlen
  have hc:=(contract_le ctx _ _ _ _ (g.edges.length*(g.edges.length+1)) W
    (ports_mass _ _ hi) (ports_mass _ _ hb) htarget hlen).trans
      (contraction_mono ctx _ _ W hw)
  have hvsum : (selected.map (vertexPolynomial ctx ports.1 ports.1.length W)).sum≤
      selected.length*vertexFactor ctx g.edges.length := by
    have aux : ∀xs : List Vertex, (∀v∈xs,v∈selected) →
        (xs.map (vertexPolynomial ctx ports.1 ports.1.length W)).sum≤ xs.length*vertexFactor ctx g.edges.length := by
      intro xs hx
      induction xs with
      | nil => simp
      | cons v xs ih =>
        have hv:=vertex_le ctx ports.1 ports.1.length W g.edges.length v hi
          (selected_vertex_ports net hwf colours c v (hx v List.mem_cons_self)) hlen hw
        have ht:=ih (fun v hv => hx v (List.mem_cons_of_mem _ hv))
        simp only [List.map_cons,List.sum_cons,List.length_cons]
        nlinarith only [hv,ht]
    exact aux _ (fun _ h => h)
  have hvcount : selected.length≤ g.vertices := selected_length vs colours c
  have hvsum':=hvsum.trans (Nat.mul_le_mul_right _ hvcount)
  unfold bucketPolynomial verticesPolynomial bucketFactor
  change _≤ seedBudget ctx g.edges.length+g.vertices*vertexFactor ctx g.edges.length+1+
    contraction ctx g.edges.length (g.edges.length*(g.edges.length+1)) g.edges.length+
    (2*g.vertices+g.edges.length+1)^3+3
  have hp : (g.vertices+g.edges.length+colours.length+1)^3≤(2*g.vertices+g.edges.length+1)^3 := by
    rw [show colours.length=g.vertices from hcol]
    apply Nat.pow_le_pow_left
    omega
  nlinarith only [hs,hc,hvsum',hp]

/-- The maximum fold preserves a common original-edge bound. -/
theorem foldl_le (xs : List Nat) (M a : Nat) (ha : a≤ M) (h : ∀x∈xs,x≤ M) : xs.foldl max a≤ M := by
  induction xs generalizing a with
  | nil => exact ha
  | cons x xs ih => exact ih _ (max_le ha (h x List.mem_cons_self)) (fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- Every acquired measured load is a subset of the original edge occurrences. -/
theorem plan_width_le (g : SemiprimeD1BoundaryPlan.Graph) :
    (SemiprimeD1BoundaryPlan.acquire g).width≤ g.edges.length := by
  apply foldl_le _ _ 0 (Nat.zero_le _)
  intro x hx
  obtain ⟨l,_,rfl⟩:=List.mem_map.mp hx
  exact List.length_filter_le _ _

/-- Uniform finite-sum inventory bound. -/
theorem sum_le {α : Type} (xs : List α) (f : α → Nat) (B : Nat)
    (h : ∀x∈xs,f x≤ B) : (xs.map f).sum≤ xs.length*B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx:=h x List.mem_cons_self
    have ht:=ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    nlinarith only [hx,ht]

/-- Fixed polynomial in original graph size and the whole current context. -/
def uniformFactor (ctx : Context) (V M : Nat) : Nat :=
  (M+2)*(bucketFactor ctx V M+mergeFactor ctx M+3)+1+
    ctx.rank*(3*ctx.precision+4)+1+(V+M+1)^4+11+
    ctx.axes.length+ctx.axes.sum+ctx.rank+ctx.precision+1

/-- Explicit stage factors are dominated by a fixed original-data polynomial. -/
theorem reportFactor_le (ctx : Context) (net : Network)
    (hwf : SemiprimeD1TensorNetwork.WellFormed net) :
    reportFactor ctx net≤ uniformFactor ctx
      (SemiprimeD1BoundaryPlan.graph net).vertices (SemiprimeD1BoundaryPlan.graph net).edges.length := by
  let g:=SemiprimeD1BoundaryPlan.graph net
  let vs:=SemiprimeD1TensorNetwork.vertices net
  let plan:=SemiprimeD1BoundaryPlan.acquire g
  let bs:=SemiprimeD1BoundaryLeafReport.buckets ctx net
  let first:=(bs.headD ⟨⟨[],[]⟩,1⟩).value
  let rest:=bs.tail.map SemiprimeD1BoundaryPlan.Work.value
  let W:=SemiprimeD1BoundaryLeafReport.width ctx net
  have hw : W≤ g.edges.length := (width_le_plan ctx net hwf).trans (plan_width_le g)
  have hcol:=SemiprimeD1BoundaryChoice.acquire_length g
  have hk : plan.k≤ g.edges.length+2 := (SemiprimeD1BoundaryChoice.chooseK_bounds g).2
  have hb:=sum_le (List.range plan.k) (fun c => bucketPolynomial ctx g vs plan.colours c W)
    (bucketFactor ctx g.vertices g.edges.length)
    (fun c _ => bucket_le ctx net hwf plan.colours c W hcol hw)
  rw [List.length_range] at hb
  have hp : ∀b∈bs,Ports g.edges.length b.value.ports := by
    intro b hb
    obtain ⟨c,_,rfl⟩:=List.mem_map.mp hb
    exact (class_ports g plan.colours c).2
  have hfirst : Ports g.edges.length first.ports := hp _
    (SemiprimeD1BoundaryLeafCanonical.headD_member bs ⟨⟨[],[]⟩,1⟩
      (SemiprimeD1BoundaryLeafCanonical.buckets_nonempty ctx net))
  have hrest : ∀t∈rest,Ports g.edges.length t.ports := by
    intro t ht
    obtain ⟨b,hb,rfl⟩:=List.mem_map.mp ht
    exact hp b (List.mem_of_mem_tail hb)
  have hc:=chain_le ctx W g.edges.length first rest hfirst hrest hw
  have hn : rest.length≤ plan.k := by
    change (bs.tail.map SemiprimeD1BoundaryPlan.Work.value).length≤ plan.k
    rw [List.length_map]
    have hlen : bs.length=plan.k := (List.length_map _).trans (List.length_range)
    rw [List.length_tail,hlen]
    omega
  have hc':=hc.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hn) 1)
  have hsum:=Nat.mul_le_mul_right (bucketFactor ctx g.vertices g.edges.length+mergeFactor ctx g.edges.length+3) hk
  unfold reportFactor SemiprimeD1BoundaryLeafReport.polynomial uniformFactor
  change _≤(g.edges.length+2)*(bucketFactor ctx g.vertices g.edges.length+mergeFactor ctx g.edges.length+3)+1+
    ctx.rank*(3*ctx.precision+4)+1+(g.vertices+g.edges.length+1)^4+11+
    ctx.axes.length+ctx.axes.sum+ctx.rank+ctx.precision+1
  change ((List.range plan.k).map (fun c => bucketPolynomial ctx g vs plan.colours c W)).sum+
    mergeChainPolynomial ctx W first rest+ctx.rank*(3*ctx.precision+4)+1+
    (g.vertices+g.edges.length+1)^4+11+ctx.axes.length+ctx.axes.sum+ctx.rank+ctx.precision+1≤_
  nlinarith only [hb,hc',hsum]

/-- Empty colour metadata selects every literal input vertex in colour zero. -/
theorem all_zero_class (vs : List Vertex) : classVertices vs [] 0=vs := by
  simp [classVertices]

/-- Every original literal vertex uses distinct original ordinals. -/
theorem original_vertex_ports (net : Network) (hw : SemiprimeD1TensorNetwork.WellFormed net)
    (v : Vertex) (hv : v∈SemiprimeD1TensorNetwork.vertices net) :
    Ports (SemiprimeD1BoundaryPlan.graph net).edges.length v.ports := by
  apply selected_vertex_ports net hw [] 0 v
  rw [all_zero_class]
  exact hv

/-- Literal input serialization factor in original dimensions. -/
def inputFactor (ctx : Context) (V M : Nat) : Nat :=
  V*(ctx.rank*(3*ctx.precision+4)+3+M*(M+1)+3)

/-- Stored local truth tables are charged once, with their arities bounded by
an actual acquired class load. This avoids a second exponential in input mass. -/
theorem inputMass_le (ctx : Context) (net : Network)
    (hw : SemiprimeD1TensorNetwork.WellFormed net)
    (hg : SemiprimeD1LeafCounter.Good ctx (SemiprimeD1TensorNetwork.vertices net)) :
    inputMass (SemiprimeD1TensorNetwork.vertices net)≤
      inputFactor ctx (SemiprimeD1BoundaryPlan.graph net).vertices (SemiprimeD1BoundaryPlan.graph net).edges.length*
      (2^(SemiprimeD1BoundaryPlan.acquire (SemiprimeD1BoundaryPlan.graph net)).width+1) := by
  let g:=SemiprimeD1BoundaryPlan.graph net
  let vs:=SemiprimeD1TensorNetwork.vertices net
  let N:=2^(SemiprimeD1BoundaryPlan.acquire g).width
  let C:=ctx.rank*(3*ctx.precision+4)+3
  let P:=g.edges.length*(g.edges.length+1)
  have hsum:=sum_le vs (fun v => SemiprimeD1TensorTables.storage v.table+portMass v.ports+3)
    ((C+P+3)*(N+1)) (by
      intro v hv
      have hs:=SemiprimeD1TensorTables.storage_bound ctx v.table (hg v hv)
      have hdeg:=acquired_vertex_le net hw v hv
      have hpow : (2:Nat)^v.ports.length≤ N := Nat.pow_le_pow_right (by omega) hdeg
      have hs' : SemiprimeD1TensorTables.storage v.table≤ C*N :=
        (Nat.le_add_right _ 1).trans (hs.trans (Nat.mul_le_mul_left C hpow))
      have hp:=ports_mass g.edges.length v.ports (original_vertex_ports net hw v hv)
      change portMass v.ports≤ P at hp
      nlinarith only [hs',hp,Nat.zero_le N,Nat.zero_le C,Nat.zero_le P])
  change inputMass vs≤ inputFactor ctx g.vertices g.edges.length*(N+1)
  unfold inputMass
  change (vs.map (fun v => SemiprimeD1TensorTables.storage v.table+portMass v.ports+3)).sum≤_
  apply hsum.trans_eq
  unfold inputFactor
  change vs.length*((C+P+3)*(N+1))=vs.length*(C+P+3)*(N+1)
  ring

/-- Fixed polynomial envelope of the complete native retained leaf report. -/
def closedBudget (ctx : Context) (V M : Nat) : Nat :=
  SemiprimeD1BoundaryPlanBudget.acquisitionBudget V M+uniformFactor ctx V M+10*inputFactor ctx V M

/-- The actual closed valid leaf has polynomial current-context/original-graph
work times a single exponential in its own acquired measured width. This
certifies the mixed native retained report, not a primitive finite machine. -/
theorem run_clock_polynomial (ctx : Context) (net : Network)
    (hw : SemiprimeD1TensorNetwork.WellFormed net)
    (hg : SemiprimeD1LeafCounter.Good ctx (SemiprimeD1TensorNetwork.vertices net)) :
    (run ctx net).clock≤
      closedBudget ctx (SemiprimeD1BoundaryPlan.graph net).vertices (SemiprimeD1BoundaryPlan.graph net).edges.length*
        (2^(SemiprimeD1BoundaryPlan.acquire (SemiprimeD1BoundaryPlan.graph net)).width+1) := by
  have hrun:=run_clock_acquired ctx net hw hg
  have hfactor:=reportFactor_le ctx net hw
  have hmass:=inputMass_le ctx net hw hg
  have hplan:=SemiprimeD1BoundaryPlanBudget.acquire_clock (SemiprimeD1BoundaryPlan.graph net)
  have hplan':=hplan.trans (Nat.le_mul_of_pos_right _
    (Nat.succ_pos (2^(SemiprimeD1BoundaryPlan.acquire (SemiprimeD1BoundaryPlan.graph net)).width)))
  have hfactor':=Nat.mul_le_mul_right
    (2^(SemiprimeD1BoundaryPlan.acquire (SemiprimeD1BoundaryPlan.graph net)).width+1) hfactor
  unfold closedBudget
  nlinarith only [hrun,hmass,hplan',hfactor']

end RiemannGaussian.SemiprimeD1BoundaryLeafPolynomial
