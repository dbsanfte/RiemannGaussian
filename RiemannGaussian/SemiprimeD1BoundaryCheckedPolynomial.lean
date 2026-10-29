/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1BoundaryLeafOriginalRate

/-! # Actual checked boundary leaf report, including paid validation -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1BoundaryCheckedPolynomial
open SemiprimeD1BoundaryLeaf
open SemiprimeD1BoundaryLeafPolynomial
open SemiprimeD1BoundaryLeafOriginalRate
open SemiprimeD1JetAxes (Context)
open SemiprimeReportPolynomialGrowth
open SemiprimeD1PackingReady SemiprimeD1OriginalStateResources
open SemiprimeD1OriginalEnvelopeRate SemiprimeD1OriginalScalarResources

/-- Metadata traversed by the actual layout and payload checker. -/
def metadata (ctx : Context) (V M : Nat) : Nat := V+M+V*M+ctx.axes.sum+ctx.precision+2

/-- Fixed complete checked-leaf factor, including all validation work. -/
def checkedBudget (ctx : Context) (V M : Nat) : Nat :=
  closedBudget ctx V M+(metadata ctx V M+1)^6+
    20*(inputFactor ctx V M+1)*(metadata ctx V M+1)^2+3

/-- Exact checked source uses its accepting branch on canonical original data. -/
theorem checked_clock (ctx : Context) (net : Network)
    (hw : SemiprimeD1TensorNetwork.WellFormed net)
    (hg : SemiprimeD1LeafCounter.Good ctx (SemiprimeD1TensorNetwork.vertices net)) :
    (checked ctx net).clock≤ checkedBudget ctx
      (SemiprimeD1BoundaryPlan.graph net).vertices (SemiprimeD1BoundaryPlan.graph net).edges.length*
      (2^(SemiprimeD1BoundaryPlan.acquire (SemiprimeD1BoundaryPlan.graph net)).width+1) := by
  let g:=SemiprimeD1BoundaryPlan.graph net
  let vs:=SemiprimeD1TensorNetwork.vertices net
  let N:=2^(SemiprimeD1BoundaryPlan.acquire g).width+1
  have hr:=run_clock_polynomial ctx net hw hg
  have hi:=inputMass_le ctx net hw hg
  have hscope:=sum_le vs (fun v => v.ports.length) g.edges.length
    (fun v hv => ports_length _ _ (original_vertex_ports net hw v hv))
  have hmeta : vs.length+SemiprimeD1TensorNetwork.edgeCount net+
      (vs.map (fun v => v.ports.length)).sum+ctx.axes.sum+ctx.precision+2≤ metadata ctx g.vertices g.edges.length := by
    rw [←SemiprimeD1BoundaryPlan.graph_edges_length net]
    change vs.length+g.edges.length+_+ctx.axes.sum+ctx.precision+2≤_
    unfold metadata
    change vs.length+g.edges.length+_+ctx.axes.sum+ctx.precision+2≤
      vs.length+g.edges.length+vs.length*g.edges.length+ctx.axes.sum+ctx.precision+2
    omega
  have hN : 1≤ N := Nat.le_add_left _ _
  have hi' : inputMass vs+1≤(inputFactor ctx g.vertices g.edges.length+1)*N := by
    change inputMass vs≤ inputFactor ctx g.vertices g.edges.length*N at hi
    nlinarith only [hi,hN]
  have hv : (validate ctx net).clock≤
      (metadata ctx g.vertices g.edges.length+1)^6+
        20*((inputFactor ctx g.vertices g.edges.length+1)*N)*(metadata ctx g.vertices g.edges.length+1)^2 := by
    change (vs.length+SemiprimeD1TensorNetwork.edgeCount net+
      (vs.map (fun v => v.ports.length)).sum+ctx.axes.sum+ctx.precision+2+1)^6+
      20*(inputMass vs+1)*(vs.length+SemiprimeD1TensorNetwork.edgeCount net+
      (vs.map (fun v => v.ports.length)).sum+ctx.axes.sum+ctx.precision+2+1)^2≤_
    exact Nat.add_le_add (Nat.pow_le_pow_left (Nat.add_le_add_right hmeta 1) 6)
      (Nat.mul_le_mul (Nat.mul_le_mul_left 20 hi')
        (Nat.pow_le_pow_left (Nat.add_le_add_right hmeta 1) 2))
  have hbase : (metadata ctx g.vertices g.edges.length+1)^6≤
      (metadata ctx g.vertices g.edges.length+1)^6*N := Nat.le_mul_of_pos_right _ (by omega)
  have hpad : 3≤3*N := by omega
  have hvalid : (validate ctx net).value=true := (validate_correct ctx net).mpr ⟨hw,hg⟩
  simp only [checked,hvalid,ite_true]
  unfold checkedBudget
  change _≤(closedBudget ctx g.vertices g.edges.length+(metadata ctx g.vertices g.edges.length+1)^6+
    20*(inputFactor ctx g.vertices g.edges.length+1)*(metadata ctx g.vertices g.edges.length+1)^2+3)*N
  change (run ctx net).clock≤ closedBudget ctx g.vertices g.edges.length*N at hr
  nlinarith only [hr,hv,hbase,hpad]

/-- One-variable validation polynomial with a separately paid axis inventory. -/
def checkedEnvelope (S : Nat) : Nat  := SemiprimeD1BoundaryLeafOriginalRate.envelope S+(3*S+2*S*S+3)^6+
  20*(inputFactor (capContext S) S S+1)*(3*S+2*S*S+3)^2+3

/-- Complete checked-leaf factor fits the same actual scalar-field caps. -/
theorem checkedBudget_le (ctx : Context) (V M S : Nat)
    (hV : V≤ S) (hM : M≤ S) (ha : ctx.axes.length≤ S) (hu : ctx.axes.sum≤ S*S)
    (hr : ctx.rank≤ S) (hp : ctx.precision≤ S) : checkedBudget ctx V M≤ checkedEnvelope S := by
  have hb:=budget_le_envelope ctx V M S hV hM ha hu hr hp
  have hm : metadata ctx V M+1≤3*S+2*S*S+3 := by
    unfold metadata
    have hmul:=Nat.mul_le_mul hV hM
    nlinarith only [hV,hM,hu,hp,hmul]
  have hi : inputFactor ctx V M≤ inputFactor (capContext S) S S := by
    unfold inputFactor
    simp only [capContext,SemiprimeD1JetAxes.Context.rank,List.prod_append,List.prod_replicate,List.prod_cons,List.prod_nil,one_pow,Nat.one_mul,Nat.mul_one]
    have hr':ctx.axes.prod≤ S+1 := hr.trans (Nat.le_succ _)
    gcongr
  unfold checkedBudget checkedEnvelope
  gcongr

/-- Validation adds only fixed arithmetic, hence has fixed monomial witnesses. -/
theorem checkedEnvelope_monomial : Bound checkedEnvelope := by
  unfold checkedEnvelope
  apply add_bound
  · apply add_bound
    · apply add_bound
      · exact envelope_monomial
      · boundArithmetic
    · simp only [inputFactor,capContext,SemiprimeD1JetAxes.Context.rank,List.prod_append,List.prod_replicate,
        List.prod_cons,List.prod_nil,one_pow,Nat.one_mul,Nat.mul_one]
      boundArithmetic
  · exact constant_bound 3

/-- Full original family resources bound paid validation and contraction together. -/
theorem checked_original_budget_le (ctx : Context) (V M s : Nat) (hl : 1000≤ logarithm s)
    (hV : V≤5*s) (hM : M≤ s+1) (ha : ctx.axes.length≤ logarithm s+1)
    (hq : ∀q∈ctx.axes,q≤4*s) (hr : ctx.rank≤ rankCap s) (hp : ctx.precision≤ precisionCap s) :
    checkedBudget ctx V M≤ checkedEnvelope (scalar s+1) := by
  obtain ⟨hs,hv,hlength⟩:=base_caps s hl
  have ha':ctx.axes.length≤ scalar s := ha.trans hlength
  have hq':∀q∈ctx.axes,q≤ scalar s := by intro q hqmem; exact (hq q hqmem).trans (by omega)
  have hu:ctx.axes.sum≤(scalar s+1)*(scalar s+1) :=
    (axes_sum_le ctx.axes (scalar s) hq').trans
      (Nat.mul_le_mul (ha'.trans (Nat.le_succ _)) (Nat.le_succ _))
  exact checkedBudget_le ctx V M (scalar s+1) (by omega) (by omega) (by omega) hu
    ((hr.trans (rankCap_le s hl)).trans (Nat.le_succ _))
    ((hp.trans (precisionCap_le s hl)).trans (Nat.le_succ _))

/-- Uniform fixed original-scale reserve for the actual checked recursion leaf.
Validation is included. The old full-enumeration leaf allowance is used only as
an upper envelope for this new source's independently proved native report. -/
theorem checked_original_polynomial : ∃B k : Nat, 0<B ∧
    ∀ (s : Nat) (ctx : Context) (net : Network), 1000≤ logarithm s →
    SemiprimeD1TensorNetwork.WellFormed net →
    SemiprimeD1LeafCounter.Good ctx (SemiprimeD1TensorNetwork.vertices net) →
    (SemiprimeD1BoundaryPlan.graph net).vertices≤5*s →
    (SemiprimeD1BoundaryPlan.graph net).edges.length≤ s+1 →
    (SemiprimeD1BoundaryPlan.graph net).edges.length≤ SemiprimeD1Schedule.leafSize s (logarithm s) →
    ctx.axes.length≤ logarithm s+1 → (∀q∈ctx.axes,q≤4*s) →
    ctx.rank≤ rankCap s → ctx.precision≤ precisionCap s →
    (checked ctx net).clock≤ B*(scalar s+1)^k*2^(SemiprimeD1Schedule.leafSize s (logarithm s)) := by
  obtain ⟨C,k,hmono⟩:=checkedEnvelope_monomial
  refine ⟨2*C*2^k+1,k,by omega,?_⟩
  intro s ctx net hl hw hg hV hM hleaf ha hq hr hp
  let g:=SemiprimeD1BoundaryPlan.graph net
  let L:=SemiprimeD1Schedule.leafSize s (logarithm s)
  have hb:=(checked_original_budget_le ctx g.vertices g.edges.length s hl hV hM ha hq hr hp).trans
    (hmono (scalar s+1))
  have hwidth : (SemiprimeD1BoundaryPlan.acquire g).width≤ L := (plan_width_le g).trans hleaf
  have hn : 2^(SemiprimeD1BoundaryPlan.acquire g).width+1≤2*2^L := by
    have hh:=Nat.pow_le_pow_right (by omega : 0<(2:Nat)) hwidth
    have ho : 1≤(2:Nat)^L := Nat.one_le_two_pow
    omega
  have hs : scalar s+2≤2*(scalar s+1) := by omega
  calc
    _ ≤ (C*(scalar s+2)^k)*(2*2^L) := (checked_clock ctx net hw hg).trans (Nat.mul_le_mul hb hn)
    _ ≤ (C*(2*(scalar s+1))^k)*(2*2^L) := by gcongr
    _ = (2*C*2^k)*(scalar s+1)^k*2^L := by rw [mul_pow]; ring
    _ ≤ _ := by gcongr; omega

end RiemannGaussian.SemiprimeD1BoundaryCheckedPolynomial
