/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1BoundaryLeafPolynomial
import RiemannGaussian.SemiprimeD1BoundaryPartitionOriginalRate
import RiemannGaussian.SemiprimeD1BoundaryNetworkDegree
import RiemannGaussian.SemiprimeD1OriginalScalarResources
import RiemannGaussian.SemiprimeReportPolynomialGrowth

/-! # Uniform leading half exponent for the actual retained native boundary leaf -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1BoundaryLeafOriginalRate
open Filter
open SemiprimeD1JetAxes (Context)
open SemiprimeD1BoundaryLeafPolynomial
open SemiprimeD1PackingReady SemiprimeD1OriginalStateResources
open SemiprimeD1OriginalEnvelopeRate SemiprimeD1OriginalScalarResources
open SemiprimeReportPolynomialGrowth

/-- Synthetic polynomial cap, with separately paid axis inventory. -/
def capContext (S : Nat) : Context := ⟨List.replicate (S*S) 1++[S+1],S⟩

/-- Fixed one-variable polynomial dominating the complete closed leaf factor. -/
def envelope (S : Nat) : Nat := closedBudget (capContext S) S S

/-- All concrete budget arithmetic has fixed monomial witnesses. -/
theorem envelope_monomial : Bound envelope := by
  change Bound (fun S => closedBudget (capContext S) S S)
  simp only [closedBudget,
    SemiprimeD1BoundaryPlanBudget.acquisitionBudget,SemiprimeD1BoundaryPlanBudget.candidateBudget,
    SemiprimeD1BoundaryPlanBudget.potentialBudget,SemiprimeD1BoundaryPlanBudget.localBudget,
    uniformFactor,bucketFactor,mergeFactor,vertexFactor,inputFactor,
    SemiprimeD1BoundaryBudgetEnvelope.attachment,SemiprimeD1BoundaryBudgetEnvelope.contraction,
    SemiprimeD1BoundaryBudgetEnvelope.projection,
    SemiprimeD1BoundaryRecordsSeedBounds.seedBudget,SemiprimeD1LeafCounterBounds.oneBudget,
    SemiprimeD1BoundaryRecordsTableBounds.tableBudget,
    SemiprimeD1BoundaryRecordsGroupBounds.recordBudget,SemiprimeD1BoundaryRecordsGroupBounds.sumBudget,
    SemiprimeD1BoundaryRecordsAttachBounds.requestBudget,
    SemiprimeD1BoundaryRecordsLookupBounds.joinBudget,SemiprimeD1BoundaryRecordsLookupBounds.arithmeticBudget,
    SemiprimeD1JetRingBounds.mulBudget,SemiprimeD1JetRingBounds.mulAtBudget,SemiprimeD1JetRingBounds.termBudget,
    capContext,SemiprimeD1JetAxes.Context.rank,List.prod_append,List.prod_replicate,List.prod_cons,
    List.prod_nil,one_pow,List.length_append,List.length_replicate,List.length_cons,List.length_nil,
    List.sum_append,List.sum_replicate,List.sum_cons,List.sum_nil,nsmul_eq_mul,Nat.cast_id,Nat.mul_one,Nat.one_mul,Nat.add_zero]
  boundArithmetic

/-- Actual scalar fields, including every unit axis, fit the cap polynomial. -/
theorem budget_le_envelope (ctx : Context) (V M S : Nat)
    (hV : V≤ S) (hM : M≤ S) (ha : ctx.axes.length≤ S) (hu : ctx.axes.sum≤ S*S)
    (hr : ctx.rank≤ S) (hp : ctx.precision≤ S) : closedBudget ctx V M≤ envelope S := by
  have ha' : ctx.axes.length≤ S*S+1 := by nlinarith
  have hu' : ctx.axes.sum≤ S*S+(S+1) := by omega
  have hr' : ctx.rank≤ S+1 := by omega
  simp only [envelope,closedBudget,
    SemiprimeD1BoundaryPlanBudget.acquisitionBudget,SemiprimeD1BoundaryPlanBudget.candidateBudget,
    SemiprimeD1BoundaryPlanBudget.potentialBudget,SemiprimeD1BoundaryPlanBudget.localBudget,
    uniformFactor,bucketFactor,mergeFactor,vertexFactor,inputFactor,
    SemiprimeD1BoundaryBudgetEnvelope.attachment,SemiprimeD1BoundaryBudgetEnvelope.contraction,
    SemiprimeD1BoundaryBudgetEnvelope.projection,
    SemiprimeD1BoundaryRecordsSeedBounds.seedBudget,SemiprimeD1LeafCounterBounds.oneBudget,
    SemiprimeD1BoundaryRecordsTableBounds.tableBudget,
    SemiprimeD1BoundaryRecordsGroupBounds.recordBudget,SemiprimeD1BoundaryRecordsGroupBounds.sumBudget,
    SemiprimeD1BoundaryRecordsAttachBounds.requestBudget,
    SemiprimeD1BoundaryRecordsLookupBounds.joinBudget,SemiprimeD1BoundaryRecordsLookupBounds.arithmeticBudget,
    SemiprimeD1JetRingBounds.mulBudget,SemiprimeD1JetRingBounds.mulAtBudget,SemiprimeD1JetRingBounds.termBudget,
    capContext,SemiprimeD1JetAxes.Context.rank,List.prod_append,List.prod_replicate,List.prod_cons,
    List.prod_nil,one_pow,List.length_append,List.length_replicate,List.length_cons,List.length_nil,
    List.sum_append,List.sum_replicate,List.sum_cons,List.sum_nil,nsmul_eq_mul,Nat.cast_id,Nat.mul_one,Nat.one_mul,Nat.add_zero]
  gcongr <;> exact hr'

/-- Every fixed cubic logarithmic exponent is negligible at the stopped-leaf scale. -/
theorem eventually_poly_exponent_small (A : Nat) (e : Real) (he : 0<e) :
    ∀ᶠ s : Nat in atTop, (A : Real)*((logarithm s : Real)+1)^3≤
      e*((s : Real)/Real.sqrt (logarithm s : Real)) := by
  have ht : Tendsto logarithm atTop atTop :=
    SemiprimeCounterRate.tendsto_clog_two_atTop.comp (tendsto_add_atTop_nat 2)
  have htR : Tendsto (fun s : Nat => (logarithm s : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp ht
  filter_upwards [SemiprimeD1AuxiliaryRate.eventually_log_power 5,
    htR.eventually (eventually_ge_atTop (max 1 (8*(A:Real)/e)))] with s hs hl
  have h1 : (1:Real)≤ logarithm s := (le_max_left _ _).trans hl
  have hA : 8*(A:Real)≤ e*(logarithm s:Real) := by
    have hh:8*(A:Real)/e≤(logarithm s:Real) := (le_max_right _ _).trans hl
    nlinarith [(div_le_iff₀ he).mp hh]
  have hpow : (logarithm s:Real)^5≤ s := by exact_mod_cast hs
  have ht0 : 0<Real.sqrt (logarithm s:Real) := Real.sqrt_pos.mpr (by linarith)
  have hroot : Real.sqrt (logarithm s:Real)≤(logarithm s:Real) := by
    have hh:=Real.sq_sqrt (show (0:Real)≤ logarithm s by positivity)
    nlinarith only [hh,h1,Real.sqrt_nonneg (logarithm s:Real)]
  have hc : ((logarithm s:Real)+1)^3≤8*(logarithm s:Real)^3 := by
    have hh:=pow_le_pow_left₀ (by positivity : (0:Real)≤(logarithm s:Real)+1)
      (by linarith : (logarithm s:Real)+1≤2*(logarithm s:Real)) 3
    nlinarith only [hh]
  rw [←mul_div_assoc]
  apply (le_div_iff₀ ht0).mpr
  calc
    _ ≤ (A:Real)*(8*(logarithm s:Real)^3)*(logarithm s:Real) := by gcongr
    _ = (8*(A:Real))*(logarithm s:Real)^4 := by ring
    _ ≤ (e*(logarithm s:Real))*(logarithm s:Real)^4 := mul_le_mul_of_nonneg_right hA (by positivity)
    _ = e*(logarithm s:Real)^5 := by ring
    _ ≤ e*(s:Real) := mul_le_mul_of_nonneg_left hpow he.le

/-- Whole-axis inventory is bounded from the actual list and each actual bound. -/
theorem axes_sum_le (xs : List Nat) (S : Nat) (h : ∀q∈xs,q≤ S) : xs.sum≤ xs.length*S := by
  induction xs with
  | nil => simp
  | cons q qs ih =>
    have hq:=h q List.mem_cons_self
    have ht:=ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    simp only [List.sum_cons,List.length_cons]
    nlinarith only [hq,ht]

/-- Original family resources bound the complete native polynomial factor,
including axis count/sum separately from dense rank. -/
theorem original_budget_le (ctx : Context) (V M s : Nat) (hl : 1000≤ logarithm s)
    (hV : V≤5*s) (hM : M≤ s+1) (ha : ctx.axes.length≤ logarithm s+1)
    (hq : ∀q∈ctx.axes,q≤4*s) (hr : ctx.rank≤ rankCap s) (hp : ctx.precision≤ precisionCap s) :
    closedBudget ctx V M≤ envelope (scalar s+1) := by
  obtain ⟨hs,hv,hlength⟩:=base_caps s hl
  have ha':ctx.axes.length≤ scalar s := ha.trans hlength
  have hq':∀q∈ctx.axes,q≤ scalar s := by intro q hqmem; exact (hq q hqmem).trans (by omega)
  have hu:ctx.axes.sum≤(scalar s+1)*(scalar s+1) :=
    (axes_sum_le ctx.axes (scalar s) hq').trans
      (Nat.mul_le_mul (ha'.trans (Nat.le_succ _)) (Nat.le_succ _))
  exact budget_le_envelope ctx V M (scalar s+1) (by omega) (by omega) (by omega) hu
    ((hr.trans (rankCap_le s hl)).trans (Nat.le_succ _))
    ((hp.trans (precisionCap_le s hl)).trans (Nat.le_succ _))

/-- A fixed coefficient and monomial exponent produce one explicit binary
polynomial-overhead exponent, with no table enumeration hidden inside it. -/
theorem monomial_to_power (C k s : Nat) :
    C*(scalar s+2)^k≤2^(C+((logarithm s+1)^3+2)*k) := by
  have hC : C≤2^C := Nat.le_of_lt C.lt_two_pow_self
  have hS : scalar s+2≤2^((logarithm s+1)^3+2) := by
    have hpos : 1≤ scalar s := Nat.one_le_two_pow
    change 2^((logarithm s+1)^3)+2≤_
    rw [pow_add]
    norm_num only [Nat.reducePow]
    change 1≤2^((logarithm s+1)^3) at hpos
    omega
  calc
    _ ≤ 2^C*(2^((logarithm s+1)^3+2))^k := Nat.mul_le_mul hC (Nat.pow_le_pow_left hS k)
    _ = _ := by rw [←pow_mul,←pow_add]

/-- Uniform positive leading-exponent gain for the actual new complete native
leaf report over all original-resource families. The context is the full jet,
and the deterministic partition is acquired by the actual source itself. -/
theorem eventually_uniform_half (e : Real) (he : 0<e) :
    ∀ᶠ s : Nat in atTop, ∀ (ctx : Context) (net : SemiprimeD1BoundaryLeaf.Network),
      SemiprimeD1TensorNetwork.WellFormed net →
      SemiprimeD1LeafCounter.Good ctx (SemiprimeD1TensorNetwork.vertices net) →
      (SemiprimeD1BoundaryPlan.graph net).vertices≤5*s →
      (SemiprimeD1BoundaryPlan.graph net).edges.length≤ SemiprimeD1Schedule.leafSize s (logarithm s) →
      ctx.axes.length≤ logarithm s+1 → (∀q∈ctx.axes,q≤4*s) →
      ctx.rank≤ rankCap s → ctx.precision≤ precisionCap s →
      SemiprimeD1TensorNetworkRecursion.DegreeBound net (degreeCap s) →
      (SemiprimeD1BoundaryLeaf.run ctx net).clock≤
        (2:Real)^((1/2+e)*((s:Real)/Real.sqrt (logarithm s:Real))) := by
  obtain ⟨C,k,hmono⟩:=envelope_monomial
  have ht : Tendsto logarithm atTop atTop :=
    SemiprimeCounterRate.tendsto_clog_two_atTop.comp (tendsto_add_atTop_nat 2)
  filter_upwards [SemiprimeD1BoundaryPartitionOriginalRate.eventually_acquired_width_half_all (e/2) (by linarith),
    eventually_poly_exponent_small (C+3*k+1) (e/2) (by linarith),
    ht.eventually (eventually_ge_atTop 1000)] with s hwidth hover hl
  intro ctx net hw hg hV hM ha hq hr hp hd
  let g:=SemiprimeD1BoundaryPlan.graph net
  let w:=(SemiprimeD1BoundaryPlan.acquire g).width
  have hlpos : 0<logarithm s := by omega
  have hMR : (g.edges.length:Real)≤(s:Real)/Real.sqrt (logarithm s:Real)+1 :=
    (show (g.edges.length:Real)≤ SemiprimeD1Schedule.leafSize s (logarithm s) by exact_mod_cast hM).trans
      (SemiprimeD1LeafRate.leafSize_real s (logarithm s) hlpos)
  have hsqrt : (1:Real)≤ Real.sqrt (logarithm s:Real) := by
    have hsq:=Real.sq_sqrt (show (0:Real)≤ logarithm s by positivity)
    have hlR : (1000:Real)≤ logarithm s := by exact_mod_cast hl
    nlinarith only [hsq,hlR,Real.sqrt_nonneg (logarithm s:Real)]
  have hmain : (s:Real)/Real.sqrt (logarithm s:Real)≤ s := div_le_self (by positivity) hsqrt
  have hMn : g.edges.length≤ s+1 := by exact_mod_cast (hMR.trans (by linarith : (s:Real)/Real.sqrt (logarithm s:Real)+1≤ s+1))
  have hwR : (w:Real)≤(1/2+e/2)*((s:Real)/Real.sqrt (logarithm s:Real)) :=
    hwidth g (SemiprimeD1BoundaryPotential.graph_valid net) hMR
      (SemiprimeD1BoundaryNetworkDegree.maxDegree_le net hw (degreeCap s) hd)
  have hb:=(original_budget_le ctx g.vertices g.edges.length s hl hV hMn ha hq hr hp).trans (hmono (scalar s+1))
  have hb' : closedBudget ctx g.vertices g.edges.length≤2^(C+((logarithm s+1)^3+2)*k) :=
    hb.trans (monomial_to_power C k s)
  have hrun:=run_clock_polynomial ctx net hw hg
  have hplus : 2^w+1≤2^(w+1) := by
    have hh : 1≤(2:Nat)^w := Nat.one_le_two_pow
    rw [pow_succ]
    omega
  have hnat : (SemiprimeD1BoundaryLeaf.run ctx net).clock≤
      2^(C+((logarithm s+1)^3+2)*k+w+1) := by
    apply hrun.trans
    apply (Nat.mul_le_mul hb' hplus).trans_eq
    rw [←pow_add]
    congr 1
  have hreal : ((SemiprimeD1BoundaryLeaf.run ctx net).clock:Real)≤
      (2:Real)^((C+((logarithm s+1)^3+2)*k+w+1:Nat):Real) := by
    simpa only [Real.rpow_natCast,Nat.cast_pow,Nat.cast_ofNat] using
      (show ((SemiprimeD1BoundaryLeaf.run ctx net).clock:Real)≤
        (2^(C+((logarithm s+1)^3+2)*k+w+1):Nat) by exact_mod_cast hnat)
  apply hreal.trans
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:Real)≤2)
  have hE : (1:Real)≤((logarithm s:Real)+1)^3 := by
    have hh : (1:Real)≤(logarithm s:Real)+1 := by linarith [show (0:Real)≤logarithm s by positivity]
    exact one_le_pow₀ hh
  have hcost : (C:Real)+(((logarithm s:Real)+1)^3+2)*(k:Real)+1≤
      (C+3*k+1:Nat)*((logarithm s:Real)+1)^3 := by
    push_cast
    nlinarith only [hE,show (0:Real)≤ C by positivity,show (0:Real)≤ k by positivity]
  push_cast at hover hcost ⊢
  nlinarith only [hcost,hover,hwR]

end RiemannGaussian.SemiprimeD1BoundaryLeafOriginalRate
