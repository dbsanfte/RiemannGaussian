/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1BoundaryCheckedPolynomial

/-! # Uniform leading half exponent for the actual checked recursion leaf -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1BoundaryCheckedOriginalRate
open Filter
open SemiprimeD1JetAxes (Context)
open SemiprimeD1BoundaryCheckedPolynomial SemiprimeD1BoundaryLeafOriginalRate
open SemiprimeD1PackingReady SemiprimeD1OriginalStateResources
open SemiprimeD1OriginalEnvelopeRate SemiprimeD1OriginalScalarResources

/-- Uniform positive leading-exponent gain for the actual checked complete native
leaf report over all original-resource families. The context is the full jet,
and the deterministic partition is acquired by the actual source itself. -/
theorem eventually_checked_uniform_half (e : Real) (he : 0<e) :
    ∀ᶠ s : Nat in atTop, ∀ (ctx : Context) (net : SemiprimeD1BoundaryLeaf.Network),
      SemiprimeD1TensorNetwork.WellFormed net →
      SemiprimeD1LeafCounter.Good ctx (SemiprimeD1TensorNetwork.vertices net) →
      (SemiprimeD1BoundaryPlan.graph net).vertices≤5*s →
      (SemiprimeD1BoundaryPlan.graph net).edges.length≤ SemiprimeD1Schedule.leafSize s (logarithm s) →
      ctx.axes.length≤ logarithm s+1 → (∀q∈ctx.axes,q≤4*s) →
      ctx.rank≤ rankCap s → ctx.precision≤ precisionCap s →
      SemiprimeD1TensorNetworkRecursion.DegreeBound net (degreeCap s) →
      (SemiprimeD1BoundaryLeaf.checked ctx net).clock≤
        (2:Real)^((1/2+e)*((s:Real)/Real.sqrt (logarithm s:Real))) := by
  obtain ⟨C,k,hmono⟩:=checkedEnvelope_monomial
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
  have hb:=(checked_original_budget_le ctx g.vertices g.edges.length s hl hV hMn ha hq hr hp).trans (hmono (scalar s+1))
  have hb' : checkedBudget ctx g.vertices g.edges.length≤2^(C+((logarithm s+1)^3+2)*k) :=
    hb.trans (monomial_to_power C k s)
  have hrun:=checked_clock ctx net hw hg
  have hplus : 2^w+1≤2^(w+1) := by
    have hh : 1≤(2:Nat)^w := Nat.one_le_two_pow
    rw [pow_succ]
    omega
  have hnat : (SemiprimeD1BoundaryLeaf.checked ctx net).clock≤
      2^(C+((logarithm s+1)^3+2)*k+w+1) := by
    apply hrun.trans
    apply (Nat.mul_le_mul hb' hplus).trans_eq
    rw [←pow_add]
    congr 1
  have hreal : ((SemiprimeD1BoundaryLeaf.checked ctx net).clock:Real)≤
      (2:Real)^((C+((logarithm s+1)^3+2)*k+w+1:Nat):Real) := by
    simpa only [Real.rpow_natCast,Nat.cast_pow,Nat.cast_ofNat] using
      (show ((SemiprimeD1BoundaryLeaf.checked ctx net).clock:Real)≤
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


end RiemannGaussian.SemiprimeD1BoundaryCheckedOriginalRate
