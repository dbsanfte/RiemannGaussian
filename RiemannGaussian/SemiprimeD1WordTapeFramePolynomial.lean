/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1WordTapeFrameBudget
import RiemannGaussian.SemiprimeD1WordTapePhasePolynomial
import RiemannGaussian.SemiprimeD1PhysicalRecoveryPolynomial

/-! # Actual active-frame envelope in original scalar resources
All phase/source/menu/child/recovery reports remain attached to their executed
loops. The squared branching factor refers to the actual child-call inventory.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeD1WordTapeFramePolynomial
open SemiprimeD1JetAxes SemiprimeD1TensorNetwork SemiprimeD1TensorNetworkRecursion
open SemiprimeReportPolynomialGrowth
open SemiprimeD1RecursiveCallTree SemiprimeD1RecursiveCounter
open SemiprimeD1PhysicalChildPolynomial
attribute [local irreducible] SemiprimeD1OriginalModeAcquisition.acquire

/-- Physical recovery and native frame-control coefficient, with every
coordinate source producer paid again at its actual multiplicity. -/
def recoveryFactor (S : ℕ) : ℕ :=
  S*SemiprimeD1PhysicalRecoveryPolynomial.envelope (inflation S)+(3*S+8)+20*(8*S+inflation S+1)

/-- Complete active scalar coefficient before actual branching/eager scales. -/
def frameFactor (S a : ℕ) : ℕ :=
  S*SemiprimeD1WordTapePhasePolynomial.phaseFactor S a+recoveryFactor S

/-- A literal flatMap component cannot exceed the whole actual list inventory. -/
theorem component_length {A B : Type} (xs : List A) (f : A → List B) (x : A)
    (hx : x∈xs) : (f x).length ≤ (xs.flatMap f).length := by
  induction xs with
  | nil => simp only [List.not_mem_nil] at hx
  | cons y xs ih =>
    simp only [List.mem_cons] at hx
    simp only [List.flatMap_cons,List.length_append]
    rcases hx with rfl|hx
    · omega
    · exact (ih hx).trans (Nat.le_add_left _ _)

/-- Actual working precision at i0 has a derived original scalar cap. -/
theorem precision_zero (M u a p S : ℕ) (hu : 0 < u) (huM : u ≤ M)
    (hM : M ≤ S) (ha : a ≤ S) (hp : p ≤ S) (hN : 2^(a+1) ≤ S) :
    SemiprimeD1ModeRate.workingPrecision M u a 0 p ≤ inflation S := by
  have hh:=SemiprimeD1ModeRate.jetHeight_mul_le M u huM
  have hheight : SemiprimeD1ModeRate.jetHeight M u ≤ 4*M := by
    have hm:=Nat.mul_le_mul_left (SemiprimeD1ModeRate.jetHeight M u) (show 1 ≤ u by omega)
    simp only [Nat.mul_one] at hm
    omega
  have hpow : 2^a ≤ S := (Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) (Nat.le_succ a)).trans hN
  have hterm:=Nat.mul_le_mul (hheight.trans (Nat.mul_le_mul_left 4 hM)) hpow
  have hterm2:=Nat.mul_le_mul hM (Nat.add_le_add_right ha 1)
  apply le_trans (b := 1000*(S+1)^2) ?_ (quadratic_le_inflation S)
  simp only [SemiprimeD1ModeRate.workingPrecision,Nat.sub_zero]
  nlinarith only [hterm,hterm2,hp]

/-- All active local setup/recovery reports are bounded by fixed scalar work
per squared actual child inventory, from original guards rather than advice. -/
theorem budget_active_bound (s : ℕ) (parent : Call) (a u S : ℕ)
    (haSchedule : a=SemiprimeD1Schedule.exponent (SemiprimeD1PackingReady.logarithm s) parent.depth)
    (huSchedule : u=SemiprimeD1Schedule.levels (SemiprimeD1PackingReady.logarithm s) parent.depth)
    (hactive : activeTest s (SemiprimeD1PackingReady.logarithm s) parent.depth (edgeCount parent.net)=true)
    (hw : WellFormed parent.net) (hg : Good parent.ctx parent.net)
    (hlam : 1000 ≤ SemiprimeD1PackingReady.logarithm s)
    (hd : DegreeBound parent.net (SemiprimeD1PackingReady.degreeCap s))
    (hsmall : 2*(64^(2*a))^2*(SemiprimeD1PackingReady.degreeCap s) ≤ edgeCount parent.net)
    (hsize : 64^(2*a)*2^a ≤ edgeCount parent.net)
    (hMroot : edgeCount parent.net ≤ s)
    (hprecision : ∀i : Fin a,i.val < u → parent.ctx.precision*u ≤ edgeCount parent.net*2^(a-i.val))
    (hreserve : ∀i : Fin a,i.val < u → (a+1)*u ≤ 2^(a-i.val))
    (hn : parent.net.leftCount ≤ S) (hF : parent.net.rows.length ≤ S)
    (hM : edgeCount parent.net ≤ S) (ha : a ≤ S)
    (hp : parent.ctx.precision ≤ S) (hrank : parent.ctx.rank ≤ S)
    (haxes : parent.ctx.axes.length ≤ S)
    (hN : 2^(a+1) ≤ S) (hL : 64^a ≤ S)
    (hD : SemiprimeD1PackingReady.degreeCap s ≤ S)
    (hInventory : SemiprimeD1NetworkStateResources.inventory parent.net ≤ S)
    (hs : s ≤ S) (hlamS : SemiprimeD1PackingReady.logarithm s ≤ S) (hdepth : parent.depth ≤ S) :
    SemiprimeD1WordTapeFrameBudget.budget s parent ≤
      frameFactor S a*((children s parent).length+1)^2*2^(3*(SemiprimeD1PackingReady.degreeCap s)) := by
  let lam:=SemiprimeD1PackingReady.logarithm s
  let P:=SemiprimeD1ModeRate.workingPrecision (edgeCount parent.net) u a 0 parent.ctx.precision
  let K:=((children s parent).length+1)^2*2^(3*(SemiprimeD1PackingReady.degreeCap s))
  have hAct:=((activeTest_correct _ _ _ _).mp hactive)
  have hu0 : 0 < u := by rw [huSchedule];exact SemiprimeD1Schedule.active_positive _ _ _ _ hAct
  have huM : u ≤ edgeCount parent.net := by rw [huSchedule];exact hAct.2.2
  have hUI : u ≤ S := huM.trans hM
  have hSI:=le_inflation S
  have hNs : SemiprimeD1WireKernelOriginal.size a ≤ S := hN
  have hP : P ≤ inflation S := precision_zero _ _ _ _ _ hu0 huM hM ha hp hN
  have haSmall : a ≤ 4*(lam/131072) := by
    rw [haSchedule]
    exact SemiprimeD1Schedule.exponent_le _ _
  have hMlog : edgeCount parent.net ≤ 2^lam := by
    have hlog:=Nat.le_pow_clog (by decide : 1 < (2:ℕ)) (s+2)
    exact hMroot.trans ((by omega : s ≤ s+2).trans hlog)
  have hchildren : children s parent=(List.finRange (SemiprimeD1WireKernelOriginal.size a)).flatMap
      (phaseChildren parent a u) := by
    simp only [children,hactive,ite_true]
    rw [←haSchedule,←huSchedule]
  have hsum : ((List.finRange (SemiprimeD1WireKernelOriginal.size a)).map
      (SemiprimeD1WordTapePhaseBudget.phaseBudget parent a u)).sum ≤
      S*SemiprimeD1WordTapePhasePolynomial.phaseFactor S a*K := by
    have hsum':=List.sum_le_length_nsmul
      ((List.finRange (SemiprimeD1WireKernelOriginal.size a)).map
        (SemiprimeD1WordTapePhaseBudget.phaseBudget parent a u))
      (SemiprimeD1WordTapePhasePolynomial.phaseFactor S a*K) (by
        intro value hv
        obtain ⟨t,ht,rfl⟩:=List.mem_map.mp hv
        have htBound:=SemiprimeD1WordTapePhasePolynomial.phase_budget_bound parent lam a u t S
          hw hg hlam haSmall hMlog hd hsmall hsize hu0 huM hprecision hreserve
          hn hF hM ha hp hrank haxes hN hL hD hInventory
        have hlen : (phaseChildren parent a u t).length ≤ (children s parent).length := by
          rw [hchildren]
          exact component_length _ _ t ht
        apply htBound.trans
        change _ ≤ SemiprimeD1WordTapePhasePolynomial.phaseFactor S a*
          (((children s parent).length+1)^2*2^(3*(SemiprimeD1PackingReady.degreeCap s)))
        rw [←Nat.mul_assoc]
        gcongr
        exact le_rfl)
    simp only [List.length_map,List.length_finRange,nsmul_eq_mul,Nat.cast_id] at hsum'
    apply hsum'.trans
    calc
      _ ≤ S*(SemiprimeD1WordTapePhasePolynomial.phaseFactor S a*K) := Nat.mul_le_mul_right _ hNs
      _ = _ := by ring
  have hR:=SemiprimeD1PhysicalRecoveryPolynomial.budget_le_envelope a (edgeCount parent.net)
    parent.ctx.precision parent.ctx.rank P (inflation S) (ha.trans hSI) (hM.trans hSI)
    (hNs.trans hSI) (hp.trans hSI) (hrank.trans hSI) hP
  have hK : 1 ≤ K :=
    one_le_mul_of_one_le_of_one_le (Nat.one_le_pow _ _ (by omega)) Nat.one_le_two_pow
  have lift (x : ℕ) : x ≤ x*K := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left x hK
  have hRecovery := (Nat.mul_le_mul hrank hR).trans
    (lift (S*SemiprimeD1PhysicalRecoveryPolynomial.envelope (inflation S)))
  have hGeometry : (SemiprimeD1RecoveryWeightRun.geometry a 0).work ≤ (3*S+8)*K := by
    rw [SemiprimeD1RecoveryMetadataBudget.geometry_work]
    exact (by omega : 3*a+8 ≤ 3*S+8).trans (lift (3*S+8))
  have hControl : 20*(s+lam+parent.depth+edgeCount parent.net+a+u+P+parent.ctx.rank+
      SemiprimeD1WireKernelOriginal.size a+1) ≤ (20*(8*S+inflation S+1))*K := by
    have hctrl : s+lam+parent.depth+edgeCount parent.net+a+u+P+parent.ctx.rank+
        SemiprimeD1WireKernelOriginal.size a+1 ≤ 8*S+inflation S+1 := by omega
    exact (Nat.mul_le_mul_left 20 hctrl).trans (lift _)
  simp only [SemiprimeD1WordTapeFrameBudget.budget,hactive,ite_true]
  rw [←haSchedule,←huSchedule]
  calc
    _ ≤ S*SemiprimeD1WordTapePhasePolynomial.phaseFactor S a*K+
        (S*SemiprimeD1PhysicalRecoveryPolynomial.envelope (inflation S))*K+(3*S+8)*K+
        (20*(8*S+inflation S+1))*K :=
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hsum hRecovery) hGeometry) hControl
    _ = frameFactor S a*K := by unfold frameFactor recoveryFactor;ring
    _ = _ := by dsimp only [K];ring



/-- All physical scalar recovery and native control coefficients have fixed
monomial growth in the actual original dimension cap. -/
theorem recoveryFactor_monomial : SemiprimeReportPolynomialGrowth.Bound recoveryFactor := by
  unfold recoveryFactor
  apply SemiprimeReportPolynomialGrowth.add_bound
  · apply SemiprimeReportPolynomialGrowth.add_bound
    · apply SemiprimeReportPolynomialGrowth.mul_bound SemiprimeReportPolynomialGrowth.identity_bound
      exact SemiprimeD1PhysicalNetworkSourceBudget.compose_bound
        SemiprimeD1PhysicalRecoveryPolynomial.envelope_monomial
        SemiprimeD1PhysicalChildGrowth.inflation_monomial
    · exact SemiprimeReportPolynomialGrowth.add_bound
        (SemiprimeReportPolynomialGrowth.mul_bound
          (SemiprimeReportPolynomialGrowth.constant_bound 3)
          SemiprimeReportPolynomialGrowth.identity_bound)
        (SemiprimeReportPolynomialGrowth.constant_bound 8)
  · unfold inflation
    boundArithmetic

/-- Fixed witnesses bound the ACTUAL active-frame scalar coefficient. -/
theorem frameFactor_monomial : SemiprimeD1ChildPrefactorPolynomial.Bound frameFactor := by
  unfold frameFactor
  exact SemiprimeD1ChildPrefactorPolynomial.add_bound
    (SemiprimeD1ChildPrefactorPolynomial.mul_bound
      SemiprimeD1ChildPrefactorPolynomial.scalar_bound
      SemiprimeD1WordTapePhasePolynomial.phaseFactor_monomial)
    (SemiprimeD1PhysicalChildGrowth.lift_bound recoveryFactor_monomial)

end RiemannGaussian.SemiprimeD1WordTapeFramePolynomial
