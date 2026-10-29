/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1WordTapeOriginalPhaseBudget
import RiemannGaussian.SemiprimeD1ChildWordOriginalPolynomial
import RiemannGaussian.SemiprimeD1PhysicalPhasePolynomial

/-! # Actual word-only phase costs in original scalar resources
Every repeated source/header/menu producer is retained and paid. The squared
menu factor is bounded by the literal actual phase-child inventory.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeD1WordTapePhasePolynomial
open SemiprimeD1JetAxes SemiprimeD1TensorNetwork SemiprimeD1TensorNetworkRecursion SemiprimeD1RecursiveCallTree
open SemiprimeD1WordTapePhaseBudget SemiprimeD1WordTapeOriginalPhaseBudget
attribute [local irreducible] SemiprimeD1OriginalModeAcquisition.acquire

/-- Uniform scalar factor before the actual squared branching and eager scales. -/
def phaseFactor (S a : ℕ) : ℕ :=
  SemiprimeD1PhysicalPhasePolynomial.phaseFactor S (SemiprimeD1ChildWordOriginalPolynomial.factor S a)

/-- All original phase coefficients have fixed monomial witnesses. -/
theorem phaseFactor_monomial : SemiprimeD1ChildPrefactorPolynomial.Bound phaseFactor := by
  exact SemiprimeD1PhysicalPhasePolynomial.phaseFactor_monomial
    SemiprimeD1ChildWordOriginalPolynomial.factor_monomial


/-- Each actual mode creates all64 group children, counted without evaluating
or changing any child constructor. -/
theorem groups_length {A B : Type} (xs : List A) (f : A → Fin 64 → B) :
    (xs.flatMap (fun x => (List.finRange 64).map (f x))).length=64*xs.length := by
  simp only [List.length_flatMap,List.length_map,List.length_finRange,List.map_const',List.sum_replicate,
    nsmul_eq_mul,Nat.cast_id]
  omega

/-- Pure scalar control arithmetic is isolated before original records are substituted. -/
theorem control_bound (M a u i q L S I : ℕ) (hM : M ≤ S) (ha : a ≤ S)
    (hu : u ≤ S) (hi : i ≤ S) (hq : q ≤ I) :
    10*(M+a+u+i+q+L+1) ≤ (10*(4*S+I+2))*(L+1) := by
  have hbase : M+a+u+i+q+L+1 ≤ (4*S+I+2)*(L+1) := by
    nlinarith only [hM,ha,hu,hi,hq,Nat.zero_le ((4*S+I+1)*L)]
  simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 10 hbase

/-- The actual original word-only phase budget is polynomial per squared actual
child count. No clock, fit, shape or histogram answer is a premise. -/
theorem phase_budget_bound (parent : Call) (lam a u : ℕ)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (S : ℕ)
    (hw : WellFormed parent.net) (hg : Good parent.ctx parent.net)
    (hlam : 1000 ≤ lam) (haSmall : a ≤ 4*(lam/131072))
    (hMlog : edgeCount parent.net ≤ 2^lam)
    (hd : DegreeBound parent.net (2^((9*lam+9)/10)))
    (hsmall : 2*(64^(2*a))^2*(2^((9*lam+9)/10)) ≤ edgeCount parent.net)
    (hsize : 64^(2*a)*2^a ≤ edgeCount parent.net)
    (hu : 0 < u) (huM : u ≤ edgeCount parent.net)
    (hprecision : ∀i : Fin a,i.val < u → parent.ctx.precision*u ≤ edgeCount parent.net*2^(a-i.val))
    (hreserve : ∀i : Fin a,i.val < u → (a+1)*u ≤ 2^(a-i.val))
    (hn : parent.net.leftCount ≤ S) (hF : parent.net.rows.length ≤ S)
    (hM : edgeCount parent.net ≤ S) (ha : a ≤ S)
    (hp : parent.ctx.precision ≤ S) (hrank : parent.ctx.rank ≤ S)
    (haxes : parent.ctx.axes.length ≤ S)
    (hN : 2^(a+1) ≤ S) (hL : 64^a ≤ S) (hD : 2^((9*lam+9)/10) ≤ S)
    (hInventory : SemiprimeD1NetworkStateResources.inventory parent.net ≤ S) :
    phaseBudget parent a u t ≤ phaseFactor S a*((phaseChildren parent a u t).length+1)^2*
      2^(3*(2^((9*lam+9)/10))) := by
  have hstart:=phaseBudget_le_original parent lam a u t hw hg hlam haSmall hMlog hd hsmall hsize
    hu huM hprecision hreserve
  apply hstart.trans
  unfold originalPhaseBudget
  dsimp only
  split
  · rename_i hi
    let i : Fin a:=⟨_,hi.1⟩
    let source:=SemiprimeD1ChildOriginalClock.source parent.net parent.ctx a u i
    let q:=SemiprimeD1ModeRate.jetHeight (edgeCount parent.net) u*(u-i.val)
    let L:=source.modes.values.length
    let C:=SemiprimeD1ChildWordOriginalPolynomial.factor S a
    let F:=SemiprimeD1PhysicalSourcePolynomial.sourceFactor
      (SemiprimeD1PhysicalNetworkSourceBudget.inflation S)
    have hc:=SemiprimeD1ChildWordOriginalPolynomial.child_budget_bound parent lam a u i S
      hw hlam haSmall hMlog hd hsmall hsize hu huM (hprecision i hi.2.1) (hreserve i hi.2.1)
      hn hF hM ha hp hrank haxes hN hL hD hInventory
    change childBudget parent lam a u i ≤ C*(L+1)*2^(3*(2^((9*lam+9)/10))) at hc
    have hs:=SemiprimeD1PhysicalNetworkSourceBudget.acquire_work parent.net hw _ a u i.val
      parent.ctx.precision S hd hsmall hsize hu huM i.isLt.le hn hF hM ha hp hN hL
    change source.work ≤ F*(L+1) at hs
    have hprec:=SemiprimeD1PhysicalChildPolynomial.precision_bound parent a u i S hu huM hM ha hp hN
    have hq:=SemiprimeD1PhysicalChildPolynomial.fresh_axis_bound parent a u i S huM hM
    have hz : 9*source.precision+3*(q*parent.ctx.rank)+10 ≤ SemiprimeD1PhysicalChildPolynomial.freshBudget S := by
      unfold SemiprimeD1PhysicalChildPolynomial.freshBudget
      gcongr
    have he : modeOverhead (current parent a u i) ≤ SemiprimeD1PhysicalPhasePolynomial.modeEnvelope S :=
      SemiprimeD1PhysicalPhasePolynomial.modeOverhead_bound parent a u i S hu huM hM ha hp hrank haxes hN
    have hv : (current parent a u i).rank ≤ SemiprimeD1PhysicalPhasePolynomial.vectorCap S :=
      (SemiprimeD1PhysicalPhasePolynomial.current_fields parent a u i S hu huM hM ha hp hrank haxes hN).1
    have hb:=SemiprimeD1PhysicalPhasePolynomial.block_bound parent a u i S hu huM hM ha hp hrank haxes hN
    dsimp only at hb
    have hG : (SemiprimeD1RecoveryWeightRun.geometry a t.val).work+
        (SemiprimeD1RecoveryScalarRun.orderFuel (SemiprimeD1RecoveryWeightRun.geometry a t.val).size
          (SemiprimeD1RecoveryWeightRun.geometry a t.val).point.natAbs).work ≤ 8*S+11 := by
      have ho:=SemiprimeD1RecoveryScalarRun.orderFuel_work
        (SemiprimeD1RecoveryWeightRun.geometry a t.val).size
        (SemiprimeD1RecoveryWeightRun.geometry a t.val).point.natAbs
      rw [SemiprimeD1RecoveryMetadataBudget.geometry_work]
      simp only [SemiprimeD1RecoveryWeightRun.geometry_size] at ho ⊢
      have hNs : SemiprimeD1WireKernelOriginal.size a ≤ S := hN
      omega
    have hcontrol : 10*(edgeCount parent.net+a+u+i.val+q+L+1) ≤
        SemiprimeD1PhysicalPhasePolynomial.controlEnvelope S*(L+1) := by
      have hui : u ≤ S := huM.trans hM
      have hii : i.val ≤ S := i.isLt.le.trans ha
      simpa only [SemiprimeD1PhysicalPhasePolynomial.controlEnvelope] using
        control_bound (edgeCount parent.net) a u i.val q L S
          (SemiprimeD1PhysicalChildPolynomial.inflation S) hM ha hui hii hq
    have hnum:=SemiprimeD1PhasePolynomialArithmetic.phase_bound L (3*(2^((9*lam+9)/10)))
      (8*S+11) F (SemiprimeD1PhysicalChildPolynomial.freshBudget S) C
      (SemiprimeD1PhysicalPhasePolynomial.modeEnvelope S) (SemiprimeD1PhysicalPhasePolynomial.vectorCap S)
      (SemiprimeD1PhysicalPhasePolynomial.blockEnvelope S) (SemiprimeD1PhysicalPhasePolynomial.controlEnvelope S)
      _ _ _ _ _ _ _ _ _ hG hs hz hc he hv hb hcontrol
    have hcoef:=SemiprimeD1PhysicalPhasePolynomial.coefficient_le S C
    have hnum':=hnum.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right ((L+1)^2) hcoef))
    have hlength : (phaseChildren parent a u t).length=64*L := by
      unfold phaseChildren
      dsimp only
      rw [dite_eq_left hi]
      exact groups_length _ _
    apply hnum'.trans
    change phaseFactor S a*(L+1)^2*2^(3*(2^((9*lam+9)/10))) ≤ _
    apply Nat.mul_le_mul_right _
    apply Nat.mul_le_mul_left _
    apply Nat.pow_le_pow_left
    omega
  · have ho:=SemiprimeD1RecoveryScalarRun.orderFuel_work
      (SemiprimeD1RecoveryWeightRun.geometry a t.val).size
      (SemiprimeD1RecoveryWeightRun.geometry a t.val).point.natAbs
    have hv:=SemiprimeD1PhysicalPhasePolynomial.order_value_le
      (SemiprimeD1RecoveryWeightRun.geometry a t.val).size
      (SemiprimeD1RecoveryWeightRun.geometry a t.val).point.natAbs
    simp only [SemiprimeD1RecoveryWeightRun.geometry_size] at ho hv ⊢
    rw [SemiprimeD1RecoveryMetadataBudget.geometry_work]
    have hNs : SemiprimeD1WireKernelOriginal.size a ≤ S := hN
    have hui : u ≤ S := huM.trans hM
    have hg : 3*a+8+
        (SemiprimeD1RecoveryScalarRun.orderFuel (SemiprimeD1RecoveryWeightRun.geometry a t.val).size
          (SemiprimeD1RecoveryWeightRun.geometry a t.val).point.natAbs).work+a+u+
        (SemiprimeD1RecoveryScalarRun.orderFuel (SemiprimeD1RecoveryWeightRun.geometry a t.val).size
          (SemiprimeD1RecoveryWeightRun.geometry a t.val).point.natAbs).value+8 ≤ 11*S+19 := by
      simp only [SemiprimeD1RecoveryWeightRun.geometry_size]
      omega
    simp only [SemiprimeD1RecoveryWeightRun.geometry_size] at hg
    have hf : 11*S+19 ≤ phaseFactor S a := by
      unfold phaseFactor SemiprimeD1PhysicalPhasePolynomial.phaseFactor
        SemiprimeD1PhysicalPhasePolynomial.arithmeticBase SemiprimeD1PhysicalPhasePolynomial.arithmeticOnly
      omega
    have h1 : 1 ≤ ((phaseChildren parent a u t).length+1)^2*2^(3*(2^((9*lam+9)/10))) :=
      one_le_mul_of_one_le_of_one_le (Nat.one_le_pow _ _ (by omega)) Nat.one_le_two_pow
    apply (hg.trans hf).trans
    simpa only [Nat.mul_assoc,Nat.mul_one] using Nat.mul_le_mul_left (phaseFactor S a) h1

end RiemannGaussian.SemiprimeD1WordTapePhasePolynomial
