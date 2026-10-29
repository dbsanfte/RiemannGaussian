/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PhysicalPhaseBudget
import RiemannGaussian.SemiprimeD1ChildOriginalClock
import RiemannGaussian.SemiprimeD1RecursiveCallState

/-! # Original-constructor phase budgets, with no child-clock advice
Every repeated actual child constructor is bounded by the original source/table
producer theorem. The actual source/menu multiplicity is retained explicitly.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace RiemannGaussian.SemiprimeD1PhysicalOriginalPhaseBudget
open SemiprimeD1JetAxes SemiprimeD1TensorNetwork SemiprimeD1TensorNetworkRecursion
open SemiprimeD1RecursiveCallTree SemiprimeD1RecursiveCallState
open SemiprimeD1PhysicalRecursiveClock SemiprimeD1PhysicalPhaseBudget
open SemiprimeD1JetAffineCoefficient (JetRun)
attribute [local irreducible] SemiprimeD1OriginalModeAcquisition.acquire

/-- Actual fresh generator used by the original phase, not a supplied value. -/
def fresh (parent : Call) (a u : ℕ) (i : Fin a) : JetRun :=
  let source:=SemiprimeD1ChildOriginalClock.source parent.net parent.ctx a u i
  SemiprimeD1FreshJetBits.acquireFresh parent.ctx
    (SemiprimeD1ModeRate.jetHeight (edgeCount parent.net) u*(u-i.val)) source.precision

/-- The uniform original child budget retains its actual source and fresh reports. -/
def childBudget (parent : Call) (lam a u : ℕ) (i : Fin a) : ℕ :=
  SemiprimeD1ChildOriginalClock.originalBudget parent.net parent.ctx
    [SemiprimeD1ModeRate.jetHeight (edgeCount parent.net) u*(u-i.val)] lam a u i
    (fresh parent a u i).clock

/-- All64 actual group constructors at an actual acquired mode have a uniform
original-data cap. No field/clock/output-height supplier is an input. -/
theorem childClocks_original (parent : Call) (lam a u : ℕ)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (i : Fin a) (beta : List ℕ)
    (hb : beta ∈ (SemiprimeD1ChildOriginalClock.source parent.net parent.ctx a u i).modes.values)
    (hw : WellFormed parent.net) (hg : Good parent.ctx parent.net)
    (hlam : 1000 ≤ lam) (haSmall : a ≤ 4*(lam/131072))
    (hM : edgeCount parent.net ≤ 2^lam)
    (hd : DegreeBound parent.net (2^((9*lam+9)/10)))
    (hsmall : 2*(64^(2*a))^2*(2^((9*lam+9)/10)) ≤ edgeCount parent.net)
    (hsize : 64^(2*a)*2^a ≤ edgeCount parent.net)
    (hu : 0 < u) (huM : u ≤ edgeCount parent.net) (hiu : i.val < u)
    (hp : parent.ctx.precision*u ≤ edgeCount parent.net*2^(a-i.val))
    (ha : (a+1)*u ≤ 2^(a-i.val)) :
    childClocks parent a u t i beta ≤ 64*childBudget parent lam a u i := by
  let q:=SemiprimeD1ModeRate.jetHeight (edgeCount parent.net) u*(u-i.val)
  let source:=SemiprimeD1ChildOriginalClock.source parent.net parent.ctx a u i
  have hq : 0 < q := Nat.mul_pos (height_positive _ _ hu huM) (Nat.sub_pos_of_lt hiu)
  have he : 0 < ([q]:List ℕ).prod := by simpa using hq
  have hz : SemiprimeD1JetAffineCoefficientBounds.Good
      ⟨[q]++parent.ctx.axes,source.precision⟩ (fresh parent a u i).words := by
    simpa only [fresh,SemiprimeD1FreshJetBits.context,List.singleton_append] using
      SemiprimeD1FreshJetBits.acquireFresh_good parent.ctx q source.precision
  have hs:=List.sum_le_length_nsmul
    ((List.finRange 64).map (fun g =>
      (SemiprimeD1ChildNetwork.fromSource parent.net source i g parent.ctx [q] source.precision
        (fresh parent a u i) t beta).clock)) (childBudget parent lam a u i) (by
      intro c hc
      obtain ⟨g,hg',rfl⟩:=List.mem_map.mp hc
      exact SemiprimeD1ChildOriginalClock.fromSource_clock_original parent.net parent.ctx [q]
        lam a u i g (fresh parent a u i) t beta hb hw hg he hz
        hlam haSmall hM hd hsmall hsize hu huM hp ha)
  simpa only [childClocks,childBudget,fresh,q,source,List.length_map,List.length_finRange,
    nsmul_eq_mul,Nat.cast_id] using hs

/-- Sum of all acquired modes keeps its exact menu factor and repeated original
child/source producers, with no supplied child cost or hidden group sharing. -/
theorem phaseTotal_original (s fuel : ℕ) (parent : Call) (lam a u : ℕ)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (i : Fin a)
    (hw : WellFormed parent.net) (hg : Good parent.ctx parent.net)
    (hlam : 1000 ≤ lam) (haSmall : a ≤ 4*(lam/131072))
    (hM : edgeCount parent.net ≤ 2^lam)
    (hd : DegreeBound parent.net (2^((9*lam+9)/10)))
    (hsmall : 2*(64^(2*a))^2*(2^((9*lam+9)/10)) ≤ edgeCount parent.net)
    (hsize : 64^(2*a)*2^a ≤ edgeCount parent.net)
    (hu : 0 < u) (huM : u ≤ edgeCount parent.net) (hiu : i.val < u)
    (hp : parent.ctx.precision*u ≤ edgeCount parent.net*2^(a-i.val))
    (ha : (a+1)*u ≤ 2^(a-i.val)) :
    let source:=SemiprimeD1ChildOriginalClock.source parent.net parent.ctx a u i
    (phaseTotal (eraseClock (SemiprimeD1PhysicalRecursiveCounter.run s fuel (parent.depth+1)))
      parent a u t i).clock ≤
      source.modes.values.length*(64*childBudget parent lam a u i+modeOverhead (current parent a u i))+
        (current parent a u i).rank+1 := by
  let source:=SemiprimeD1ChildOriginalClock.source parent.net parent.ctx a u i
  have hc:=List.sum_le_length_nsmul (source.modes.values.map (childClocks parent a u t i))
    (64*childBudget parent lam a u i) (by
      intro c hc
      obtain ⟨beta,hbeta,rfl⟩:=List.mem_map.mp hc
      exact childClocks_original parent lam a u t i beta hbeta hw hg hlam haSmall hM hd hsmall hsize
        hu huM hiu hp ha)
  simp only [List.length_map,nsmul_eq_mul,Nat.cast_id] at hc
  have ht:=SemiprimeD1PhysicalPhaseBudget.phaseTotal_clock s fuel parent a u t i
  dsimp only at ht ⊢
  change _ ≤ source.modes.values.length*(_+_)+(current parent a u i).rank+1
  have ht' : (phaseTotal (eraseClock (SemiprimeD1PhysicalRecursiveCounter.run s fuel (parent.depth+1)))
      parent a u t i).clock ≤ (source.modes.values.map (childClocks parent a u t i)).sum+
        source.modes.values.length*modeOverhead (current parent a u i)+(current parent a u i).rank+1 := ht
  nlinarith only [hc,ht']



/-- Original-data phase envelope with the full acquired-menu multiplicity. -/
def originalPhaseBudget (parent : Call) (lam a u : ℕ)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) : ℕ :=
  let geometry:=SemiprimeD1RecoveryWeightRun.geometry a t.val
  let order:=SemiprimeD1RecoveryScalarRun.orderFuel geometry.size geometry.point.natAbs
  if hi : order.value < a ∧ order.value < u ∧ geometry.point ≠ 0 then
    let i : Fin a:=⟨order.value,hi.1⟩
    let source:=SemiprimeD1OriginalModeAcquisition.acquire parent.net.leftCount
      parent.net.rows.length 64 a u i.val parent.ctx.precision
      (arity parent.net.rows) (owner parent.net.rows)
    let q:=SemiprimeD1ModeRate.jetHeight (edgeCount parent.net) u*(u-i.val)
    let ctx:=current parent a u i
    geometry.work+order.work+source.work+(9*source.precision+3*(q*parent.ctx.rank)+10)+
      (source.modes.values.length*(64*childBudget parent lam a u i)+
        source.modes.values.length*modeOverhead ctx+ctx.rank+1)+
      q*(parent.ctx.rank*(3*ctx.rank+3*source.precision+5)+5*parent.ctx.rank+5)+
      10*(edgeCount parent.net+a+u+i.val+q+source.modes.values.length+1)
  else geometry.work+order.work+a+u+order.value+8


/-- Every actual child constructor is paid, including repeated source reports.
The precision inequalities are original schedule inequalities, not clock advice. -/
theorem phaseBudget_le_original (parent : Call) (lam a u : ℕ)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (hw : WellFormed parent.net) (hg : Good parent.ctx parent.net)
    (hlam : 1000 ≤ lam) (haSmall : a ≤ 4*(lam/131072))
    (hM : edgeCount parent.net ≤ 2^lam)
    (hd : DegreeBound parent.net (2^((9*lam+9)/10)))
    (hsmall : 2*(64^(2*a))^2*(2^((9*lam+9)/10)) ≤ edgeCount parent.net)
    (hsize : 64^(2*a)*2^a ≤ edgeCount parent.net)
    (hu : 0 < u) (huM : u ≤ edgeCount parent.net)
    (hp : ∀ i : Fin a, i.val < u →
      parent.ctx.precision*u ≤ edgeCount parent.net*2^(a-i.val))
    (ha : ∀ i : Fin a, i.val < u → (a+1)*u ≤ 2^(a-i.val)) :
    phaseBudget parent a u t ≤ originalPhaseBudget parent lam a u t := by
  unfold phaseBudget originalPhaseBudget
  dsimp only
  split
  · rename_i hi
    let i : Fin a:=⟨(SemiprimeD1RecoveryScalarRun.orderFuel
      (SemiprimeD1RecoveryWeightRun.geometry a t.val).size
      (SemiprimeD1RecoveryWeightRun.geometry a t.val).point.natAbs).value,hi.1⟩
    let source:=SemiprimeD1ChildOriginalClock.source parent.net parent.ctx a u i
    have hc:=List.sum_le_length_nsmul (source.modes.values.map (childClocks parent a u t i))
      (64*childBudget parent lam a u i) (by
        intro c hc
        obtain ⟨beta,hb,rfl⟩:=List.mem_map.mp hc
        exact childClocks_original parent lam a u t i beta hb hw hg hlam haSmall hM hd
          hsmall hsize hu huM hi.2.1 (hp i hi.2.1) (ha i hi.2.1))
    simp only [List.length_map,nsmul_eq_mul,Nat.cast_id] at hc
    dsimp only [source,SemiprimeD1ChildOriginalClock.source,i] at hc
    exact Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.add_le_add_left (Nat.add_le_add_right
        (Nat.add_le_add_right (Nat.add_le_add_right hc _) _) _) _) _) _
  · exact le_rfl



/-- Actual original phase, with every repeated child producer discharged. -/
theorem phase_clock_original (s fuel : ℕ) (parent : Call) (lam a u : ℕ)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (hw : WellFormed parent.net) (hg : Good parent.ctx parent.net)
    (hlam : 1000 ≤ lam) (haSmall : a ≤ 4*(lam/131072))
    (hM : edgeCount parent.net ≤ 2^lam)
    (hd : DegreeBound parent.net (2^((9*lam+9)/10)))
    (hsmall : 2*(64^(2*a))^2*(2^((9*lam+9)/10)) ≤ edgeCount parent.net)
    (hsize : 64^(2*a)*2^a ≤ edgeCount parent.net)
    (hu : 0 < u) (huM : u ≤ edgeCount parent.net)
    (hp : ∀ i : Fin a, i.val < u →
      parent.ctx.precision*u ≤ edgeCount parent.net*2^(a-i.val))
    (ha : ∀ i : Fin a, i.val < u → (a+1)*u ≤ 2^(a-i.val)) :
    (SemiprimeD1RecursiveCounter.phase
      (eraseClock (SemiprimeD1PhysicalRecursiveCounter.run s fuel (parent.depth+1)))
      parent.ctx parent.net a u t).clock ≤ originalPhaseBudget parent lam a u t := by
  exact (phase_local_clock s fuel parent a u t).trans
    (phaseBudget_le_original parent lam a u t hw hg hlam haSmall hM hd hsmall hsize hu huM hp ha)

end RiemannGaussian.SemiprimeD1PhysicalOriginalPhaseBudget
