/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PhysicalRecursiveClock
import RiemannGaussian.SemiprimeD1PhysicalRecoveryLocalBudget
import RiemannGaussian.SemiprimeD1WordTapeRecursiveCounter

/-! # Actual local phase overhead before uniform original-resource substitution
The child-network construction reports remain literal and fully repeated here.
No supplied child cost, solved entry or intermediate Fits is an input.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace RiemannGaussian.SemiprimeD1WordTapePhaseBudget
open SemiprimeD1JetAxes SemiprimeD1TensorNetwork SemiprimeD1RecursiveCounter
open SemiprimeD1RecursiveCallTree SemiprimeD1WordTapeRecursivePhase
open SemiprimeD1PhysicalRecursiveClock (eraseClock)
open SemiprimeD1JetAffineCoefficient (JetRun)
open SemiprimeD1TensorTables (GoodWords)
attribute [local irreducible] SemiprimeD1OriginalModeAcquisition.acquire

/-- Every cached vector product intrinsically has canonical current shape. -/
theorem product_good (ctx : Context) (values : List JetRun) :
    GoodWords ctx (product ctx values).words := by
  cases values with
  | nil => exact SemiprimeD1LeafCounterBounds.one_good ctx
  | cons x xs => exact SemiprimeD1LeafCounterBounds.mul_good _ _ _

/-- Physical cached products add every input report and a fixed actual vector
operation allowance per item; no input clock upper bound is advised. -/
theorem product_clock (ctx : Context) (values : List JetRun)
    (hg : ∀ value ∈ values, GoodWords ctx value.words) :
    (product ctx values).clock ≤ (values.map (fun value => value.clock)).sum+
      values.length*(SemiprimeD1LeafCounterBounds.productBudget ctx+3)+
      SemiprimeD1LeafCounterBounds.oneBudget ctx := by
  induction values with
  | nil =>
    have h:=SemiprimeD1JetScalarBits.reduce_clock ctx.precision [true]
    simp only [product,SemiprimeD1JetAffineCoefficient.one,List.map_nil,List.sum_nil,
      List.length_nil,Nat.zero_mul,Nat.zero_add,SemiprimeD1LeafCounterBounds.oneBudget]
    omega
  | cons x xs ih =>
    have hx:=hg x (by simp)
    have ht:=product_good ctx xs
    have hi:=ih (fun y hy => hg y (by simp [hy]))
    have hm:=SemiprimeD1JetRingBounds.mul_clock ctx x.words (product ctx xs).words ctx.precision
      hx.1.le ht.1.le (fun w hw => (hx.2 w hw).2) (fun w hw => (ht.2 w hw).2)
    change x.clock+(product ctx xs).clock+
      (SemiprimeD1JetRingBits.mul ctx x.words (product ctx xs).words).clock+3 ≤ _
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
    unfold SemiprimeD1LeafCounterBounds.productBudget
    unfold SemiprimeD1LeafCounterBounds.productBudget at hi
    omega

/-- Actual current fresh-axis context at one retained original grid split. -/
def current (parent : Call) (a u : ℕ) (i : Fin a) : Context :=
  let source:=SemiprimeD1OriginalModeAcquisition.acquire parent.net.leftCount
    parent.net.rows.length 64 a u i.val parent.ctx.precision
    (arity parent.net.rows) (owner parent.net.rows)
  let q:=SemiprimeD1ModeRate.jetHeight (edgeCount parent.net) u*(u-i.val)
  ⟨q::parent.ctx.axes,source.precision⟩

/-- Actual sum of the64 repeated child construction reports in one mode. -/
def childClocks (parent : Call) (a u : ℕ)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (i : Fin a) (beta : List ℕ) : ℕ :=
  let source:=SemiprimeD1OriginalModeAcquisition.acquire parent.net.leftCount
    parent.net.rows.length 64 a u i.val parent.ctx.precision
    (arity parent.net.rows) (owner parent.net.rows)
  let q:=SemiprimeD1ModeRate.jetHeight (edgeCount parent.net) u*(u-i.val)
  let fresh:=SemiprimeD1FreshJetBits.acquireFresh parent.ctx q source.precision
  ((List.finRange 64).map (fun g =>
    (SemiprimeD1ChildWordNetwork.fromSource parent.net source i g parent.ctx [q]
      source.precision fresh t beta).clock)).sum

/-- One actual erased mode product retains all64 child construction reports,
including their repeated source/header acquisitions. Structural run canonicality
discharges the physical vector input caps internally. -/
theorem phaseTerm_clock (s fuel : ℕ) (parent : Call) (a u : ℕ)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (i : Fin a) (beta : List ℕ)
    (hpos : parent.ctx.Positive) (huM : u ≤ edgeCount parent.net) (hiu : i.val < u) :
    (phaseTerm (eraseClock (SemiprimeD1WordTapeRecursiveCounter.run s fuel (parent.depth+1)))
      parent a u t i beta).clock ≤ childClocks parent a u t i beta+
      64*(SemiprimeD1LeafCounterBounds.productBudget (current parent a u i)+8)+
      SemiprimeD1LeafCounterBounds.oneBudget (current parent a u i) := by
  unfold phaseTerm
  apply (product_clock _ _ ?_).trans
  · simp only [eraseClock,List.map_map,Function.comp_def,List.length_map,List.length_finRange,
      Nat.add_zero]
    simp only [show ∀ x : ℕ, x+0+5=x+5 from fun x => by omega]
    rw [List.sum_map_add]
    simp only [List.map_const',List.length_finRange,List.sum_const_nat]
    unfold childClocks current
    dsimp only
    omega
  · intro value hv
    obtain ⟨g,hg,rfl⟩:=List.mem_map.mp hv
    exact SemiprimeD1WordTapeRecursiveCounter.run_good _ _ _ _ _
      (SemiprimeD1WordTapeRecursivePhase.current_positive parent.ctx _ _ _ _ hpos huM hiu)

/-- Pure finite nonnegative overhead summation, isolated from source contexts. -/
theorem sum_le_budget {A : Type} (xs : List A) (f g : A → ℕ) (C : ℕ)
    (h : ∀ x ∈ xs, f x ≤ g x+C) :
    (xs.map f).sum ≤ (xs.map g).sum+xs.length*C := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hh:=h x (by simp)
    have ht:=ih (fun y hy => h y (by simp [hy]))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

attribute [local irreducible] SemiprimeD1RecursiveCounter.product

/-- Actual cached-sum loop bound, proved before any concrete source substitution
so known64-group payloads are never normalized during arithmetic elaboration. -/
theorem sumRuns_map_clock {A : Type} (ctx : Context) (xs : List A) (f : A → JetRun)
    (extra : A → ℕ) (C : ℕ)
    (hg : ∀ x ∈ xs, SemiprimeD1JetAffineCoefficientBounds.Good ctx (f x).words)
    (hc : ∀ x ∈ xs, (f x).clock ≤ extra x+C) :
    (SemiprimeD1JetAffineCoefficient.sumRuns ctx (xs.map f)).clock ≤
      (xs.map extra).sum+xs.length*(C+
        SemiprimeD1JetAffineCoefficientBounds.addBudget ctx ctx.precision+3)+ctx.rank+1 := by
  induction xs with
  | nil => simp [SemiprimeD1JetAffineCoefficient.sumRuns,SemiprimeD1JetAffineCoefficient.zero]
  | cons x xs ih =>
    have hhead:=hg x (by simp)
    have htail:=SemiprimeD1JetAffineCoefficientBounds.sumRuns_good ctx (xs.map f)
    have hi:=ih (fun y hy => hg y (by simp [hy])) (fun y hy => hc y (by simp [hy]))
    have hh:=hc x (by simp)
    have ha:=SemiprimeD1JetRingBounds.add_clock ctx (f x).words
      (SemiprimeD1JetAffineCoefficient.sumRuns ctx (xs.map f)).words ctx.precision
      hhead.1.le htail.1.le hhead.2 htail.2
    change (f x).clock+(SemiprimeD1JetAffineCoefficient.sumRuns ctx (xs.map f)).clock+
      (SemiprimeD1JetRingBits.add ctx (f x).words
        (SemiprimeD1JetAffineCoefficient.sumRuns ctx (xs.map f)).words).clock+3 ≤ _
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
    change _ ≤ SemiprimeD1JetAffineCoefficientBounds.addBudget ctx ctx.precision at ha
    nlinarith only [hi,hh,ha]

/-- Each actual mode product has canonical current words independently of
recursive semantic correctness; all physical products construct their own shape. -/
theorem phaseTerm_good (next : Context → Network → JetRun) (parent : Call) (a u : ℕ)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (i : Fin a) (beta : List ℕ) :
    GoodWords (current parent a u i) (phaseTerm next parent a u t i beta).words := by
  unfold phaseTerm current
  exact product_good _ _

/-- Pure arithmetic for composing actual cached-sum reports. -/
theorem sum_clock_arithmetic (X H Y L C A R : ℕ)
    (hX : X ≤ H+L*A+R+1) (hH : H ≤ Y+L*C) :
    X ≤ Y+L*(C+A)+R+1 := by nlinarith only [hX,hH]

attribute [local irreducible] SemiprimeD1WordTapeRecursivePhase.phaseTerm

/-- Fixed vector overhead per mode, beyond the literal64 child constructors. -/
def modeOverhead (ctx : Context) : ℕ :=
  64*(SemiprimeD1LeafCounterBounds.productBudget ctx+8)+
  SemiprimeD1LeafCounterBounds.oneBudget ctx+
  SemiprimeD1JetAffineCoefficientBounds.addBudget ctx ctx.precision+3

/-- All acquired-mode sums retain every repeated actual child constructor and
have a source-derived physical vector overhead, without child-cost advice. -/
theorem phaseTotal_clock (s fuel : ℕ) (parent : Call) (a u : ℕ)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (i : Fin a)
    (hpos : parent.ctx.Positive) (huM : u ≤ edgeCount parent.net) (hiu : i.val < u) :
    let source:=SemiprimeD1OriginalModeAcquisition.acquire parent.net.leftCount
      parent.net.rows.length 64 a u i.val parent.ctx.precision
      (arity parent.net.rows) (owner parent.net.rows)
    (phaseTotal (eraseClock (SemiprimeD1WordTapeRecursiveCounter.run s fuel (parent.depth+1)))
      parent a u t i).clock ≤
      (source.modes.values.map (childClocks parent a u t i)).sum+
      source.modes.values.length*modeOverhead (current parent a u i)+
      (current parent a u i).rank+1 := by
  let src:=SemiprimeD1OriginalModeAcquisition.acquire parent.net.leftCount
    parent.net.rows.length 64 a u i.val parent.ctx.precision
    (arity parent.net.rows) (owner parent.net.rows)
  have h:=sumRuns_map_clock (current parent a u i) src.modes.values
    (phaseTerm (eraseClock (SemiprimeD1WordTapeRecursiveCounter.run s fuel (parent.depth+1)))
      parent a u t i)
    (childClocks parent a u t i)
    (64*(SemiprimeD1LeafCounterBounds.productBudget (current parent a u i)+8)+
      SemiprimeD1LeafCounterBounds.oneBudget (current parent a u i))
    (by
      intro beta hb
      have h:=phaseTerm_good
        (eraseClock (SemiprimeD1WordTapeRecursiveCounter.run s fuel (parent.depth+1))) parent a u t i beta
      exact ⟨h.1,fun w hw => (h.2 w hw).2⟩)
    (by
      intro beta hb
      simpa only [Nat.add_assoc] using phaseTerm_clock s fuel parent a u t i beta hpos huM hiu)
  simpa only [phaseTotal,current,modeOverhead,src,Nat.add_assoc] using h

attribute [local semireducible] SemiprimeD1WordTapeRecursivePhase.phaseTerm

/-- Actual mode summation constructs canonical shape at the computed context. -/
theorem phaseTotal_good (next : Context → Network → JetRun) (parent : Call) (a u : ℕ)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (i : Fin a) :
    GoodWords (current parent a u i) (phaseTotal next parent a u t i).words := by
  unfold phaseTotal current
  exact SemiprimeD1RecursivePhaseBounds.sum_good _ _

/-- Every actual retained coefficient-block copy is paid at its full source size. -/
theorem blocks_clock (parent : Call) (q p : ℕ) (input : JetRun)
    (hg : GoodWords ⟨q::parent.ctx.axes,p⟩ input.words) :
    (((List.range q).map (fun j => SemiprimeD1JetBlockBits.extract parent.ctx j input.words)).map
      (fun block => block.clock)).sum ≤
      q*(parent.ctx.rank*(3*(⟨q::parent.ctx.axes,p⟩:Context).rank+3*p+5)+5*parent.ctx.rank+5) := by
  have h:=List.sum_le_length_nsmul
    (((List.range q).map (fun j => SemiprimeD1JetBlockBits.extract parent.ctx j input.words)).map
      (fun block => block.clock))
    (parent.ctx.rank*(3*(⟨q::parent.ctx.axes,p⟩:Context).rank+3*p+5)+5*parent.ctx.rank+5) (by
      intro c hc
      obtain ⟨block,hblock,rfl⟩:=List.mem_map.mp hc
      obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hblock
      have hc:=SemiprimeD1JetBlockBits.extract_clock parent.ctx j p input.words
        (fun w hw => (hg.2 w hw).2)
      simpa only [hg.1] using hc)
  simpa only [List.length_map,List.length_range,nsmul_eq_mul,Nat.cast_id] using h

/-- Actual nonrecursive phase budget, retaining original source/fresh reports and
EVERY mode/group child constructor. It contains no recursive solved-value input. -/
def phaseBudget (parent : Call) (a u : ℕ)
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
      ((source.modes.values.map (childClocks parent a u t i)).sum+
        source.modes.values.length*modeOverhead ctx+ctx.rank+1)+
      q*(parent.ctx.rank*(3*ctx.rank+3*source.precision+5)+5*parent.ctx.rank+5)+
      10*(edgeCount parent.net+a+u+i.val+q+source.modes.values.length+1)
  else geometry.work+order.work+a+u+order.value+8

/-- The actual erased phase has a literal nonrecursive original-data bound.
All repeated source construction remains visible for the later uniform envelope. -/
theorem phase_local_clock (s fuel : ℕ) (parent : Call) (a u : ℕ)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (hpos : parent.ctx.Positive) (huM : u ≤ edgeCount parent.net) :
    (SemiprimeD1WordTapeRecursivePhase.phase (eraseClock (SemiprimeD1WordTapeRecursiveCounter.run s fuel (parent.depth+1)))
      parent.ctx parent.net a u t).clock ≤ phaseBudget parent a u t := by
  dsimp only [SemiprimeD1WordTapeRecursivePhase.phase,phaseBudget]
  split
  · rename_i hi
    let i : Fin a:=⟨_,hi.1⟩
    let source:=SemiprimeD1OriginalModeAcquisition.acquire parent.net.leftCount
      parent.net.rows.length 64 a u i.val parent.ctx.precision
      (arity parent.net.rows) (owner parent.net.rows)
    let q:=SemiprimeD1ModeRate.jetHeight (edgeCount parent.net) u*(u-i.val)
    let next:=eraseClock (SemiprimeD1WordTapeRecursiveCounter.run s fuel (parent.depth+1))
    have ht:=phaseTotal_clock s fuel parent a u t i hpos huM hi.2.1
    have hg:=phaseTotal_good next parent a u t i
    have hb:=blocks_clock parent q source.precision (phaseTotal next parent a u t i) hg
    have hf:=SemiprimeD1FreshJetBits.acquireFresh_clock parent.ctx q source.precision
    have ht' : (phaseTotal next parent a u t i).clock ≤
        (source.modes.values.map (childClocks parent a u t i)).sum+
        source.modes.values.length*modeOverhead (current parent a u i)+
        (current parent a u i).rank+1 := ht
    change (((List.range q).map (fun j => SemiprimeD1JetBlockBits.extract parent.ctx j
        (phaseTotal next parent a u t i).words)).map (fun block => block.clock)).sum ≤
        q*(parent.ctx.rank*(3*(current parent a u i).rank+3*source.precision+5)+5*parent.ctx.rank+5) at hb
    let fixedStages:=(SemiprimeD1RecoveryWeightRun.geometry a t.val).work+
      (SemiprimeD1RecoveryScalarRun.orderFuel (SemiprimeD1RecoveryWeightRun.geometry a t.val).size
        (SemiprimeD1RecoveryWeightRun.geometry a t.val).point.natAbs).work+source.work
    let allowance:=10*(edgeCount parent.net+a+u+i.val+q+source.modes.values.length+1)
    change fixedStages+(SemiprimeD1FreshJetBits.acquireFresh parent.ctx q source.precision).clock+
        (phaseTotal next parent a u t i).clock+
        (((List.range q).map (fun j => SemiprimeD1JetBlockBits.extract parent.ctx j
          (phaseTotal next parent a u t i).words)).map (fun block => block.clock)).sum+allowance ≤
      fixedStages+(9*source.precision+3*(q*parent.ctx.rank)+10)+
        ((source.modes.values.map (childClocks parent a u t i)).sum+
          source.modes.values.length*modeOverhead (current parent a u i)+(current parent a u i).rank+1)+
        q*(parent.ctx.rank*(3*(current parent a u i).rank+3*source.precision+5)+5*parent.ctx.rank+5)+allowance
    exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_left hf fixedStages) ht') hb) allowance
  · exact le_rfl

end RiemannGaussian.SemiprimeD1WordTapePhaseBudget
