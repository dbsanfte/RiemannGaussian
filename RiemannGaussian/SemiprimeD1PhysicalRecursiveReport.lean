/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PhysicalRecursiveClock
import RiemannGaussian.SemiprimeD1RecursiveCallState

/-! # Actual one-step and whole recursive report recurrence
The local erased frame is a contribution measure retaining actual child data,
not a separately executed free solver. All repeated source/header reports remain.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace RiemannGaussian.SemiprimeD1PhysicalRecursiveReport
open SemiprimeD1JetAxes SemiprimeD1TensorNetwork SemiprimeD1RecursiveCounter
open SemiprimeD1RecursiveCallTree SemiprimeD1PhysicalRecursiveClock
open SemiprimeD1RecursiveCallState
open SemiprimeD1JetAffineCoefficient (JetRun)
attribute [local irreducible] SemiprimeD1OriginalModeAcquisition.acquire

/-- The exact nonrecursive frame of the new run, with its continuation explicit
only for the internal report-separation proof. -/
def frame (s : ℕ) (parent : Call) (next : Context → Network → JetRun) : JetRun :=
  let lam := SemiprimeD1PackingReady.logarithm s
  let M := edgeCount parent.net
  if activeTest s lam parent.depth M then
    let a := SemiprimeD1Schedule.exponent lam parent.depth
    let u := SemiprimeD1Schedule.levels lam parent.depth
    let grid := SemiprimeD1RecoveryWeightRun.geometry a 0
    let phases := (List.finRange (SemiprimeD1WireKernelOriginal.size a)).map
      (phase next parent.ctx parent.net a u)
    let retained := phases.toArray
    let P := SemiprimeD1ModeRate.workingPrecision M u a 0 parent.ctx.precision
    let outputs := (List.range parent.ctx.rank).map (SemiprimeD1PhysicalRecursiveCounter.recoverCoordinate parent.ctx a M u P retained)
    ⟨outputs.map (fun out => out.bits),(phases.map (fun out => out.clock)).sum+
      (outputs.map (fun out => out.clock)).sum+grid.work+
      20*(s+lam+parent.depth+M+a+u+P+parent.ctx.rank+phases.length+1)⟩
  else
    let leaf := SemiprimeD1TensorNetwork.leaf parent.ctx parent.net
    ⟨leaf.words,leaf.clock+s+lam+parent.depth+M+8⟩

/-- The new structural successor is this exact frame with its own predecessor. -/
theorem run_succ_frame (s fuel : ℕ) (parent : Call) :
    SemiprimeD1PhysicalRecursiveCounter.run s (fuel+1) parent.depth parent.ctx parent.net=
      frame s parent (SemiprimeD1PhysicalRecursiveCounter.run s fuel (parent.depth+1)) := rfl

/-- Exact local/child separation of the actual one-step program. The zero-clock
continuation retains all actual payloads; no report is omitted or shared. -/
theorem frame_clock (s : ℕ) (parent : Call) (next : Context → Network → JetRun) :
    (frame s parent next).words=(frame s parent (eraseClock next)).words ∧
    (frame s parent next).clock=(frame s parent (eraseClock next)).clock+
      ((children s parent).map (fun c => (next c.ctx c.net).clock)).sum := by
  dsimp only [frame,children]
  split
  · let lam:=SemiprimeD1PackingReady.logarithm s
    let a:=SemiprimeD1Schedule.exponent lam parent.depth
    let u:=SemiprimeD1Schedule.levels lam parent.depth
    let P:=SemiprimeD1ModeRate.workingPrecision (edgeCount parent.net) u a 0 parent.ctx.precision
    have hr:=retained_blocks next parent a u
    have ho : (List.range parent.ctx.rank).map
        (SemiprimeD1PhysicalRecursiveCounter.recoverCoordinate parent.ctx a (edgeCount parent.net) u P
          (SemiprimeD1RecursiveRecovery.retained next parent.ctx parent.net a u))=
      (List.range parent.ctx.rank).map
        (SemiprimeD1PhysicalRecursiveCounter.recoverCoordinate parent.ctx a (edgeCount parent.net) u P
          (SemiprimeD1RecursiveRecovery.retained (eraseClock next) parent.ctx parent.net a u)) := by
      apply List.map_congr_left
      intro k hk
      exact recoverCoordinate_congr parent.ctx a (edgeCount parent.net) u P _ _ k hr
    have hp:=phases_clock next parent a u
    constructor
    · exact congrArg (List.map CoordinateRun.bits) ho
    · change
        (((List.finRange (SemiprimeD1WireKernelOriginal.size a)).map
          (phase next parent.ctx parent.net a u)).map PhaseRun.clock).sum+
        (((List.range parent.ctx.rank).map
          (SemiprimeD1PhysicalRecursiveCounter.recoverCoordinate parent.ctx a (edgeCount parent.net) u P
            (SemiprimeD1RecursiveRecovery.retained next parent.ctx parent.net a u))).map CoordinateRun.clock).sum+_+_ =
        (((List.finRange (SemiprimeD1WireKernelOriginal.size a)).map
          (phase (eraseClock next) parent.ctx parent.net a u)).map PhaseRun.clock).sum+
        (((List.range parent.ctx.rank).map
          (SemiprimeD1PhysicalRecursiveCounter.recoverCoordinate parent.ctx a (edgeCount parent.net) u P
            (SemiprimeD1RecursiveRecovery.retained (eraseClock next) parent.ctx parent.net a u))).map CoordinateRun.clock).sum+_+_+_
      rw [hp,ho]
      simp only [List.length_map,List.length_finRange]
      dsimp only [a,u,lam,P]
      omega
  · simp only [List.map_nil,List.sum_nil,Nat.add_zero,and_self]

/-- Exact local contribution for THIS structural run and its actual child payloads.
This proof-side measure is not a free-standing executable child solver. -/
def localWork (s : ℕ) : ℕ → Call → ℕ
  | 0,parent => (SemiprimeD1TensorNetwork.leaf parent.ctx parent.net).clock+5
  | fuel+1,parent =>
    (frame s parent (eraseClock
      (SemiprimeD1PhysicalRecursiveCounter.run s fuel (parent.depth+1)))).clock

/-- Exact actual successor report recurrence in the literal child-call inventory. -/
theorem run_clock (s fuel : ℕ) (parent : Call) :
    (SemiprimeD1PhysicalRecursiveCounter.run s (fuel+1) parent.depth parent.ctx parent.net).clock=
      localWork s (fuel+1) parent+
      ((children s parent).map (fun c =>
        (SemiprimeD1PhysicalRecursiveCounter.run s fuel c.depth c.ctx c.net).clock)).sum := by
  rw [run_succ_frame]
  rw [(frame_clock s parent (SemiprimeD1PhysicalRecursiveCounter.run s fuel (parent.depth+1))).2]
  congr 1
  congr 1
  apply List.map_congr_left
  intro c hc
  rw [mem_children_depth s parent c hc]

/-- Fuel-zero report is exactly its actual eager leaf contribution. -/
theorem run_zero_clock (s : ℕ) (parent : Call) :
    (SemiprimeD1PhysicalRecursiveCounter.run s 0 parent.depth parent.ctx parent.net).clock=
      localWork s 0 parent := rfl

/-- Exact additive report over the literal recursive child inventory. This is
an erased mathematical recurrence, not an allocated execution trace. -/
def treeWork (s : ℕ) : ℕ → Call → ℕ
  | 0,parent => localWork s 0 parent
  | fuel+1,parent => localWork s (fuel+1) parent+
    ((children s parent).map (treeWork s fuel)).sum

/-- The actual closed program's report equals its exact child-inventory recurrence. -/
theorem run_clock_eq_treeWork (s fuel : ℕ) (parent : Call) :
    (SemiprimeD1PhysicalRecursiveCounter.run s fuel parent.depth parent.ctx parent.net).clock=
      treeWork s fuel parent := by
  induction fuel generalizing parent with
  | zero => exact run_zero_clock s parent
  | succ fuel ih =>
    rw [run_clock]
    simp only [treeWork]
    congr 1
    congr 1
    apply List.map_congr_left
    intro c hc
    exact ih c

/-- Internal summation principle for a derived uniform local envelope. The final
original-resource endpoint must prove this premise from actual state/component
bounds; it is not a caller-supplied counter or child-cost function. -/
theorem run_clock_le_count (s fuel B : ℕ) (root : Call)
    (hlocal : ∀ c, Reach s root c → ∀ f ≤ fuel, localWork s f c ≤ B) :
    (SemiprimeD1PhysicalRecursiveCounter.run s fuel root.depth root.ctx root.net).clock ≤
      B*count s fuel root := by
  rw [run_clock_eq_treeWork]
  have go : ∀ f ≤ fuel, ∀ c, Reach s root c → treeWork s f c ≤ B*count s f c := by
    intro f
    induction f with
    | zero =>
      intro hf c hr
      simpa only [treeWork,count,Nat.mul_one] using hlocal c hr 0 hf
    | succ f ih =>
      intro hf c hr
      have hs : ((children s c).map (treeWork s f)).sum ≤
          ((children s c).map (fun child => B*count s f child)).sum := by
        apply List.sum_le_sum
        intro child hchild
        exact ih (by omega) child (Reach.step hr hchild)
      simp only [treeWork,count]
      rw [List.sum_map_mul_left] at hs
      nlinarith only [hs,hlocal c hr (f+1) hf]
  exact go fuel le_rfl root Reach.root

end RiemannGaussian.SemiprimeD1PhysicalRecursiveReport
