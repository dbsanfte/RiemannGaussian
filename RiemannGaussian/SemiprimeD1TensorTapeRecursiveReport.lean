/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1TensorTapeRecursiveCounter

/-! # Exact retained-report recurrence for the tape-leaf recursion
Active local reports are derived from actual phase/recovery data. Changed leaf
reports are retained literally; no old/new total clock equality is assumed.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace RiemannGaussian.SemiprimeD1TensorTapeRecursiveReport
open SemiprimeD1JetAxes SemiprimeD1TensorNetwork SemiprimeD1RecursiveCounter
open SemiprimeD1RecursiveCallTree SemiprimeD1PhysicalRecursiveClock
open SemiprimeD1RecursiveCallState SemiprimeD1TensorTapeRecursiveCounter
open SemiprimeD1JetAffineCoefficient (JetRun)
attribute [local irreducible] SemiprimeD1OriginalModeAcquisition.acquire

/-- The new structural successor is this exact frame with its own predecessor. -/
theorem run_succ_frame (s fuel : ℕ) (parent : Call) :
    SemiprimeD1TensorTapeRecursiveCounter.run s (fuel+1) parent.depth parent.ctx parent.net=
      frame s parent (SemiprimeD1TensorTapeRecursiveCounter.run s fuel (parent.depth+1)) := rfl

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
  | 0,parent => (SemiprimeD1TensorTapeLeaf.leaf parent.ctx parent.net).clock+5
  | fuel+1,parent =>
    (frame s parent (eraseClock
      (SemiprimeD1TensorTapeRecursiveCounter.run s fuel (parent.depth+1)))).clock

/-- Exact actual successor report recurrence in the literal child-call inventory. -/
theorem run_clock (s fuel : ℕ) (parent : Call) :
    (SemiprimeD1TensorTapeRecursiveCounter.run s (fuel+1) parent.depth parent.ctx parent.net).clock=
      localWork s (fuel+1) parent+
      ((children s parent).map (fun c =>
        (SemiprimeD1TensorTapeRecursiveCounter.run s fuel c.depth c.ctx c.net).clock)).sum := by
  rw [run_succ_frame]
  rw [(frame_clock s parent (SemiprimeD1TensorTapeRecursiveCounter.run s fuel (parent.depth+1))).2]
  congr 1
  congr 1
  apply List.map_congr_left
  intro c hc
  rw [mem_children_depth s parent c hc]

/-- Fuel-zero report is exactly its actual eager leaf contribution. -/
theorem run_zero_clock (s : ℕ) (parent : Call) :
    (SemiprimeD1TensorTapeRecursiveCounter.run s 0 parent.depth parent.ctx parent.net).clock=
      localWork s 0 parent := rfl

/-- Exact additive report over the literal recursive child inventory. This is
an erased mathematical recurrence, not an allocated execution trace. -/
def treeWork (s : ℕ) : ℕ → Call → ℕ
  | 0,parent => localWork s 0 parent
  | fuel+1,parent => localWork s (fuel+1) parent+
    ((children s parent).map (treeWork s fuel)).sum

/-- The actual closed program's report equals its exact child-inventory recurrence. -/
theorem run_clock_eq_treeWork (s fuel : ℕ) (parent : Call) :
    (SemiprimeD1TensorTapeRecursiveCounter.run s fuel parent.depth parent.ctx parent.net).clock=
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


/-- The active frame is literally the unchanged physical source/child/recovery code. -/
theorem frame_active (s : ℕ) (parent : Call) (next : Context → Network → JetRun)
    (ha : activeTest s (SemiprimeD1PackingReady.logarithm s) parent.depth (edgeCount parent.net)=true) :
    frame s parent next=SemiprimeD1PhysicalRecursiveReport.frame s parent next := by
  simp only [frame,SemiprimeD1PhysicalRecursiveReport.frame,ha,ite_true]

/-- Only the erased active local report is identified: child payload equality is
proved first, and actual changed leaf/child clocks are never transferred. -/
theorem localWork_active (s fuel : ℕ) (parent : Call)
    (ha : activeTest s (SemiprimeD1PackingReady.logarithm s) parent.depth (edgeCount parent.net)=true) :
    localWork s (fuel+1) parent=SemiprimeD1PhysicalRecursiveReport.localWork s (fuel+1) parent := by
  change (frame s parent (eraseClock
    (SemiprimeD1TensorTapeRecursiveCounter.run s fuel (parent.depth+1)))).clock=_
  rw [frame_active s parent _ ha]
  have he:=SemiprimeD1TensorTapeRecursiveCounter.eraseClock_congr
    (SemiprimeD1TensorTapeRecursiveCounter.run s fuel (parent.depth+1))
    (SemiprimeD1PhysicalRecursiveCounter.run s fuel (parent.depth+1))
    (fun ctx net => SemiprimeD1TensorTapeRecursiveCounter.run_words_eq_physical s fuel (parent.depth+1) ctx net)
  exact congrArg (fun next => (SemiprimeD1PhysicalRecursiveReport.frame s parent next).clock) he

/-- Inactive local work retains the new executed tape leaf, not the old clock. -/
theorem localWork_inactive (s fuel : ℕ) (parent : Call)
    (ha : activeTest s (SemiprimeD1PackingReady.logarithm s) parent.depth (edgeCount parent.net)=false) :
    localWork s (fuel+1) parent=(SemiprimeD1TensorTapeLeaf.leaf parent.ctx parent.net).clock+
      s+SemiprimeD1PackingReady.logarithm s+parent.depth+edgeCount parent.net+8 := by
  simp only [localWork,frame,ha,Bool.false_eq_true,ite_false]

end RiemannGaussian.SemiprimeD1TensorTapeRecursiveReport
