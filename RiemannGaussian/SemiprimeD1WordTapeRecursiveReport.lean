/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1WordTapeRecursiveCounter
import RiemannGaussian.SemiprimeD1WordTapeRecursiveClock

/-! # Exact retained-report recurrence for the tape-leaf recursion
Active local reports are derived from actual phase/recovery data. Changed leaf
reports are retained literally; no old/new total clock equality is assumed.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace RiemannGaussian.SemiprimeD1WordTapeRecursiveReport
open SemiprimeD1JetAxes SemiprimeD1TensorNetwork SemiprimeD1RecursiveCounter
open SemiprimeD1RecursiveCallTree SemiprimeD1PhysicalRecursiveClock
open SemiprimeD1RecursiveCallState SemiprimeD1WordTapeRecursiveCounter
open SemiprimeD1JetAffineCoefficient (JetRun)
attribute [local irreducible] SemiprimeD1OriginalModeAcquisition.acquire

/-- The new structural successor is this exact frame with its own predecessor. -/
theorem run_succ_frame (s fuel : ℕ) (parent : Call) :
    SemiprimeD1WordTapeRecursiveCounter.run s (fuel+1) parent.depth parent.ctx parent.net=
      frame s parent (SemiprimeD1WordTapeRecursiveCounter.run s fuel (parent.depth+1)) := rfl

/-- Exact local/child separation of the actual one-step program. The zero-clock
continuation retains all actual payloads; no report is omitted or shared. -/
theorem frame_clock (s : ℕ) (parent : Call) (next : Context → Network → JetRun)
    (hpos : parent.ctx.Positive) :
    (frame s parent next).words=(frame s parent (eraseClock next)).words ∧
    (frame s parent next).clock=(frame s parent (eraseClock next)).clock+
      ((children s parent).map (fun c => (next c.ctx c.net).clock)).sum := by
  dsimp only [frame,children]
  split
  · rename_i ha
    let lam:=SemiprimeD1PackingReady.logarithm s
    let a:=SemiprimeD1Schedule.exponent lam parent.depth
    let u:=SemiprimeD1Schedule.levels lam parent.depth
    let P:=SemiprimeD1ModeRate.workingPrecision (edgeCount parent.net) u a 0 parent.ctx.precision
    have huM : u ≤ edgeCount parent.net := ((activeTest_correct _ _ _ _).mp ha).2.2
    have hr:=SemiprimeD1WordTapeRecursiveClock.retained_blocks next parent a u hpos huM
    have ho : (List.range parent.ctx.rank).map
        (SemiprimeD1PhysicalRecursiveCounter.recoverCoordinate parent.ctx a (edgeCount parent.net) u P
          (SemiprimeD1WordTapeRecursiveClock.retained next parent a u))=
      (List.range parent.ctx.rank).map
        (SemiprimeD1PhysicalRecursiveCounter.recoverCoordinate parent.ctx a (edgeCount parent.net) u P
          (SemiprimeD1WordTapeRecursiveClock.retained (eraseClock next) parent a u)) := by
      apply List.map_congr_left
      intro k hk
      exact recoverCoordinate_congr parent.ctx a (edgeCount parent.net) u P _ _ k hr
    have hp:=SemiprimeD1WordTapeRecursiveClock.phases_clock next parent a u hpos huM
    constructor
    · exact congrArg (List.map CoordinateRun.bits) ho
    · change
        (((List.finRange (SemiprimeD1WireKernelOriginal.size a)).map
          (SemiprimeD1WordTapeRecursivePhase.phase next parent.ctx parent.net a u)).map PhaseRun.clock).sum+
        (((List.range parent.ctx.rank).map
          (SemiprimeD1PhysicalRecursiveCounter.recoverCoordinate parent.ctx a (edgeCount parent.net) u P
            (SemiprimeD1WordTapeRecursiveClock.retained next parent a u))).map CoordinateRun.clock).sum+_+_ =
        (((List.finRange (SemiprimeD1WireKernelOriginal.size a)).map
          (SemiprimeD1WordTapeRecursivePhase.phase (eraseClock next) parent.ctx parent.net a u)).map PhaseRun.clock).sum+
        (((List.range parent.ctx.rank).map
          (SemiprimeD1PhysicalRecursiveCounter.recoverCoordinate parent.ctx a (edgeCount parent.net) u P
            (SemiprimeD1WordTapeRecursiveClock.retained (eraseClock next) parent a u))).map CoordinateRun.clock).sum+_+_+_
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
      (SemiprimeD1WordTapeRecursiveCounter.run s fuel (parent.depth+1)))).clock

/-- Exact actual successor report recurrence in the literal child-call inventory. -/
theorem run_clock (s fuel : ℕ) (parent : Call) (hpos : parent.ctx.Positive) :
    (SemiprimeD1WordTapeRecursiveCounter.run s (fuel+1) parent.depth parent.ctx parent.net).clock=
      localWork s (fuel+1) parent+
      ((children s parent).map (fun c =>
        (SemiprimeD1WordTapeRecursiveCounter.run s fuel c.depth c.ctx c.net).clock)).sum := by
  rw [run_succ_frame]
  rw [(frame_clock s parent (SemiprimeD1WordTapeRecursiveCounter.run s fuel (parent.depth+1)) hpos).2]
  congr 1
  congr 1
  apply List.map_congr_left
  intro c hc
  rw [mem_children_depth s parent c hc]

/-- Fuel-zero report is exactly its actual eager leaf contribution. -/
theorem run_zero_clock (s : ℕ) (parent : Call) :
    (SemiprimeD1WordTapeRecursiveCounter.run s 0 parent.depth parent.ctx parent.net).clock=
      localWork s 0 parent := rfl

/-- Exact additive report over the literal recursive child inventory. This is
an erased mathematical recurrence, not an allocated execution trace. -/
def treeWork (s : ℕ) : ℕ → Call → ℕ
  | 0,parent => localWork s 0 parent
  | fuel+1,parent => localWork s (fuel+1) parent+
    ((children s parent).map (treeWork s fuel)).sum

/-- Actual active guards propagate positive axes to every real child call. -/
theorem mem_children_positive (s : ℕ) (parent next : Call) (hm : next∈children s parent)
    (hp : parent.ctx.Positive) : next.ctx.Positive := by
  obtain ⟨ha,t,ht⟩ := (mem_children s parent next).mp hm
  obtain ⟨hi,beta,_,g,rfl⟩ := (mem_phaseChildren parent _ _ t next).mp ht
  have hactive:=(activeTest_correct _ _ _ _).mp ha
  have hh:=height_positive _ _ (by omega) hactive.2.2
  exact child_positive parent _ _ t _ beta g hp (Nat.mul_pos hh (Nat.sub_pos_of_lt hi.2.1))

/-- The actual closed program's report equals its exact child-inventory recurrence. -/
theorem run_clock_eq_treeWork (s fuel : ℕ) (parent : Call) (hpos : parent.ctx.Positive) :
    (SemiprimeD1WordTapeRecursiveCounter.run s fuel parent.depth parent.ctx parent.net).clock=
      treeWork s fuel parent := by
  induction fuel generalizing parent with
  | zero => exact run_zero_clock s parent
  | succ fuel ih =>
    rw [run_clock s fuel parent hpos]
    simp only [treeWork]
    congr 1
    congr 1
    apply List.map_congr_left
    intro c hc
    exact ih c (mem_children_positive s parent c hc hpos)



/-- Inactive local work is the actual tape leaf, not an old report. -/
theorem localWork_inactive (s fuel : ℕ) (parent : Call)
    (ha : activeTest s (SemiprimeD1PackingReady.logarithm s) parent.depth (edgeCount parent.net)=false) :
    localWork s (fuel+1) parent=(SemiprimeD1TensorTapeLeaf.leaf parent.ctx parent.net).clock+
      s+SemiprimeD1PackingReady.logarithm s+parent.depth+edgeCount parent.net+8 := by
  simp only [localWork,frame,ha,Bool.false_eq_true,ite_false]

end RiemannGaussian.SemiprimeD1WordTapeRecursiveReport
