/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1WordTapeRecursivePhase

/-! # Closed own recursion with physical word packets and tape table copies
Every active child uses the new concrete word/tape child constructor. Actual
fresh-axis positivity is derived from retained phase and schedule guards.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace RiemannGaussian.SemiprimeD1WordTapeRecursiveCounter
open SemiprimeD1JetAxes SemiprimeD1TensorNetwork
open SemiprimeD1RecursiveCounter SemiprimeD1RecursiveCallTree
open SemiprimeD1PhysicalRecursiveClock
open SemiprimeD1JetAffineCoefficient (JetRun)

/-- Internal successor frame, fixed to physical recovery and tape-backed leaves. -/
def frame (s : ℕ) (parent : Call) (next : Context → Network → JetRun) : JetRun :=
  let lam:=SemiprimeD1PackingReady.logarithm s
  let M:=edgeCount parent.net
  if activeTest s lam parent.depth M then
    let a:=SemiprimeD1Schedule.exponent lam parent.depth
    let u:=SemiprimeD1Schedule.levels lam parent.depth
    let grid:=SemiprimeD1RecoveryWeightRun.geometry a 0
    let phases:=(List.finRange (SemiprimeD1WireKernelOriginal.size a)).map
      (SemiprimeD1WordTapeRecursivePhase.phase next parent.ctx parent.net a u)
    let retained:=phases.toArray
    let P:=SemiprimeD1ModeRate.workingPrecision M u a 0 parent.ctx.precision
    let outputs:=(List.range parent.ctx.rank).map
      (SemiprimeD1PhysicalRecursiveCounter.recoverCoordinate parent.ctx a M u P retained)
    ⟨outputs.map (fun out => out.bits),(phases.map (fun out => out.clock)).sum+
      (outputs.map (fun out => out.clock)).sum+grid.work+
      20*(s+lam+parent.depth+M+a+u+P+parent.ctx.rank+phases.length+1)⟩
  else
    let leaf:=SemiprimeD1TensorTapeLeaf.leaf parent.ctx parent.net
    ⟨leaf.words,leaf.clock+s+lam+parent.depth+M+8⟩

/-- Closed finite recursion: every active child invokes this function's predecessor. -/
def run (s : ℕ) : ℕ → ℕ → Context → Network → JetRun
  | 0,_,ctx,net =>
    let leaf:=SemiprimeD1TensorTapeLeaf.leaf ctx net
    ⟨leaf.words,leaf.clock+5⟩
  | fuel+1,depth,ctx,net => frame s ⟨depth,ctx,net⟩ (run s fuel (depth+1))

/-- Actual new and old frames agree in bytes after proved positive-context child refinement. -/
theorem frame_words (s : ℕ) (parent : Call) (f g : Context → Network → JetRun)
    (hp : parent.ctx.Positive)
    (h : ∀ctx net,ctx.Positive → (f ctx net).words=(g ctx net).words) :
    (frame s parent f).words=(SemiprimeD1PhysicalRecursiveReport.frame s parent g).words := by
  dsimp only [frame,SemiprimeD1PhysicalRecursiveReport.frame]
  split
  · rename_i ha
    let lam:=SemiprimeD1PackingReady.logarithm s
    let a:=SemiprimeD1Schedule.exponent lam parent.depth
    let u:=SemiprimeD1Schedule.levels lam parent.depth
    let P:=SemiprimeD1ModeRate.workingPrecision (edgeCount parent.net) u a 0 parent.ctx.precision
    have huM : u ≤ edgeCount parent.net := ((activeTest_correct _ _ _ _).mp ha).2.2
    let fs:=((List.finRange (SemiprimeD1WireKernelOriginal.size a)).map
      (SemiprimeD1WordTapeRecursivePhase.phase f parent.ctx parent.net a u)).toArray
    let gs:=((List.finRange (SemiprimeD1WireKernelOriginal.size a)).map
      (phase g parent.ctx parent.net a u)).toArray
    have hb : fs.map PhaseRun.blocks=gs.map PhaseRun.blocks := by
      apply Array.toList_inj.mp
      simp only [fs,gs,Array.toList_map,List.map_map,Function.comp_def]
      apply List.map_congr_left
      intro t ht
      exact (SemiprimeD1WordTapeRecursivePhase.phase_data f g parent a u t hp huM h).1
    have ho : (List.range parent.ctx.rank).map
        (SemiprimeD1PhysicalRecursiveCounter.recoverCoordinate parent.ctx a (edgeCount parent.net) u P fs)=
      (List.range parent.ctx.rank).map
        (SemiprimeD1PhysicalRecursiveCounter.recoverCoordinate parent.ctx a (edgeCount parent.net) u P gs) := by
      apply List.map_congr_left
      intro k hk
      exact recoverCoordinate_congr parent.ctx a (edgeCount parent.net) u P fs gs k hb
    exact congrArg (List.map CoordinateRun.bits) ho
  · exact SemiprimeD1TensorTapeLeaf.leaf_words parent.ctx parent.net

/-- Literal-byte correctness of every finite run on the actual positive-context family. -/
theorem run_words_eq_physical (s fuel depth : ℕ) (ctx : Context) (net : Network)
    (hp : ctx.Positive) :
    (run s fuel depth ctx net).words=
      (SemiprimeD1PhysicalRecursiveCounter.run s fuel depth ctx net).words := by
  induction fuel generalizing depth ctx net with
  | zero => exact SemiprimeD1TensorTapeLeaf.leaf_words ctx net
  | succ fuel ih =>
    change (frame s ⟨depth,ctx,net⟩ (run s fuel (depth+1))).words=_
    rw [SemiprimeD1PhysicalRecursiveReport.run_succ_frame s fuel ⟨depth,ctx,net⟩]
    exact frame_words s ⟨depth,ctx,net⟩ _ _ hp (ih (depth+1))

/-- Canonical output derives from the actual original positive context, not Fits advice. -/
theorem run_good (s fuel depth : ℕ) (ctx : Context) (net : Network) (hp : ctx.Positive) :
    SemiprimeD1TensorTables.GoodWords ctx (run s fuel depth ctx net).words := by
  rw [run_words_eq_physical s fuel depth ctx net hp]
  exact SemiprimeD1PhysicalRecursiveCounter.run_good s fuel depth ctx net

/-- Original literal contraction semantics for actual Positive/WF/Good networks. -/
theorem run_words_eq_leaf (s fuel depth : ℕ) (ctx : Context) (net : Network)
    (hp : ctx.Positive) (hw : WellFormed net) (hg : Good ctx net) :
    (run s fuel depth ctx net).words=(SemiprimeD1TensorNetwork.leaf ctx net).words :=
  (run_words_eq_physical s fuel depth ctx net hp).trans
    (SemiprimeD1PhysicalRecursiveCorrectness.run_words_eq_leaf s fuel depth ctx net hp hw hg)

/-- Actual exhausted-fuel branch retains the concrete tape leaf's entire report. -/
theorem run_zero_clock (s depth : ℕ) (ctx : Context) (net : Network) :
    (run s 0 depth ctx net).clock=(SemiprimeD1TensorTapeLeaf.leaf ctx net).clock+5 := rfl

/-- Actual failed-test branch retains the concrete tape leaf's entire report. -/
theorem run_inactive_clock (s fuel depth : ℕ) (ctx : Context) (net : Network)
    (h : activeTest s (SemiprimeD1PackingReady.logarithm s) depth (edgeCount net)=false) :
    (run s (fuel+1) depth ctx net).clock=(SemiprimeD1TensorTapeLeaf.leaf ctx net).clock+
      s+SemiprimeD1PackingReady.logarithm s+depth+edgeCount net+8 := by
  simp only [run,frame,h,Bool.false_eq_true,ite_false]

end RiemannGaussian.SemiprimeD1WordTapeRecursiveCounter
