/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1WordTapeRecursiveReport

/-! # Structural integration of a concrete replacement leaf

This internal composition keeps the acquired active phases unchanged and uses
the replacement at both stopping sites. Each leaf contributes its own report.
The byte-refinement premise is a proof obligation for the concrete evaluator;
it is not a supplied count, partition, resource bound, or runtime oracle.
-/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option Elab.async false

namespace RiemannGaussian.SemiprimeD1HybridRecursiveKernel
open SemiprimeD1JetAxes SemiprimeD1TensorNetwork
open SemiprimeD1RecursiveCounter SemiprimeD1RecursiveCallTree
open SemiprimeD1PhysicalRecursiveClock
open SemiprimeD1RecursiveCallState
open SemiprimeD1JetAffineCoefficient (JetRun)

/-- One frame with the existing active acquisition and a word-only stopping leaf. -/
def frame (leaf : Context → Network → JetRun) (s : ℕ) (parent : Call)
    (next : Context → Network → JetRun) : JetRun :=
  let lam := SemiprimeD1PackingReady.logarithm s
  let M := edgeCount parent.net
  if activeTest s lam parent.depth M then
    let a := SemiprimeD1Schedule.exponent lam parent.depth
    let u := SemiprimeD1Schedule.levels lam parent.depth
    let grid := SemiprimeD1RecoveryWeightRun.geometry a 0
    let phases := (List.finRange (SemiprimeD1WireKernelOriginal.size a)).map
      (SemiprimeD1WordTapeRecursivePhase.phase next parent.ctx parent.net a u)
    let retained := phases.toArray
    let P := SemiprimeD1ModeRate.workingPrecision M u a 0 parent.ctx.precision
    let outputs := (List.range parent.ctx.rank).map
      (SemiprimeD1PhysicalRecursiveCounter.recoverCoordinate parent.ctx a M u P retained)
    ⟨outputs.map (fun out => out.bits), (phases.map (fun out => out.clock)).sum +
      (outputs.map (fun out => out.clock)).sum + grid.work +
      20 * (s + lam + parent.depth + M + a + u + P + parent.ctx.rank + phases.length + 1)⟩
  else
    let out := leaf parent.ctx parent.net
    ⟨out.words, out.clock + s + lam + parent.depth + M + 8⟩

/-- Both inactive and exhausted-fuel calls execute the same replacement leaf. -/
def run (leaf : Context → Network → JetRun) (s : ℕ) :
    ℕ → ℕ → Context → Network → JetRun
  | 0, _, ctx, net =>
    let out := leaf ctx net
    ⟨out.words, out.clock + 5⟩
  | fuel + 1, depth, ctx, net =>
    frame leaf s ⟨depth, ctx, net⟩ (run leaf s fuel (depth + 1))

/-- An active frame is literally the existing acquired word/tape frame. -/
theorem frame_active (leaf : Context → Network → JetRun) (s : ℕ) (parent : Call)
    (next : Context → Network → JetRun)
    (ha : activeTest s (SemiprimeD1PackingReady.logarithm s) parent.depth
      (edgeCount parent.net) = true) :
    frame leaf s parent next = SemiprimeD1WordTapeRecursiveCounter.frame s parent next := by
  simp only [frame, SemiprimeD1WordTapeRecursiveCounter.frame, ha, ite_true]

/-- An inactive frame retains only its executed leaf and the original control report. -/
theorem frame_inactive (leaf : Context → Network → JetRun) (s : ℕ) (parent : Call)
    (next : Context → Network → JetRun)
    (ha : activeTest s (SemiprimeD1PackingReady.logarithm s) parent.depth
      (edgeCount parent.net) = false) :
    frame leaf s parent next =
      ⟨(leaf parent.ctx parent.net).words, (leaf parent.ctx parent.net).clock + s +
        SemiprimeD1PackingReady.logarithm s + parent.depth + edgeCount parent.net + 8⟩ := by
  simp only [frame, ha, Bool.false_eq_true, ite_false]

/-- Exact leaf bytes suffice to preserve each frame's complete jet output. -/
theorem frame_words_eq_tape (leaf : Context → Network → JetRun)
    (hleaf : ∀ ctx net, ctx.Positive → (leaf ctx net).words =
      (SemiprimeD1TensorNetwork.leaf ctx net).words)
    (s : ℕ) (parent : Call) (next : Context → Network → JetRun)
    (hp : parent.ctx.Positive) :
    (frame leaf s parent next).words =
      (SemiprimeD1WordTapeRecursiveCounter.frame s parent next).words := by
  dsimp only [frame, SemiprimeD1WordTapeRecursiveCounter.frame]
  split
  · rfl
  · exact (hleaf parent.ctx parent.net hp).trans
      (SemiprimeD1TensorTapeLeaf.leaf_words parent.ctx parent.net).symm

/-- Every finite replacement run returns the original physical counter's exact words. -/
theorem run_words_eq_physical (leaf : Context → Network → JetRun)
    (hleaf : ∀ ctx net, ctx.Positive → (leaf ctx net).words =
      (SemiprimeD1TensorNetwork.leaf ctx net).words)
    (s fuel depth : ℕ) (ctx : Context) (net : Network) (hp : ctx.Positive) :
    (run leaf s fuel depth ctx net).words =
      (SemiprimeD1PhysicalRecursiveCounter.run s fuel depth ctx net).words := by
  induction fuel generalizing depth ctx net with
  | zero =>
    exact ((hleaf ctx net hp).trans (SemiprimeD1TensorTapeLeaf.leaf_words ctx net).symm).trans
      (SemiprimeD1WordTapeRecursiveCounter.run_words_eq_physical s 0 depth ctx net hp)
  | succ fuel ih =>
    change (frame leaf s ⟨depth, ctx, net⟩ (run leaf s fuel (depth + 1))).words = _
    rw [frame_words_eq_tape leaf hleaf s ⟨depth, ctx, net⟩ _ hp]
    rw [SemiprimeD1PhysicalRecursiveReport.run_succ_frame s fuel ⟨depth, ctx, net⟩]
    exact SemiprimeD1WordTapeRecursiveCounter.frame_words s ⟨depth, ctx, net⟩ _ _ hp
      (ih (depth + 1))

/-- The replacement's complete output remains canonically encoded. -/
theorem run_good (leaf : Context → Network → JetRun)
    (hleaf : ∀ ctx net, ctx.Positive → (leaf ctx net).words =
      (SemiprimeD1TensorNetwork.leaf ctx net).words)
    (s fuel depth : ℕ) (ctx : Context) (net : Network) (hp : ctx.Positive) :
    SemiprimeD1TensorTables.GoodWords ctx (run leaf s fuel depth ctx net).words := by
  rw [run_words_eq_physical leaf hleaf s fuel depth ctx net hp]
  exact SemiprimeD1PhysicalRecursiveCounter.run_good s fuel depth ctx net

/-- All literal contraction coordinates are preserved on the original valid family. -/
theorem run_words_eq_leaf (leaf : Context → Network → JetRun)
    (hleaf : ∀ ctx net, ctx.Positive → (leaf ctx net).words =
      (SemiprimeD1TensorNetwork.leaf ctx net).words)
    (s fuel depth : ℕ) (ctx : Context) (net : Network) (hp : ctx.Positive)
    (hw : WellFormed net) (hg : Good ctx net) :
    (run leaf s fuel depth ctx net).words = (SemiprimeD1TensorNetwork.leaf ctx net).words :=
  (run_words_eq_physical leaf hleaf s fuel depth ctx net hp).trans
    (SemiprimeD1PhysicalRecursiveCorrectness.run_words_eq_leaf s fuel depth ctx net hp hw hg)

/-- Actual successor frame; no trace or second leaf run is allocated. -/
theorem run_succ_frame (leaf : Context → Network → JetRun) (s fuel : ℕ) (parent : Call) :
    run leaf s (fuel + 1) parent.depth parent.ctx parent.net =
      frame leaf s parent (run leaf s fuel (parent.depth + 1)) := rfl

/-- Each frame separates its local report from all actual child reports. -/
theorem frame_clock (leaf : Context → Network → JetRun) (s : ℕ) (parent : Call)
    (next : Context → Network → JetRun) (hp : parent.ctx.Positive) :
    (frame leaf s parent next).words = (frame leaf s parent (eraseClock next)).words ∧
    (frame leaf s parent next).clock = (frame leaf s parent (eraseClock next)).clock +
      ((children s parent).map (fun c => (next c.ctx c.net).clock)).sum := by
  by_cases ha : activeTest s (SemiprimeD1PackingReady.logarithm s) parent.depth
      (edgeCount parent.net) = true
  · rw [frame_active leaf s parent next ha, frame_active leaf s parent (eraseClock next) ha]
    exact SemiprimeD1WordTapeRecursiveReport.frame_clock s parent next hp
  · have hf : activeTest s (SemiprimeD1PackingReady.logarithm s) parent.depth
        (edgeCount parent.net) = false := by simpa only [Bool.not_eq_true] using ha
    have hc : children s parent = [] := by
      simp only [children, hf, Bool.false_eq_true, ite_false]
    rw [frame_inactive leaf s parent next hf, frame_inactive leaf s parent (eraseClock next) hf, hc]
    simp only [List.map_nil, List.sum_nil, Nat.add_zero, and_self]

/-- Local work uses this run's own leaf clock and actual child payloads. -/
def localWork (leaf : Context → Network → JetRun) (s : ℕ) : ℕ → Call → ℕ
  | 0, parent => (leaf parent.ctx parent.net).clock + 5
  | fuel + 1, parent =>
    (frame leaf s parent (eraseClock (run leaf s fuel (parent.depth + 1)))).clock

/-- The exhausted-fuel branch retains the replacement leaf's actual report. -/
theorem run_zero_clock (leaf : Context → Network → JetRun) (s : ℕ) (parent : Call) :
    (run leaf s 0 parent.depth parent.ctx parent.net).clock = localWork leaf s 0 parent := rfl

/-- Exact successor accounting, including every acquired grid, mode and child. -/
theorem run_clock (leaf : Context → Network → JetRun) (s fuel : ℕ) (parent : Call)
    (hp : parent.ctx.Positive) :
    (run leaf s (fuel + 1) parent.depth parent.ctx parent.net).clock =
      localWork leaf s (fuel + 1) parent +
      ((children s parent).map (fun c => (run leaf s fuel c.depth c.ctx c.net).clock)).sum := by
  rw [run_succ_frame, (frame_clock leaf s parent (run leaf s fuel (parent.depth + 1)) hp).2]
  congr 1
  congr 1
  apply List.map_congr_left
  intro c hc
  rw [mem_children_depth s parent c hc]

/-- Mathematical additive inventory, separate from executable trace storage. -/
def treeWork (leaf : Context → Network → JetRun) (s : ℕ) : ℕ → Call → ℕ
  | 0, parent => localWork leaf s 0 parent
  | fuel + 1, parent => localWork leaf s (fuel + 1) parent +
    ((children s parent).map (treeWork leaf s fuel)).sum

/-- The closed recursion retains exactly its own additive work inventory. -/
theorem run_clock_eq_treeWork (leaf : Context → Network → JetRun) (s fuel : ℕ)
    (parent : Call) (hp : parent.ctx.Positive) :
    (run leaf s fuel parent.depth parent.ctx parent.net).clock = treeWork leaf s fuel parent := by
  induction fuel generalizing parent with
  | zero => rfl
  | succ fuel ih =>
    rw [run_clock leaf s fuel parent hp]
    simp only [treeWork]
    congr 1
    congr 1
    apply List.map_congr_left
    intro c hc
    exact ih c (SemiprimeD1WordTapeRecursiveReport.mem_children_positive s parent c hc hp)

end RiemannGaussian.SemiprimeD1HybridRecursiveKernel
