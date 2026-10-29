/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1HybridRecursiveKernel
import RiemannGaussian.SemiprimeD1BoundaryLeaf

/-! # Closed boundary-leaf recursive acquisition

The executed stopping routine is fixed here. Both inactive and exhausted-fuel
calls acquire their own partition and contract the literal local tables through
sorted records. Every acquired phase, mode, child and report is retained.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1HybridRecursiveCounter
open SemiprimeD1JetAxes (Context)
open SemiprimeD1TensorNetwork (Network)
open SemiprimeD1JetAffineCoefficient (JetRun)
open SemiprimeD1RecursiveCallTree (Call children)

/-- Actual acquired frame with the concrete boundary evaluator at a stop. -/
def frame (s : Nat) (parent : Call) (next : Context → Network → JetRun) : JetRun :=
  SemiprimeD1HybridRecursiveKernel.frame SemiprimeD1BoundaryLeaf.checked s parent next

/-- Closed recursion; no replacement leaf or entry supplier is an input. -/
def run (s fuel depth : Nat) (ctx : Context) (net : Network) : JetRun :=
  SemiprimeD1HybridRecursiveKernel.run SemiprimeD1BoundaryLeaf.checked s fuel depth ctx net

/-- Fuel exhaustion executes the boundary routine and pays its own report. -/
theorem run_zero (s depth : Nat) (ctx : Context) (net : Network) :
    run s 0 depth ctx net =
      ⟨(SemiprimeD1BoundaryLeaf.checked ctx net).words,
        (SemiprimeD1BoundaryLeaf.checked ctx net).clock + 5⟩ := rfl

/-- The recursive controller and all of its acquired active modes are preserved. -/
theorem run_succ_frame (s fuel : Nat) (parent : Call) :
    run s (fuel + 1) parent.depth parent.ctx parent.net =
      frame s parent (run s fuel (parent.depth + 1)) := rfl

/-- Exact local work from the concrete boundary recursion. -/
def localWork (s fuel : Nat) (parent : Call) : Nat :=
  SemiprimeD1HybridRecursiveKernel.localWork SemiprimeD1BoundaryLeaf.checked s fuel parent

/-- Proof-side additive inventory of the actual reached calls. -/
def treeWork (s fuel : Nat) (parent : Call) : Nat :=
  SemiprimeD1HybridRecursiveKernel.treeWork SemiprimeD1BoundaryLeaf.checked s fuel parent

/-- All reports from all actual child occurrences are retained exactly once. -/
theorem run_clock (s fuel : Nat) (parent : Call) (hp : parent.ctx.Positive) :
    (run s (fuel + 1) parent.depth parent.ctx parent.net).clock =
      localWork s (fuel + 1) parent +
      ((children s parent).map
        (fun c => (run s fuel c.depth c.ctx c.net).clock)).sum :=
  SemiprimeD1HybridRecursiveKernel.run_clock SemiprimeD1BoundaryLeaf.checked s fuel parent hp

/-- The concrete executed recursion equals its own additive report inventory. -/
theorem run_clock_eq_treeWork (s fuel : Nat) (parent : Call) (hp : parent.ctx.Positive) :
    (run s fuel parent.depth parent.ctx parent.net).clock = treeWork s fuel parent :=
  SemiprimeD1HybridRecursiveKernel.run_clock_eq_treeWork
    SemiprimeD1BoundaryLeaf.checked s fuel parent hp

end RiemannGaussian.SemiprimeD1HybridRecursiveCounter
