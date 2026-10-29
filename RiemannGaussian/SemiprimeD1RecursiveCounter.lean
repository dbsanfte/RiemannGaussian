/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ChildNetwork
import RiemannGaussian.SemiprimeD1FreshJetBits
import RiemannGaussian.SemiprimeD1JetBlockBits
import RiemannGaussian.SemiprimeD1RecoveryFinishBits
import RiemannGaussian.SemiprimeD1TensorNetworkModes
import RiemannGaussian.SemiprimeD1LeafCounterBounds

/-! # Concrete finite recursive counter dataflow
All child graphs/tables, finite mode queries, fresh jets, retained coefficient
blocks and scalar recovery words are actually constructed from literal input
network data. The recursive successor is closed internally, never supplied as
a count or entry oracle. Fuel gives unconditional termination.

This module defines the executed controller. Its full D.16 correctness and
whole-tree primitive bit/address clock are subsequent obligations. The report
retains called component reports and explicit finite control allowances; it is
not yet asserted equal to a complete primitive-machine execution time.
-/
set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace RiemannGaussian.SemiprimeD1RecursiveCounter
open SemiprimeD1JetAxes SemiprimeD1TensorNetwork
open SemiprimeD1JetAffineCoefficient (JetRun)

/-- Actual finite schedule test, using decidable native arithmetic only. -/
def activeTest (s lam depth M : ℕ) : Bool :=
  decide (SemiprimeD1Schedule.leafSize s lam < M) &&
    decide (SemiprimeD1PrecisionEnvelope.minimumLevels lam ≤ SemiprimeD1Schedule.levels lam depth) &&
    decide (SemiprimeD1Schedule.levels lam depth ≤ M)

/-- The controller's executed test is exactly the proved schedule predicate. -/
theorem activeTest_correct (s lam depth M : ℕ) :
    activeTest s lam depth M = true ↔ SemiprimeD1Schedule.Active s lam depth M := by
  simp only [activeTest,Bool.and_eq_true,decide_eq_true_eq,SemiprimeD1Schedule.Active,and_assoc]

/-- Actual physical product of a cached list of child coefficient vectors. -/
def product (ctx : Context) : List JetRun → JetRun
  | [] => SemiprimeD1JetAffineCoefficient.one ctx
  | x::xs =>
    let tail := product ctx xs
    let out := SemiprimeD1JetRingBits.mul ctx x.words tail.words
    ⟨out.words,x.clock+tail.clock+out.clock+3⟩

/-- The executed cached child product is exactly the product in the actual
current multijet ring, preserving all original child reports. -/
theorem product_value (ctx : Context) (hpos : ctx.Positive) (values : List JetRun) :
    SemiprimeD1JetInterpretation.interpret ctx (product ctx values).words =
      (values.map (fun value => SemiprimeD1JetInterpretation.interpret ctx value.words)).prod := by
  induction values with
  | nil => exact SemiprimeD1JetAffineCoefficient.interpret_one ctx hpos
  | cons x xs ih =>
    change SemiprimeD1JetInterpretation.interpret ctx
      (SemiprimeD1JetRingBits.mul ctx x.words (product ctx xs).words).words = _
    rw [SemiprimeD1JetOperations.interpret_mul ctx _ _ hpos,ih]
    rfl

/-- Cached fresh-axis coefficient blocks for one original grid node. -/
structure PhaseRun where
  /-- Actual old-coordinate vectors, one for each retained fresh coefficient. -/
  blocks : Array (List (List Bool))
  /-- Actual working scalar precision at this node, zero when inactive. -/
  precision : ℕ
  /-- All called source/child/vector/block reports retained. -/
  clock : ℕ

/-- Literal empty retained data for a non-retained original grid point. -/
def emptyPhase : PhaseRun := ⟨#[],0,1⟩

/-- Actual copy of one old coordinate from every retained child coefficient block. -/
structure CoordinateData where
  /-- Original-node-indexed arrays of physically copied coefficient words. -/
  values : Array (Array (List Bool))
  /-- Every dense coordinate read/copy and finite array cell. -/
  clock : ℕ

/-- Prepare actual scalar recovery input from stored phase blocks, with no
coefficient or child-word callback supplied from outside the controller. -/
def coordinate (phases : Array PhaseRun) (k : ℕ) : CoordinateData :=
  let rows := phases.map (fun phase =>
    let copied := phase.blocks.map (fun words => SemiprimeD1JetBlockBits.readCopy words k)
    (copied.map (fun out => out.bits), (copied.toList.map (fun out => out.clock)).sum+5*copied.size+3))
  ⟨rows.map Prod.fst,(rows.toList.map Prod.snd).sum+5*rows.size+3⟩

/-- Finite scalar output and all component reports for one old coordinate. -/
structure CoordinateRun where
  /-- Canonical actual parent scalar-residue word. -/
  bits : List Bool
  /-- Producer/integer/physical recovery and coordinate-copy reports. -/
  clock : ℕ

/-- Execute one actual old-coordinate recovery, retaining repeated scalar
producer acquisition per coordinate rather than silently sharing it. -/
def recoverCoordinate (ctx : Context) (a M u P : ℕ) (phases : Array PhaseRun) (k : ℕ) : CoordinateRun :=
  let input := coordinate phases k
  let out := SemiprimeD1RecoveryFinishBits.run a M u ctx.precision P
    (fun t => (input.values[t]?).getD #[])
  ⟨out.bits,input.clock+SemiprimeD1RecoveryFinishBits.work out+7⟩

/-- The actual scalar recovery output is canonical at the ACTUAL parent precision. -/
theorem recoverCoordinate_good (ctx : Context) (a M u P : ℕ) (phases : Array PhaseRun) (k : ℕ) :
    SemiprimeSourceCompactBits.Compact (recoverCoordinate ctx a M u P phases k).bits ∧
      (recoverCoordinate ctx a M u P phases k).bits.length ≤ ctx.precision := by
  have h := SemiprimeD1RecoveryFinishBits.run_good a M u ctx.precision P
    (fun t => ((coordinate phases k).values[t]?).getD #[])
  exact ⟨h.2,h.1⟩

/-- One finite internal recursion phase. The continuation is wired to the
structural predecessor in `run`; it is never an external solver input. -/
def phase (next : Context → Network → JetRun) (ctx : Context) (net : Network)
    (a u : ℕ) (t : Fin (SemiprimeD1WireKernelOriginal.size a)) : PhaseRun :=
  let M := edgeCount net
  let geometry := SemiprimeD1RecoveryWeightRun.geometry a t.val
  let order := SemiprimeD1RecoveryScalarRun.orderFuel geometry.size geometry.point.natAbs
  let i := order.value
  if hi : i < a ∧ i < u ∧ geometry.point ≠ 0 then
    let index : Fin a := ⟨i,hi.1⟩
    let source := SemiprimeD1OriginalModeAcquisition.acquire net.leftCount net.rows.length 64
      a u i ctx.precision (SemiprimeD1TensorNetwork.arity net.rows) (SemiprimeD1TensorNetwork.owner net.rows)
    let height := SemiprimeD1ModeRate.jetHeight M u
    let q := height*(u-i)
    let fresh := SemiprimeD1FreshJetBits.acquireFresh ctx q source.precision
    let current : Context := ⟨q::ctx.axes,source.precision⟩
    let terms := source.modes.values.map (fun beta =>
      let children := (List.finRange 64).map (fun g =>
        let child := SemiprimeD1ChildNetwork.fromSource net source index g
          ctx [q] source.precision fresh t beta
        let answer := next current child.network
        (⟨answer.words,child.clock+answer.clock+5⟩ : JetRun))
      product current children)
    let total := SemiprimeD1JetAffineCoefficient.sumRuns current terms
    let blocks := (List.range q).map (fun j => SemiprimeD1JetBlockBits.extract ctx j total.words)
    ⟨(blocks.map (fun block => block.words)).toArray,source.precision,
      geometry.work+order.work+source.work+fresh.clock+total.clock+
        (blocks.map (fun block => block.clock)).sum+
        10*(M+a+u+i+q+source.modes.values.length+1)⟩
  else ⟨#[],0,geometry.work+order.work+a+u+i+8⟩

/-- The fixed recursive controller from finite literal data. Child solutions are
recursive calls of THIS function; no counter/entry/weight function is an input. -/
def run (s : ℕ) : ℕ → ℕ → Context → Network → JetRun
  | 0,_,ctx,net =>
    let leaf := SemiprimeD1TensorNetwork.leaf ctx net
    ⟨leaf.words,leaf.clock+5⟩
  | fuel+1,depth,ctx,net =>
    let lam := SemiprimeD1PackingReady.logarithm s
    let M := edgeCount net
    if activeTest s lam depth M then
      let a := SemiprimeD1Schedule.exponent lam depth
      let u := SemiprimeD1Schedule.levels lam depth
      let grid := SemiprimeD1RecoveryWeightRun.geometry a 0
      let phases := (List.finRange (SemiprimeD1WireKernelOriginal.size a)).map
        (phase (run s fuel (depth+1)) ctx net a u)
      let retained := phases.toArray
      let P := SemiprimeD1ModeRate.workingPrecision M u a 0 ctx.precision
      let outputs := (List.range ctx.rank).map (recoverCoordinate ctx a M u P retained)
      ⟨outputs.map (fun out => out.bits),(phases.map (fun out => out.clock)).sum+
        (outputs.map (fun out => out.clock)).sum+grid.work+
        20*(s+lam+depth+M+a+u+P+ctx.rank+phases.length+1)⟩
    else
      let leaf := SemiprimeD1TensorNetwork.leaf ctx net
      ⟨leaf.words,leaf.clock+s+lam+depth+M+8⟩

/-- Literal fuel-zero execution is the actual eager leaf counter. -/
theorem run_zero_words (s depth : ℕ) (ctx : Context) (net : Network) :
    (run s 0 depth ctx net).words = (SemiprimeD1TensorNetwork.leaf ctx net).words := rfl

/-- An actual failed schedule test executes the same concrete leaf counter. -/
theorem run_inactive_words (s fuel depth : ℕ) (ctx : Context) (net : Network)
    (h : activeTest s (SemiprimeD1PackingReady.logarithm s) depth (edgeCount net) = false) :
    (run s (fuel+1) depth ctx net).words = (SemiprimeD1TensorNetwork.leaf ctx net).words := by
  simp only [run,h,Bool.false_eq_true,ite_false]

/-- ALL executed branches derive the current dense shape and canonical scalar
word width. No recursive output Fits/canonicality advice is an input. -/
theorem run_good (s fuel depth : ℕ) (ctx : Context) (net : Network) :
    SemiprimeD1TensorTables.GoodWords ctx (run s fuel depth ctx net).words := by
  cases fuel with
  | zero => exact SemiprimeD1LeafCounterBounds.run_good (edgeCount net) ctx (vertices net)
  | succ fuel =>
    dsimp only [run]
    split
    · constructor
      · simp only [List.length_map,List.length_range]
      · intro w hw
        obtain ⟨output, ho, rfl⟩ := List.mem_map.mp hw
        obtain ⟨k, _, rfl⟩ := List.mem_map.mp ho
        exact recoverCoordinate_good ctx _ _ _ _ _ k
    · exact SemiprimeD1LeafCounterBounds.run_good (edgeCount net) ctx (vertices net)

end RiemannGaussian.SemiprimeD1RecursiveCounter
