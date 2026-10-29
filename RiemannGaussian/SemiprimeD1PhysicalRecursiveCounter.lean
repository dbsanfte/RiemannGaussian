/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RecoveryPhysicalBounds
import RiemannGaussian.SemiprimeD1RecursiveCorrectness

/-! # Closed recursive counter with original physical scalar recovery
The structural continuation belongs to this new run. The frozen actual phase
constructs literal child arrays, and recovery consumes their literal copied data.
Physical and native metadata reports are both retained; the aggregate is not a
whole primitive-machine clock until the remaining host/memory lowering is joined.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace RiemannGaussian.SemiprimeD1PhysicalRecursiveCounter
open SemiprimeD1JetAxes SemiprimeD1TensorNetwork
open SemiprimeD1RecursiveCounter
open SemiprimeD1JetAffineCoefficient (JetRun)

/-- Literal copied child-coordinate data; no semantic getter is executed. -/
def coordinateCache (input : CoordinateData) : List (List (List Bool)) :=
  input.values.toList.map Array.toList

/-- Finite container cells for conversion of the already physically copied input. -/
def coordinateCacheCells (input : CoordinateData) : ℕ :=
  5*input.values.size+5*(input.values.toList.map Array.size).sum+3

/-- Execute original physical row production and scalar recovery on the actual
coordinate cache, retaining every source, copy, physical and native-stage report. -/
def recoverCoordinate (ctx : Context) (a M u P : ℕ) (phases : Array PhaseRun)
    (k : ℕ) : CoordinateRun :=
  let input:=coordinate phases k
  let out:=SemiprimeD1RecoveryPhysicalRun.run a M u ctx.precision P (coordinateCache input)
  ⟨out.bits,input.clock+out.clock+out.metadataWork+coordinateCacheCells input+7⟩

/-- Every physical scalar output is intrinsically canonical at parent precision. -/
theorem recoverCoordinate_good (ctx : Context) (a M u P : ℕ) (phases : Array PhaseRun)
    (k : ℕ) :
    SemiprimeSourceCompactBits.Compact (recoverCoordinate ctx a M u P phases k).bits ∧
      (recoverCoordinate ctx a M u P phases k).bits.length ≤ ctx.precision := by
  have h:=SemiprimeD1RecoveryPhysicalBounds.run_good a M u ctx.precision P
    (coordinateCache (coordinate phases k))
  exact ⟨h.2,h.1⟩

/-- Structural recursion uses this function's own predecessor and literal data. -/
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

/-- All branches derive current dense shape and canonical scalar output. -/
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
        obtain ⟨output,ho,rfl⟩:=List.mem_map.mp hw
        obtain ⟨k,_,rfl⟩:=List.mem_map.mp ho
        exact recoverCoordinate_good ctx _ _ _ _ _ k
    · exact SemiprimeD1LeafCounterBounds.run_good (edgeCount net) ctx (vertices net)

end RiemannGaussian.SemiprimeD1PhysicalRecursiveCounter
