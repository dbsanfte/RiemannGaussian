/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RecoveryMetadataBudget
import RiemannGaussian.SemiprimeD1PhysicalRecursiveBounds

/-! # Closed actual coordinate recovery budget, including native stage reports
All original coefficient production, literal child-cache reads, physical scalar
arithmetic, native metadata and converted containers are retained. The aggregate
is a mixed report, not a complete primitive machine simulation.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace RiemannGaussian.SemiprimeD1PhysicalRecoveryLocalBudget
open SemiprimeD1JetAxes SemiprimeD1TensorNetwork SemiprimeD1RecursiveCounter
open SemiprimeD1RecursiveRecovery SemiprimeD1PhysicalRecursiveCounter
open SemiprimeD1PhysicalRecursiveBounds
open SemiprimeD1JetAffineCoefficient (JetRun)

/-- Actual finite array/list-conversion cells follow from derived cache shape. -/
theorem cache_cells (next : Context → Network → JetRun) (ctx : Context) (net : Network)
    (a u k : ℕ) (hu : u ≤ edgeCount net) :
    coordinateCacheCells (coordinate (retained next ctx net a u) k) ≤
      5*SemiprimeD1WireKernelOriginal.size a+
      5*(SemiprimeD1WireKernelOriginal.size a*(4*edgeCount net))+3 := by
  let input:=coordinate (retained next ctx net a u) k
  have hlen:=cache_length next ctx net a u k
  have hshape:=cache_shape next ctx net a u k hu
  have hs:=List.sum_le_length_nsmul ((coordinateCache input).map List.length)
    (4*edgeCount net) (by
      intro n hn
      obtain ⟨row,hr,rfl⟩:=List.mem_map.mp hn
      exact (hshape row hr).1)
  simp only [List.length_map,nsmul_eq_mul] at hs
  change (coordinateCache input).length=SemiprimeD1WireKernelOriginal.size a at hlen
  rw [hlen] at hs
  simp only [coordinateCache,List.length_map,Array.length_toList,List.map_map,Function.comp_def] at hs hlen
  simp only [Nat.cast_id] at hs
  change (input.values.toList.map Array.size).sum ≤
    SemiprimeD1WireKernelOriginal.size a*(4*edgeCount net) at hs
  simp only [coordinateCacheCells]
  change 5*input.values.size+5*(input.values.toList.map Array.size).sum+3 ≤ _
  omega

/-- Numeric original-parameter coordinate copy/source/recovery/control envelope. -/
def budget (a M p rank P : ℕ) : ℕ :=
  SemiprimeD1WireKernelOriginal.size a*(4*M*(3*rank+3*P+10)+8)+3+
  SemiprimeD1RecoveryPhysicalBounds.budget a M p P+
  SemiprimeD1RecoveryMetadataBudget.budget a M+
  (5*SemiprimeD1WireKernelOriginal.size a+5*(SemiprimeD1WireKernelOriginal.size a*(4*M))+3)+7

/-- Every report in the actual physical recursive coordinate call has a closed
original-dimensional cap. No metadata/source/coefficient/width/clock advice occurs. -/
theorem recoverCoordinate_clock (next : Context → Network → JetRun) (ctx : Context)
    (net : Network) (a u k : ℕ) (hu : u ≤ edgeCount net) :
    let P:=SemiprimeD1ModeRate.workingPrecision (edgeCount net) u a 0 ctx.precision
    (SemiprimeD1PhysicalRecursiveCounter.recoverCoordinate ctx a (edgeCount net) u P
      (retained next ctx net a u) k).clock ≤ budget a (edgeCount net) ctx.precision ctx.rank P := by
  have hc:=SemiprimeD1PhysicalRecursiveBounds.recoverCoordinate_clock next ctx net a u k hu
  have hi:=retained_coordinate_clock next ctx net a u k hu
  have hm:=SemiprimeD1RecoveryMetadataBudget.run_metadataWork a (edgeCount net) u ctx.precision
    (SemiprimeD1ModeRate.workingPrecision (edgeCount net) u a 0 ctx.precision)
    (coordinateCache (coordinate (retained next ctx net a u) k)) hu
  have hs:=cache_cells next ctx net a u k hu
  dsimp only at hc ⊢
  unfold budget
  omega

/-- All parent-coordinate recoveries repeat and retain their actual source
acquisition; the total uses the actual parent rank, without a sharing assumption. -/
theorem recoveries_clock (next : Context → Network → JetRun) (ctx : Context)
    (net : Network) (a u : ℕ) (hu : u ≤ edgeCount net) :
    let P:=SemiprimeD1ModeRate.workingPrecision (edgeCount net) u a 0 ctx.precision
    (((List.range ctx.rank).map
      (SemiprimeD1PhysicalRecursiveCounter.recoverCoordinate ctx a (edgeCount net) u P
        (retained next ctx net a u))).map CoordinateRun.clock).sum ≤
      ctx.rank*budget a (edgeCount net) ctx.precision ctx.rank P := by
  dsimp only
  have h:=List.sum_le_length_nsmul
    (((List.range ctx.rank).map
      (SemiprimeD1PhysicalRecursiveCounter.recoverCoordinate ctx a (edgeCount net) u
        (SemiprimeD1ModeRate.workingPrecision (edgeCount net) u a 0 ctx.precision)
        (retained next ctx net a u))).map CoordinateRun.clock)
    (budget a (edgeCount net) ctx.precision ctx.rank
      (SemiprimeD1ModeRate.workingPrecision (edgeCount net) u a 0 ctx.precision)) (by
      intro c hc
      obtain ⟨out,hout,rfl⟩:=List.mem_map.mp hc
      obtain ⟨k,hk,rfl⟩:=List.mem_map.mp hout
      exact recoverCoordinate_clock next ctx net a u k hu)
  simpa only [List.length_map,List.length_range,nsmul_eq_mul,Nat.cast_id] using h

end RiemannGaussian.SemiprimeD1PhysicalRecoveryLocalBudget
