/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PhysicalRecursiveCorrectness

/-! # Derived actual phase shapes and physical local recovery report
The scalar producer/bit arithmetic bound is numeric in original dimensions.
Native typed/source metadata is explicitly retained alongside this report;
no total primitive-machine or complete recursion-tree rate is claimed here.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace RiemannGaussian.SemiprimeD1PhysicalRecursiveBounds
open SemiprimeD1JetAxes SemiprimeD1TensorNetwork SemiprimeD1RecursiveCounter
open SemiprimeD1RecursiveRecovery SemiprimeD1PhysicalRecursiveCounter
open SemiprimeD1PhysicalRecursiveCorrectness
open SemiprimeD1JetAffineCoefficient (JetRun)
attribute [local irreducible] SemiprimeD1OriginalModeAcquisition.acquire

/-- Every actual phase has at most 4M retained blocks, including inactive phases. -/
theorem phase_blocks_size (next : Context → Network → JetRun) (ctx : Context)
    (net : Network) (a u : ℕ) (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (hu : u ≤ edgeCount net) :
    (phase next ctx net a u t).blocks.size ≤ 4*edgeCount net := by
  have hh:=SemiprimeD1ModeRate.jetHeight_mul_le (edgeCount net) u hu
  dsimp only [phase]
  split
  · simp only [List.size_toArray,List.length_map,List.length_range]
    exact (Nat.mul_le_mul_left _ (Nat.sub_le _ _)).trans hh
  · simp

/-- Actual copied coordinate storage has exactly one row per original grid node. -/
theorem cache_length (next : Context → Network → JetRun) (ctx : Context) (net : Network)
    (a u k : ℕ) :
    (coordinateCache (coordinate (retained next ctx net a u) k)).length=
      SemiprimeD1WireKernelOriginal.size a := by
  simp only [coordinateCache,List.length_map,Array.length_toList,
    SemiprimeD1RecursivePhaseBounds.coordinate_values,Array.size_map,retained,
    List.size_toArray,List.length_map,List.length_finRange]

/-- Every actual literal child row has at most 4M words, each bounded by the
computed split-zero phase precision. All caps follow from actual phase creation. -/
theorem cache_shape (next : Context → Network → JetRun) (ctx : Context) (net : Network)
    (a u k : ℕ) (hu : u ≤ edgeCount net) :
    ∀ row ∈ coordinateCache (coordinate (retained next ctx net a u) k),
      row.length ≤ 4*edgeCount net ∧ ∀ w ∈ row, w.length ≤
        SemiprimeD1ModeRate.workingPrecision (edgeCount net) u a 0 ctx.precision := by
  intro row hr
  refine ⟨?_,cache_width next ctx net a u k row hr⟩
  obtain ⟨source,hs,rfl⟩:=List.mem_map.mp hr
  rw [SemiprimeD1RecursivePhaseBounds.coordinate_values] at hs
  obtain ⟨point,hp,rfl⟩:=Array.mem_map.mp (show source ∈ _ by simpa using hs)
  rw [retained,List.mem_toArray] at hp
  obtain ⟨t,_,rfl⟩:=List.mem_map.mp hp
  simp only [Array.length_toList,Array.size_map]
  exact phase_blocks_size next ctx net a u t hu

/-- The exact physical scalar recovery subcall made by the actual recursive
coordinate pipeline has an original-parameter clock, with no height/Fits advice. -/
theorem local_recovery_clock (next : Context → Network → JetRun) (ctx : Context)
    (net : Network) (a u k : ℕ) (hu : u ≤ edgeCount net) :
    let P:=SemiprimeD1ModeRate.workingPrecision (edgeCount net) u a 0 ctx.precision
    (SemiprimeD1RecoveryPhysicalRun.run a (edgeCount net) u ctx.precision P
      (coordinateCache (coordinate (retained next ctx net a u) k))).clock ≤
      SemiprimeD1RecoveryPhysicalBounds.budget a (edgeCount net) ctx.precision P := by
  dsimp only
  exact SemiprimeD1RecoveryPhysicalBounds.run_clock a (edgeCount net) u ctx.precision _ _ hu
    (cache_length next ctx net a u k).le (cache_shape next ctx net a u k hu)

/-- Coordinate conversion retains its source copy report and the full physical
recovery report, and explicitly retains the separate native metadata ledger. -/
theorem recoverCoordinate_clock (next : Context → Network → JetRun) (ctx : Context)
    (net : Network) (a u k : ℕ) (hu : u ≤ edgeCount net) :
    let P:=SemiprimeD1ModeRate.workingPrecision (edgeCount net) u a 0 ctx.precision
    let input:=coordinate (retained next ctx net a u) k
    (SemiprimeD1PhysicalRecursiveCounter.recoverCoordinate ctx a (edgeCount net) u P
      (retained next ctx net a u) k).clock ≤
      input.clock+SemiprimeD1RecoveryPhysicalBounds.budget a (edgeCount net) ctx.precision P+
      (SemiprimeD1RecoveryPhysicalRun.run a (edgeCount net) u ctx.precision P
        (coordinateCache input)).metadataWork+coordinateCacheCells input+7 := by
  have h:=local_recovery_clock next ctx net a u k hu
  dsimp only [SemiprimeD1PhysicalRecursiveCounter.recoverCoordinate]
  exact Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.add_le_add_right (Nat.add_le_add_left h _) _) _) _

/-- The actual active test derives the only taper-size guard used by local recovery. -/
theorem active_local_recovery_clock (s depth : ℕ) (ctx : Context) (net : Network)
    (next : Context → Network → JetRun) (k : ℕ)
    (ha : activeTest s (SemiprimeD1PackingReady.logarithm s) depth (edgeCount net)=true) :
    let a:=SemiprimeD1Schedule.exponent (SemiprimeD1PackingReady.logarithm s) depth
    let u:=SemiprimeD1Schedule.levels (SemiprimeD1PackingReady.logarithm s) depth
    let P:=SemiprimeD1ModeRate.workingPrecision (edgeCount net) u a 0 ctx.precision
    (SemiprimeD1RecoveryPhysicalRun.run a (edgeCount net) u ctx.precision P
      (coordinateCache (coordinate (retained next ctx net a u) k))).clock ≤
      SemiprimeD1RecoveryPhysicalBounds.budget a (edgeCount net) ctx.precision P :=
  local_recovery_clock next ctx net _ _ k
    ((activeTest_correct _ _ _ _).mp ha).2.2

/-- Generic actual coordinate read/copy report from literal stored-block shape.
The original phase theorem below discharges these internal shape facts. -/
theorem coordinate_clock (phases : Array PhaseRun) (k rank P m : ℕ)
    (hp : ∀ point ∈ phases, point.blocks.size ≤ m ∧
      ∀ block ∈ point.blocks, block.length=rank ∧ ∀ w ∈ block, w.length ≤ P) :
    (coordinate phases k).clock ≤ phases.size*(m*(3*rank+3*P+10)+8)+3 := by
  let cost : PhaseRun → ℕ := fun point =>
    (((point.blocks.map (fun words => SemiprimeD1JetBlockBits.readCopy words k)).toList.map
      (fun out => out.clock)).sum+5*point.blocks.size+3)
  have hc : ∀ point ∈ phases, cost point ≤ m*(3*rank+3*P+10)+3 := by
    intro point hpoint
    have hshape:=hp point hpoint
    have hs:=List.sum_le_length_nsmul
      ((point.blocks.map (fun words => SemiprimeD1JetBlockBits.readCopy words k)).toList.map
        (fun out => out.clock)) (3*rank+3*P+5) (by
          intro c hc
          obtain ⟨out,hout,rfl⟩:=List.mem_map.mp hc
          obtain ⟨block,hblock,rfl⟩:=Array.mem_map.mp (show out ∈ _ by simpa using hout)
          have h:=SemiprimeD1JetBlockBits.readCopy_clock block k P (hshape.2 block hblock).2
          simpa only [(hshape.2 block hblock).1] using h)
    simp only [List.length_map,Array.length_toList,Array.size_map,nsmul_eq_mul] at hs
    have hm:=Nat.mul_le_mul_right (3*rank+3*P+10) hshape.1
    dsimp only [cost]
    nlinarith only [hs,hm]
  have hs:=List.sum_le_length_nsmul (phases.toList.map cost)
    (m*(3*rank+3*P+10)+3) (by
      intro c hc'
      obtain ⟨point,hpoint,rfl⟩:=List.mem_map.mp hc'
      exact hc point (by simpa using hpoint))
  simp only [List.length_map,Array.length_toList,nsmul_eq_mul] at hs
  have he : (coordinate phases k).clock=(phases.toList.map cost).sum+5*phases.size+3 := by
    simp only [coordinate,Array.size_map,Array.toList_map,List.map_map,Function.comp_def,cost]
  rw [he]
  nlinarith only [hs]

/-- Every copied coordinate read derives its complete physical payload clock
from the actual original grid, retained block count, rank and split-zero precision. -/
theorem retained_coordinate_clock (next : Context → Network → JetRun) (ctx : Context)
    (net : Network) (a u k : ℕ) (hu : u ≤ edgeCount net) :
    (coordinate (retained next ctx net a u) k).clock ≤
      SemiprimeD1WireKernelOriginal.size a*
        (4*edgeCount net*(3*ctx.rank+
          3*SemiprimeD1ModeRate.workingPrecision (edgeCount net) u a 0 ctx.precision+10)+8)+3 := by
  have h:=coordinate_clock (retained next ctx net a u) k ctx.rank
    (SemiprimeD1ModeRate.workingPrecision (edgeCount net) u a 0 ctx.precision)
    (4*edgeCount net) (by
      intro point hp
      rw [retained,List.mem_toArray] at hp
      obtain ⟨t,_,rfl⟩:=List.mem_map.mp hp
      refine ⟨phase_blocks_size next ctx net a u t hu,?_⟩
      intro block hb
      exact ⟨(SemiprimeD1RecursivePhaseBounds.phase_blocks_good next ctx net a u t block hb).1,
        fun w hw => SemiprimeD1RecursivePhaseBounds.phase_word_bound next ctx net a u t block hb w hw⟩)
  simpa only [retained,List.size_toArray,List.length_map,List.length_finRange] using h

end RiemannGaussian.SemiprimeD1PhysicalRecursiveBounds
