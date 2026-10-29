/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RecursiveCounter
import RiemannGaussian.SemiprimeD1JetBlockBits

/-! # Original controller phase precision and physically retained block bounds
The maximum precision is computed at split0. Every phase's actual working
precision lies below it, and every physically extracted block has intrinsic
canonical current width. No child-word Fits answers are premises.
-/
set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace RiemannGaussian.SemiprimeD1RecursivePhaseBounds
open SemiprimeD1JetAxes SemiprimeD1TensorNetwork
open SemiprimeD1RecursiveCounter
open SemiprimeD1JetAffineCoefficient (JetRun)

/-- Physical accumulation derives full canonical shape at the current precision. -/
theorem sum_good (ctx : Context) (values : List JetRun) :
    SemiprimeD1TensorTables.GoodWords ctx (SemiprimeD1JetAffineCoefficient.sumRuns ctx values).words := by
  have h := SemiprimeD1JetAffineCoefficientBounds.sumRuns_good ctx values
  refine ⟨h.1,fun w hw => ⟨?_,h.2 w hw⟩⟩
  cases values with
  | nil =>
    have he : w = [] := (List.mem_replicate.mp hw).2
    subst w
    trivial
  | cons x xs => exact SemiprimeD1JetRingBits.add_compact _ _ _ w hw

/-- Computed actual original-source working precision uses the ACTUAL network scope. -/
theorem source_precision (net : Network) (a u i p : ℕ) :
    (SemiprimeD1OriginalModeAcquisition.acquire net.leftCount net.rows.length 64 a u i p
      (SemiprimeD1TensorNetwork.arity net.rows) (SemiprimeD1TensorNetwork.owner net.rows)).precision =
      SemiprimeD1ModeRate.workingPrecision (edgeCount net) u a i p := by
  rw [SemiprimeD1OriginalModeAcquisition.precision_original,SemiprimeD1TensorNetworkLayout.original_ports]
  rfl

/-- Split0 gives an unconditional common precision bound for every retained split. -/
theorem workingPrecision_le_zero (M u a i p : ℕ) :
    SemiprimeD1ModeRate.workingPrecision M u a i p ≤ SemiprimeD1ModeRate.workingPrecision M u a 0 p := by
  have hpow := Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) (Nat.sub_le a i)
  unfold SemiprimeD1ModeRate.workingPrecision
  simp only [Nat.sub_zero]
  nlinarith

/-- Every ACTUAL phase's precision is below the explicitly computed recovery width input. -/
theorem phase_precision_le (next : Context → Network → JetRun) (ctx : Context) (net : Network)
    (a u : ℕ) (t : Fin (SemiprimeD1WireKernelOriginal.size a)) :
    (phase next ctx net a u t).precision ≤
      SemiprimeD1ModeRate.workingPrecision (edgeCount net) u a 0 ctx.precision := by
  dsimp only [phase]
  split
  · rw [source_precision]
    exact workingPrecision_le_zero _ _ _ _ _
  · exact Nat.zero_le _

/-- Literal block extraction derives canonical old-coordinate vectors from the
actual current phase words, including all old coordinates. -/
theorem extract_blocks_good (ctx : Context) (q p : ℕ) (input : List (List Bool))
    (hw : SemiprimeD1TensorTables.GoodWords ⟨q::ctx.axes,p⟩ input) :
    ∀ block ∈ ((List.range q).map (fun j => (SemiprimeD1JetBlockBits.extract ctx j input).words)).toArray,
      SemiprimeD1TensorTables.GoodWords ⟨ctx.axes,p⟩ block := by
  intro block hb
  rw [List.mem_toArray] at hb
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hb
  exact ⟨SemiprimeD1JetBlockBits.extract_shape _ _ _,fun w hw' =>
    ⟨SemiprimeD1JetBlockBits.extract_compact _ _ _ (fun w h => (hw.2 w h).1) w hw',
      SemiprimeD1JetBlockBits.extract_bounded _ _ _ _ (fun w h => (hw.2 w h).2) w hw'⟩⟩

/-- ALL actual phase blocks have derived canonical shape/width, independently
of recursive-value correctness or a supplied intermediate precision envelope. -/
theorem phase_blocks_good (next : Context → Network → JetRun) (ctx : Context) (net : Network)
    (a u : ℕ) (t : Fin (SemiprimeD1WireKernelOriginal.size a)) :
    ∀ block ∈ (phase next ctx net a u t).blocks,
      SemiprimeD1TensorTables.GoodWords ⟨ctx.axes,(phase next ctx net a u t).precision⟩ block := by
  dsimp only [phase]
  split
  · dsimp only
    simp only [List.map_map,Function.comp_def]
    exact extract_blocks_good ctx _ _ _ (sum_good _ _)
  · intro block hb
    simp only [Array.not_mem_empty] at hb

/-- Every actually retained word fits the single COMPUTED original recovery precision cap. -/
theorem phase_word_bound (next : Context → Network → JetRun) (ctx : Context) (net : Network)
    (a u : ℕ) (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (block : List (List Bool))
    (hb : block ∈ (phase next ctx net a u t).blocks) (w : List Bool) (hw : w ∈ block) :
    w.length ≤ SemiprimeD1ModeRate.workingPrecision (edgeCount net) u a 0 ctx.precision :=
  ((phase_blocks_good next ctx net a u t block hb).2 w hw).2.trans (phase_precision_le next ctx net a u t)

/-- Coordinate acquisition consists of literal reads of the retained blocks;
the clock-bearing intermediate records do not alter the copied words. -/
theorem coordinate_values (phases : Array PhaseRun) (k : ℕ) :
    (coordinate phases k).values = phases.map (fun point =>
      point.blocks.map (fun words => (words[k]?).getD [])) := by
  simp only [coordinate,Array.map_map,Function.comp_def,
    SemiprimeD1JetBlockBits.readCopy_bits]

/-- Reading a missing block or coordinate returns the literal zero word. -/
theorem coordinate_read (phases : Array PhaseRun) (k t j : ℕ) :
    (((((coordinate phases k).values[t]?).getD #[])[j]?).getD []) =
      ((((((phases[t]?).getD emptyPhase).blocks[j]?).getD [])[k]?).getD []) := by
  rw [coordinate_values]
  simp only [Array.getElem?_map]
  cases ht : phases[t]? with
  | none => simp [emptyPhase]
  | some point =>
    simp only [Option.map_some,Option.getD_some,Array.getElem?_map]
    cases hj : point.blocks[j]? <;> simp

/-- Every copied coordinate word derives its width from its stored source
block, including out-of-range reads. -/
theorem coordinate_width (phases : Array PhaseRun) (k P : ℕ)
    (hp : ∀ point ∈ phases, ∀ block ∈ point.blocks, ∀ w ∈ block, w.length ≤ P) :
    ∀ row ∈ (coordinate phases k).values, ∀ w ∈ row, w.length ≤ P := by
  intro row hr w hw
  rw [coordinate_values] at hr
  obtain ⟨point,hpoint,rfl⟩ := Array.mem_map.mp hr
  obtain ⟨block,hblock,rfl⟩ := Array.mem_map.mp hw
  rw [← SemiprimeD1JetRingBits.read_bits]
  exact SemiprimeD1JetRingBounds.read_length block k P (hp point hpoint block hblock)

/-- The scalar recovery's TOTAL two-dimensional input accessor has a derived
word bound; no caller-supplied Fits answer is required. -/
theorem coordinate_word_bound (phases : Array PhaseRun) (k P : ℕ)
    (hp : ∀ point ∈ phases, ∀ block ∈ point.blocks, ∀ w ∈ block, w.length ≤ P)
    (t j : ℕ) :
    (((((coordinate phases k).values[t]?).getD #[])[j]?).getD []).length ≤ P := by
  cases ht : (coordinate phases k).values[t]? with
  | none => simp
  | some row =>
    cases hj : row[j]? with
    | none => simp [hj]
    | some w =>
      simpa only [ht,hj,Option.getD_some] using
        coordinate_width phases k P hp row (Array.mem_of_getElem? ht) w
          (Array.mem_of_getElem? hj)

/-- The actual retained original-grid array supplies the required recovery
word cap at every node/order, with split0 precision computed from the input. -/
theorem retained_word_bound (next : Context → Network → JetRun) (ctx : Context)
    (net : Network) (a u k t j : ℕ) :
    let retained := ((List.finRange (SemiprimeD1WireKernelOriginal.size a)).map
      (phase next ctx net a u)).toArray
    (((((coordinate retained k).values[t]?).getD #[])[j]?).getD []).length ≤
      SemiprimeD1ModeRate.workingPrecision (edgeCount net) u a 0 ctx.precision := by
  apply coordinate_word_bound
  intro point hp block hb w hw
  rw [List.mem_toArray] at hp
  obtain ⟨t,_,rfl⟩ := List.mem_map.mp hp
  exact phase_word_bound next ctx net a u t block hb w hw

/-- The EXECUTED scalar recovery from the actual phase arrays agrees with
maximal-content integer recovery. Its intermediate integer heights follow
from the original network and the derived stored-word cap above. -/
theorem recoverCoordinate_value (next : Context → Network → JetRun) (ctx : Context)
    (net : Network) (a u k : ℕ) (hu : u ≤ edgeCount net) :
    let retained := ((List.finRange (SemiprimeD1WireKernelOriginal.size a)).map
      (phase next ctx net a u)).toArray
    let P := SemiprimeD1ModeRate.workingPrecision (edgeCount net) u a 0 ctx.precision
    (SemiprimeBitArithmetic.bitValue
      (recoverCoordinate ctx a (edgeCount net) u P retained k).bits : ZMod (2^ctx.precision)) =
      SemiprimeD1IntegerRecoveryResidue.finish ctx.precision
        (SemiprimeD1IntegerRecovery.run a (edgeCount net) u
          (fun t => ((coordinate retained k).values[t]?).getD #[])) := by
  exact SemiprimeD1RecoveryFinishBits.run_value a (edgeCount net) u ctx.precision _ hu _
    (retained_word_bound next ctx net a u k)

end RiemannGaussian.SemiprimeD1RecursivePhaseBounds
