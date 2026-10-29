/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PhysicalRecursiveCounter

/-! # Original network correctness of the closed physical-recovery recursion -/
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace RiemannGaussian.SemiprimeD1PhysicalRecursiveCorrectness
open SemiprimeD1JetAxes SemiprimeD1TensorNetwork SemiprimeD1JetInterpretation
open SemiprimeD1RecursiveCounter SemiprimeD1RecursiveRecovery
open SemiprimeD1PhysicalRecursiveCounter
open SemiprimeD1JetAffineCoefficient (JetRun)

/-- Literal array-to-list conversion preserves the exact original total child accessor. -/
theorem cache_childView (input : CoordinateData) (t : ℕ) :
    SemiprimeD1RecoveryPhysicalRun.childView (coordinateCache input) t=
      (input.values[t]?).getD #[] := by
  simp only [SemiprimeD1RecoveryPhysicalRun.childView,coordinateCache,List.getElem?_map,
    Array.getElem?_toList]
  cases h:input.values[t]? <;> simp

/-- Every actual literal cache word has the computed original phase precision cap. -/
theorem cache_width (next : Context → Network → JetRun) (ctx : Context) (net : Network)
    (a u k : ℕ) :
    ∀ row ∈ coordinateCache (coordinate (retained next ctx net a u) k),
      ∀ w ∈ row, w.length ≤
        SemiprimeD1ModeRate.workingPrecision (edgeCount net) u a 0 ctx.precision := by
  intro row hr w hw
  obtain ⟨source,hs,rfl⟩:=List.mem_map.mp hr
  apply SemiprimeD1RecursivePhaseBounds.coordinate_width (retained next ctx net a u) k _ _
    source (by simpa using hs) w (by simpa using hw)
  intro point hp block hb word hword
  rw [retained,List.mem_toArray] at hp
  obtain ⟨t,_,rfl⟩:=List.mem_map.mp hp
  exact SemiprimeD1RecursivePhaseBounds.phase_word_bound next ctx net a u t block hb word hword

/-- On the actual retained phase array the new physical scalar pipeline has
exactly the native recovery residue, with all child caps derived internally. -/
theorem recoverCoordinate_residue (next : Context → Network → JetRun) (ctx : Context)
    (net : Network) (a u k : ℕ) (hu : u ≤ edgeCount net) :
    let P:=SemiprimeD1ModeRate.workingPrecision (edgeCount net) u a 0 ctx.precision
    (SemiprimeBitArithmetic.bitValue
      (SemiprimeD1PhysicalRecursiveCounter.recoverCoordinate ctx a (edgeCount net) u P
        (retained next ctx net a u) k).bits:ZMod (2^ctx.precision))=
    (SemiprimeBitArithmetic.bitValue
      (SemiprimeD1RecursiveCounter.recoverCoordinate ctx a (edgeCount net) u P
        (retained next ctx net a u) k).bits:ZMod (2^ctx.precision)) := by
  dsimp only
  have hp:=SemiprimeD1RecoveryPhysicalRun.run_value a (edgeCount net) u ctx.precision
    (SemiprimeD1ModeRate.workingPrecision (edgeCount net) u a 0 ctx.precision)
    (coordinateCache (coordinate (retained next ctx net a u) k)) hu
    (cache_width next ctx net a u k)
  have hc : SemiprimeD1RecoveryPhysicalRun.childView
      (coordinateCache (coordinate (retained next ctx net a u) k))=
      (fun t => ((coordinate (retained next ctx net a u) k).values[t]?).getD #[]) := by
    funext t
    exact cache_childView _ t
  rw [hc] at hp
  exact hp.trans (SemiprimeD1RecursivePhaseBounds.recoverCoordinate_value next ctx net a u k hu).symm

/-- Intrinsic compactness and precision bounds upgrade residue equality to
literal byte equality for the actual physical coordinate replacement. -/
theorem recoverCoordinate_eq_native (next : Context → Network → JetRun) (ctx : Context)
    (net : Network) (a u k : ℕ) (hu : u ≤ edgeCount net) :
    let P:=SemiprimeD1ModeRate.workingPrecision (edgeCount net) u a 0 ctx.precision
    (SemiprimeD1PhysicalRecursiveCounter.recoverCoordinate ctx a (edgeCount net) u P
      (retained next ctx net a u) k).bits=
    (SemiprimeD1RecursiveCounter.recoverCoordinate ctx a (edgeCount net) u P
      (retained next ctx net a u) k).bits := by
  dsimp only
  let P:=SemiprimeD1ModeRate.workingPrecision (edgeCount net) u a 0 ctx.precision
  let x:=SemiprimeD1PhysicalRecursiveCounter.recoverCoordinate ctx a (edgeCount net) u P
    (retained next ctx net a u) k
  let y:=SemiprimeD1RecursiveCounter.recoverCoordinate ctx a (edgeCount net) u P
    (retained next ctx net a u) k
  have hx:=SemiprimeD1PhysicalRecursiveCounter.recoverCoordinate_good ctx a (edgeCount net) u P
    (retained next ctx net a u) k
  have hy:=SemiprimeD1RecursiveCounter.recoverCoordinate_good ctx a (edgeCount net) u P
    (retained next ctx net a u) k
  have hxl : SemiprimeBitArithmetic.bitValue x.bits < 2^ctx.precision :=
    (SemiprimeBitArithmetic.bitValue_lt_width x.bits).trans_le
      (Nat.pow_le_pow_right (by omega) hx.2)
  have hyl : SemiprimeBitArithmetic.bitValue y.bits < 2^ctx.precision :=
    (SemiprimeBitArithmetic.bitValue_lt_width y.bits).trans_le
      (Nat.pow_le_pow_right (by omega) hy.2)
  let _ : NeZero (2^ctx.precision) := ⟨by positivity⟩
  have hv:=congrArg (fun z:ZMod (2^ctx.precision) => z.val)
    (recoverCoordinate_residue next ctx net a u k hu)
  have he : SemiprimeBitArithmetic.bitValue x.bits=SemiprimeBitArithmetic.bitValue y.bits := by
    simp only [ZMod.val_natCast] at hv
    change SemiprimeBitArithmetic.bitValue x.bits % 2^ctx.precision=
      SemiprimeBitArithmetic.bitValue y.bits % 2^ctx.precision at hv
    simpa only [Nat.mod_eq_of_lt hxl,Nat.mod_eq_of_lt hyl] using hv
  exact SemiprimeSourceCompactWordIds.compact_value_injective x.bits y.bits hx.1 hy.1 he

/-- The actual closed physical-recovery recursion returns the original network
contraction; the phase continuation is this very run's structural predecessor. -/
theorem run_correct (s fuel depth : ℕ) (ctx : Context) (net : Network)
    (hpos : ctx.Positive) (hw : WellFormed net) (hg : Good ctx net) :
    interpret ctx (SemiprimeD1PhysicalRecursiveCounter.run s fuel depth ctx net).words=
      interpret ctx (leaf ctx net).words := by
  induction fuel generalizing depth ctx net with
  | zero => rfl
  | succ fuel ih =>
    by_cases ha : activeTest s (SemiprimeD1PackingReady.logarithm s) depth (edgeCount net)=true
    · have guards:=SemiprimeD1RecursiveRecoveryRun.active_recovery_guards s depth net ha
      let a:=SemiprimeD1Schedule.exponent (SemiprimeD1PackingReady.logarithm s) depth
      let u:=SemiprimeD1Schedule.levels (SemiprimeD1PackingReady.logarithm s) depth
      let next:=SemiprimeD1PhysicalRecursiveCounter.run s fuel (depth+1)
      have hp:=SemiprimeD1RecursiveCorrectness.phase_correct next ctx net a u hpos hw hg
        guards.2.2 (fun c child hc hwc hgc => ih (depth+1) c child hc hwc hgc)
      have hwords : (SemiprimeD1PhysicalRecursiveCounter.run s (fuel+1) depth ctx net).words=
          (List.range ctx.rank).map (fun k =>
            (SemiprimeD1RecursiveCounter.recoverCoordinate ctx a (edgeCount net) u
              (SemiprimeD1ModeRate.workingPrecision (edgeCount net) u a 0 ctx.precision)
              (retained next ctx net a u) k).bits) := by
        rw [SemiprimeD1PhysicalRecursiveCounter.run,ite_eq_left ha]
        simp only [List.map_map,Function.comp_def]
        apply List.map_congr_left
        intro k hk
        exact recoverCoordinate_eq_native next ctx net a u k guards.2.1
      rw [hwords]
      exact SemiprimeD1RecursiveRecoveryRun.recovery_words_correct next ctx net a u
        hpos guards.1 guards.2.1 guards.2.2 hp
    · simp only [SemiprimeD1PhysicalRecursiveCounter.run,Bool.eq_false_of_not_eq_true ha,
        Bool.false_eq_true,ite_false]

/-- Canonical physical output equals the eager leaf literally, not just in the quotient. -/
theorem run_words_eq_leaf (s fuel depth : ℕ) (ctx : Context) (net : Network)
    (hpos : ctx.Positive) (hw : WellFormed net) (hg : Good ctx net) :
    (SemiprimeD1PhysicalRecursiveCounter.run s fuel depth ctx net).words=(leaf ctx net).words := by
  have hr:=SemiprimeD1PhysicalRecursiveCounter.run_good s fuel depth ctx net
  have hl:=SemiprimeD1LeafCounterBounds.run_good (edgeCount net) ctx (vertices net)
  exact interpret_injective ctx _ _ hpos hr.1 hl.1
    (fun w hw => (hr.2 w hw).1) (fun w hw => (hl.2 w hw).1)
    (fun w hw => (hr.2 w hw).2) (fun w hw => (hl.2 w hw).2)
    (run_correct s fuel depth ctx net hpos hw hg)

/-- The new actual recursion is byte-equal to the frozen original counter,
without asserting any equality between the two report clocks. -/
theorem run_words_eq_original (s fuel depth : ℕ) (ctx : Context) (net : Network)
    (hpos : ctx.Positive) (hw : WellFormed net) (hg : Good ctx net) :
    (SemiprimeD1PhysicalRecursiveCounter.run s fuel depth ctx net).words=
      (SemiprimeD1RecursiveCounter.run s fuel depth ctx net).words :=
  (run_words_eq_leaf s fuel depth ctx net hpos hw hg).trans
    (SemiprimeD1RecursiveCorrectness.run_words_eq_leaf s fuel depth ctx net hpos hw hg).symm

end RiemannGaussian.SemiprimeD1PhysicalRecursiveCorrectness
