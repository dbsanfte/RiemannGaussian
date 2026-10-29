/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryCoordinateResources
import RiemannGaussian.SemiprimeD1StackRecoveryCoordinateOriginalCaps
/-! # Actual per-coordinate source with exact old copied child-cache bytes
Only retained phase-block bytes and an actual binary coordinate enter runtime.
PhaseRun objects/continuations below specify source bytes and semantic caps in
proofs. A paid outer phase-bank logger/producer join remains upstream OPEN.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryCoordinateOriginal
open SemiprimeD1StackRecoveryCoordinate SemiprimeD1StackRecoveryCoordinateEncoding
open SemiprimeD1StackRecoveryCoordinateExecution SemiprimeD1StackRecoveryCoordinateBounds
open SemiprimeD1StackRecoveryCoordinateOriginalRows SemiprimeD1StackRecoveryCoordinateOriginalCaps
open SemiprimeD1StackRecoveryCoordinateSemanticCaps
open SemiprimeD1JetAxes SemiprimeD1TensorNetwork
/-- Literal output equals the exact old two-level coordinate-cache tape, including empty phases and EOF defaults. -/
theorem output_original (phases:Array N.PhaseRun) (key:List Bool):
    (done (originalPhases phases) key).data output=SemiprimeD1StackRecoveryEntriesEncoding.childTape
      (P.coordinateCache (N.coordinate phases (SemiprimeBitArithmetic.bitValue key))):=by
  rw [output_tape]
  exact result_original phases key
/-- Whole physical source acquires an old copied coordinate column from the actual phase-bank bytes and binary key ONLY. -/
theorem source_original (phases:Array N.PhaseRun) (key:List Bool):
    ∃q ≤runBound (originalPhases phases) key,
      SemiprimeD1StackCalls.run program q (initial (originalTape phases) key)=some (done (originalPhases phases) key) ∧
      (done (originalPhases phases) key).data output=SemiprimeD1StackRecoveryEntriesEncoding.childTape
        (P.coordinateCache (N.coordinate phases (SemiprimeBitArithmetic.bitValue key))):=by
  obtain ⟨q,hq,hr⟩:=source_run_bounded (originalPhases phases) key
  exact ⟨q,hq,hr,output_original phases key⟩
/-- Fixed coefficient and degree precede every actual phase-bank and coordinate input. -/
theorem uniform_source:∃coef degree:Nat,∀(phases:Phases) (key:List Bool),
    ∃q ≤coef*(resource phases key+1)^degree,
      SemiprimeD1StackCalls.run program q (initial (tape phases) key)=some (done phases key):=by
  exact ⟨1000000000000,4,source_run_bounded⟩
/-- SAMEactual source's original retained-phase own bound, using only original shape/working precision and physical key bytes. -/
theorem source_original_bounded (next:Context→Network→SemiprimeD1JetAffineCoefficient.JetRun)
    (ctx:Context) (net:Network) (a u:Nat) (hu:u ≤edgeCount net) (key:List Bool):
    ∃q ≤1000000000000*(bankByteBound (SemiprimeD1WireKernelOriginal.size a) (4*edgeCount net) ctx.rank
      (SemiprimeD1ModeRate.workingPrecision (edgeCount net) u a 0 ctx.precision)+key.length+1)^4,
      SemiprimeD1StackCalls.run program q (initial (originalTape (V.retained next ctx net a u)) key)=
        some (done (originalPhases (V.retained next ctx net a u)) key) ∧
      (done (originalPhases (V.retained next ctx net a u)) key).data output=
        SemiprimeD1StackRecoveryEntriesEncoding.childTape
          (P.coordinateCache (N.coordinate (V.retained next ctx net a u) (SemiprimeBitArithmetic.bitValue key))):=by
  obtain ⟨q,hq,hr,hout⟩:=source_original (V.retained next ctx net a u) key
  have hb:=original_bank_bytes next ctx net a u hu
  have hp:=Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.add_le_add_right hb key.length) 1) 4
  exact ⟨q,hq.trans (Nat.mul_le_mul_left 1000000000000 hp),hr,hout⟩
end RiemannGaussian.SemiprimeD1StackRecoveryCoordinateOriginal
