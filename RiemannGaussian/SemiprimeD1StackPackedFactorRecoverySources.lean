/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryPrimitives
/-! # The two whole actual frozen source calls in factor recovery -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPackedFactorRecoverySources
open SemiprimeD1StackPackedFactorRecovery SemiprimeD1StackPackedFactorRecoveryEncoding
open SemiprimeD1StackPackedFactorRecoveryPrimitives SemiprimeD1StackProcedureTrace
/-- Whole real readout acquires both moments while preserving every other physical word. -/
theorem readout_call (bits scalar : List Bool) (s : S.Stack→List Bool) (u : Aux→List Bool) :
    ∃t ≤ SemiprimeD1StackPackedMomentReadoutCost.polynomial bits scalar+1,
      Runs program t (ctl .start) (bank (R.input bits scalar) s u) (ctl (.copy .count))
        (bank (SemiprimeD1StackPackedMomentReadoutEncoding.result bits scalar) s u) := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackPackedMomentReadoutCost.source_run_bounded bits scalar
  let before:=bank (R.input bits scalar) s u
  let after:=bank (SemiprimeD1StackPackedMomentReadoutEncoding.result bits scalar) s u
  have hi : Link.DataRel readout before (SemiprimeD1StackPackedMomentReadout.initial bits scalar).data before :=
    ⟨fun _=>rfl,fun _ _=>rfl⟩
  have ho : Link.DataRel readout before (SemiprimeD1StackPackedMomentReadoutEncoding.done bits scalar).data after := by
    constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k|k
      · exact False.elim (hk k rfl)
      · rfl
      · rfl
  exact ⟨t+1,by omega,SemiprimeD1StackProcedureCallsTrace.included_call program readout readoutLabel readout_injective
    R.program (SemiprimeD1StackPackedMomentReadout.ctl .start) (fun _=>rfl)
    (ctl .start) (ctl (.copy .count)) rfl t
    (SemiprimeD1StackPackedMomentReadout.initial bits scalar) (SemiprimeD1StackPackedMomentReadoutEncoding.done bits scalar)
    before after rfl rfl rfl rfl hr hi ho⟩
/-- The ENTIRE actual binary-square-root source runs on the physically acquired binary D. -/
theorem squareRoot_call (d : List Bool) (r : R.Stack→List Bool) (u : Aux→List Bool) :
    ∃t ≤ 100000000*(d.length+1)^4+1,
      Runs program t (ctl .root) (bank r (S.input d) u) (ctl (.copy .minusLeft))
        (bank r (SemiprimeD1StackBinarySquareRootEncoding.result d) u) := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackBinarySquareRootExecution.source_run_bounded d
  change t ≤ 100000000*(d.length+1)^4 at ht
  let before:=bank r (S.input d) u
  let after:=bank r (SemiprimeD1StackBinarySquareRootEncoding.result d) u
  have hi : Link.DataRel squareRoot before (SemiprimeD1StackBinarySquareRoot.initial d).data before :=
    ⟨fun _=>rfl,fun _ _=>rfl⟩
  have ho : Link.DataRel squareRoot before (SemiprimeD1StackBinarySquareRootEncoding.done d).data after := by
    constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k|k
      · rfl
      · exact False.elim (hk k rfl)
      · rfl
  exact ⟨t+1,by omega,SemiprimeD1StackProcedureCallsTrace.included_call program squareRoot squareRootLabel squareRoot_injective
    S.program (SemiprimeD1StackBinarySquareRoot.ctl .start) (fun _=>rfl)
    (ctl .root) (ctl (.copy .minusLeft)) rfl t
    (SemiprimeD1StackBinarySquareRoot.initial d) (SemiprimeD1StackBinarySquareRootEncoding.done d)
    before after rfl rfl rfl rfl hr hi ho⟩
end RiemannGaussian.SemiprimeD1StackPackedFactorRecoverySources
