/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackTransformExecution
import RiemannGaussian.SemiprimeD1BinaryBootstrapPublic

/-! # Original-input physical transform/radix resources and public meaning
All prefix memory is bounded from actual source/target transitions and its
proved halt. Canonical input connects the acquired small counters to the SAME
existing public parameters; no machine claim for remaining graph constructors.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackTransformBounds
open SemiprimeD1StackTransform SemiprimeD1StackTransformComponents
open SemiprimeD1StackTransformExecution SemiprimeD1StackTransformArithmetic
open SemiprimeMacroParameters SemiprimeBitArithmetic

/-- Each actual reached data stack is bounded from the original binary input and executed steps. -/
theorem prefix_data_bound (bits:List Bool) (fuel:ℕ) (out:C.State Stack Label)
    (hr:C.run program fuel (initial bits)=some out) :
    ∀k,(out.data k).length≤bits.length+fuel := by
  apply SemiprimeD1StackReturnLink.run_data_bound program fuel bits.length _ out ?_ hr
  intro k
  cases k <;> simp [initial,input]

/-- A proved halt cannot be followed by a successful extra execution. -/
theorem run_halted (n:ℕ) (state:C.State Stack Label) (hpc:state.pc=none) :
    C.run program (n+1) state=none := by
  unfold C.run
  rw [Function.iterate_succ_apply]
  have hs:C.step program state=none:=by simp [C.step,SemiprimeD1StackCalls.step,hpc]
  simp only [Option.bind_some,hs]
  exact Function.iterate_fixed rfl n

/-- Successful prefixes are bounded by the actual original-input halt, not an advised clock. -/
theorem fuel_le_halt (time fuel:ℕ) (state finish out:C.State Stack Label)
    (hh:C.run program time state=some finish) (hp:finish.pc=none)
    (hr:C.run program fuel state=some out) : fuel≤time := by
  by_contra h
  have ht:fuel=time+((fuel-time-1)+1):=by omega
  rw [ht,SemiprimeD1StackReturnLink.run_add,hh,Option.bind_some,run_halted _ finish hp] at hr
  cases hr

/-- Pure fixed-polynomial storage substitution for the actual transition cap. -/
theorem numeric_space_bound (n:ℕ) :
    12*(n+120000*(n+1)^2)≤1500000*(n+1)^2 := by nlinarith

/-- ALL reached machine prefixes include every Boolean tally/temporary and real return frame. -/
theorem machine_space (bits:List Bool) (fuel:ℕ) (cfg:machine.Cfg)
    (hr:(fun cfg=>cfg.bind machine.step)^[fuel] (some (Turing.initList machine bits))=some cfg) :
    (cfg.stk (some Stack.input)).length+(cfg.stk (some Stack.width)).length+
      (cfg.stk (some Stack.nonzero)).length+(cfg.stk (some Stack.threshold)).length+
      (cfg.stk (some Stack.radius)).length+(cfg.stk (some Stack.square)).length+
      (cfg.stk (some Stack.exponent)).length+(cfg.stk (some Stack.squareWork)).length+
      (cfg.stk (some Stack.thresholdWork)).length+(cfg.stk (some Stack.temporary)).length+
      (cfg.stk (some Stack.radix)).length+(cfg.stk none).length≤1500000*(bits.length+1)^2 := by
  rw [initial_eq] at hr
  let state:=initial bits
  change (fun cfg=>cfg.bind machine.step)^[fuel]
    (some (SemiprimeD1StackCalls.configuration state))=some cfg at hr
  have he:=SemiprimeD1StackCalls.run_correct Stack.input Stack.radix (.inl .start) program fuel state
  change (C.run program fuel state).map SemiprimeD1StackCalls.configuration=
    (fun cfg=>cfg.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration state)) at he
  cases hc:C.run program fuel state with
  | none => rw [hc,hr] at he;cases he
  | some out =>
    rw [hc,hr] at he
    have hcfg:SemiprimeD1StackCalls.configuration out=cfg:=Option.some.inj he
    rw [←hcfg]
    have hfuel:=fuel_le_halt (totalTime bits.length) fuel state (done bits) out (acquire_run bits) rfl hc
    have htime:=totalTime_le bits.length
    have h:=prefix_data_bound bits fuel out hc
    have h0:=h .input
    have h1:=h .width
    have h2:=h .nonzero
    have h3:=h .threshold
    have h4:=h .radius
    have h5:=h .square
    have h6:=h .exponent
    have h7:=h .squareWork
    have h8:=h .thresholdWork
    have h9:=h .temporary
    have h10:=h .radix
    have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel state out hc
    change out.frames.length≤0+fuel at hf
    change (out.data .input).length+(out.data .width).length+(out.data .nonzero).length+
      (out.data .threshold).length+(out.data .radius).length+(out.data .square).length+
      (out.data .exponent).length+(out.data .squareWork).length+(out.data .thresholdWork).length+
      (out.data .temporary).length+(out.data .radix).length+out.frames.length≤_
    have hsum:(out.data .input).length+(out.data .width).length+(out.data .nonzero).length+
      (out.data .threshold).length+(out.data .radius).length+(out.data .square).length+
      (out.data .exponent).length+(out.data .squareWork).length+(out.data .thresholdWork).length+
      (out.data .temporary).length+(out.data .radix).length+out.frames.length≤12*(bits.length+fuel):=by omega
    exact hsum.trans ((Nat.mul_le_mul_left 12 (Nat.add_le_add_left (hfuel.trans htime) bits.length)).trans
      (numeric_space_bound bits.length))

/-- Actual completed output retains the original N and exact original-frontdoor zero test. -/
theorem input_preserved (bits:List Bool) :
    (result bits) .input=bits ∧
      (result bits) .nonzero=[(SemiprimeBitDivision.nonzeroBits bits).nonzero] := by
  exact ⟨rfl,congrArg List.singleton (SemiprimeD1BinaryBootstrap.seenOne_eq_nonzeroBits bits)⟩

/-- Every completed counter is the exact intended parameter of the physically acquired WIDTH. -/
theorem acquired_parameters (bits:List Bool) :
    ((result bits) .width).length=bits.length ∧
    ((result bits) .threshold).length=16*bits.length ∧
    ((result bits) .radius).length=transformLength bits.length ∧
    ((result bits) .square).length=(transformLength bits.length)^2 ∧
    ((result bits) .exponent).length=transformExponent bits.length ∧
    ((result bits) .radix).length=radixBits bits.length := by
  simp [result,data,square_pow,transformLength]

/-- Actual output radix tally is ready for the physical original target-digit consumer. -/
theorem original_radix (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) :
    ((result bits) .radix).length=radixBits (bitLength (bitValue bits)) := by
  have h:=acquired_parameters bits |>.2.2.2.2.2
  have hw:bits.length=bitLength (bitValue bits):=SemiprimeD1BinaryBootstrap.canonical_width bits hc
  simpa only [hw] using h

/-- Original-input time is polynomial in the SAME public bitLength, with no prepared input counters. -/
def originalInTime (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine bits)
      (some (SemiprimeD1StackCalls.configuration (done bits)))
      (120000*(bitLength (bitValue bits)+1)^2) := by
  have h:=acquireInTime bits
  have hw:bits.length=bitLength (bitValue bits):=SemiprimeD1BinaryBootstrap.canonical_width bits hc
  simpa only [hw] using h
/-- The real nonzero flag licenses a positive radix tally without any supplied width predicate. -/
theorem radix_pos_of_flag (bits:List Bool) (hflag:(result bits) .nonzero=[true]) :
    0<((result bits) .radix).length := by
  have hn:0<bits.length:=by
    cases bits with
    | nil => simp [result,data,Boot.seenOne] at hflag
    | cons bit bits => simp
  rw [(acquired_parameters bits).2.2.2.2.2]
  exact radixBits_pos hn

/-- Canonical original input uses the SAME public bitLength in its actual all-visited memory bound. -/
theorem original_space (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits)
    (fuel:ℕ) (cfg:machine.Cfg)
    (hr:(fun cfg=>cfg.bind machine.step)^[fuel] (some (Turing.initList machine bits))=some cfg) :
    (cfg.stk (some Stack.input)).length+(cfg.stk (some Stack.width)).length+
      (cfg.stk (some Stack.nonzero)).length+(cfg.stk (some Stack.threshold)).length+
      (cfg.stk (some Stack.radius)).length+(cfg.stk (some Stack.square)).length+
      (cfg.stk (some Stack.exponent)).length+(cfg.stk (some Stack.squareWork)).length+
      (cfg.stk (some Stack.thresholdWork)).length+(cfg.stk (some Stack.temporary)).length+
      (cfg.stk (some Stack.radix)).length+(cfg.stk none).length≤1500000*(bitLength (bitValue bits)+1)^2 := by
  have h:=machine_space bits fuel cfg hr
  have hw:bits.length=bitLength (bitValue bits):=SemiprimeD1BinaryBootstrap.canonical_width bits hc
  simpa only [hw] using h
end RiemannGaussian.SemiprimeD1StackTransformBounds
