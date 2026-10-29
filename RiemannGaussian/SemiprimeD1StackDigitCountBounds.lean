/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackDigitCountExecution
import RiemannGaussian.SemiprimeD1BinaryPublicAcquisitionBounds

/-! # Actual cache-counter storage and original digitCount correspondence
The original-cache identity is derived from frozen real public acquisition,
not from a supplied quotient/count answer. N-only caller composition is a
separate following module; this scanner itself consumes physical cache bytes.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackDigitCountBounds
open SemiprimeD1StackDigitCount SemiprimeD1StackDigitCountExecution
open SemiprimeD1TensorTapeCodec (vectorBits)

/-- Every actually reached word is bounded by source bytes plus executed instructions. -/
theorem prefix_data_bound (bank:List Bool) (fuel:ℕ) (out:C.State Stack Label)
    (hr:C.run program fuel (initial bank)=some out) : ∀k,(out.data k).length≤bank.length+fuel := by
  apply SemiprimeD1StackReturnLink.run_data_bound program fuel bank.length _ out ?_ hr
  intro k
  cases k <;> simp [initial,data]

/-- A proved stopped count cannot execute extra successful steps. -/
theorem run_halted (n:ℕ) (state:C.State Stack Label) (hp:state.pc=none) : C.run program (n+1) state=none := by
  unfold C.run
  rw [Function.iterate_succ_apply]
  have hs:C.step program state=none:=by simp [C.step,SemiprimeD1StackCalls.step,hp]
  simp only [Option.bind_some,hs]
  exact Function.iterate_fixed rfl n

/-- Every machine prefix counts all seven Boolean roles and the actual return frames. -/
theorem machine_space (words:List (List Bool)) (fuel:ℕ) (cfg:machine.Cfg)
    (hr:(fun cfg=>cfg.bind machine.step)^[fuel] (some (Turing.initList machine (vectorBits words)))=some cfg) :
    (cfg.stk (some Stack.bank)).length+(cfg.stk (some Stack.reader)).length+
      (cfg.stk (some Stack.count)).length+(cfg.stk (some Stack.word)).length+
      (cfg.stk (some Stack.fieldScratch)).length+(cfg.stk (some Stack.valid)).length+
      (cfg.stk (some Stack.copyScratch)).length+(cfg.stk none).length≤100*((vectorBits words).length+1) := by
  rw [initial_eq] at hr
  let state:=initial (vectorBits words)
  change (fun cfg=>cfg.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration state))=some cfg at hr
  have he:=SemiprimeD1StackCalls.run_correct Stack.bank Stack.count (.inl .main) program fuel state
  change (C.run program fuel state).map SemiprimeD1StackCalls.configuration=
    (fun cfg=>cfg.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration state)) at he
  cases hc:C.run program fuel state with
  | none => rw [hc,hr] at he;cases he
  | some out =>
    rw [hc,hr] at he
    have hcfg:SemiprimeD1StackCalls.configuration out=cfg:=Option.some.inj he
    rw [←hcfg]
    have ht:fuel≤totalTime words:=by
      by_contra hn
      have ht:fuel=totalTime words+((fuel-totalTime words-1)+1):=by omega
      rw [ht,SemiprimeD1StackReturnLink.run_add,acquire_run words,Option.bind_some,
        run_halted _ (done words) rfl] at hc
      cases hc
    have htime:=totalTime_le words
    have hb:=prefix_data_bound (vectorBits words) fuel out hc
    have h0:=hb Stack.bank
    have h1:=hb Stack.reader
    have h2:=hb Stack.count
    have h3:=hb Stack.word
    have h4:=hb Stack.fieldScratch
    have h5:=hb Stack.valid
    have h6:=hb Stack.copyScratch
    have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel state out hc
    change out.frames.length≤0+fuel at hf
    change (out.data Stack.bank).length+(out.data Stack.reader).length+(out.data Stack.count).length+
      (out.data Stack.word).length+(out.data Stack.fieldScratch).length+(out.data Stack.valid).length+
      (out.data Stack.copyScratch).length+out.frames.length≤_
    omega

/-- Actual original metadata/cache source for the physical count scanner. -/
def originalWords (bits:List Bool) : List (List Bool) :=
  SemiprimeD1StackDigitBankSpec.blocks (SemiprimeD1BinaryDigitAcquisitionComponents.radix bits) bits.length bits
/-- Fixed actual retained bank stack of the N-only public acquisition machine. -/
def bankRole : SemiprimeD1BinaryPublicAcquisition.Stack :=
  SemiprimeD1BinaryPublicAcquisition.digitStack
    (SemiprimeD1BinaryDigitAcquisition.bankStack SemiprimeD1StackDigitBank.output)

/-- The actual acquired cache, not a count answer, is the physical scanner input. -/
theorem original_cache_run (bits:List Bool) :
    C.run program (totalTime (originalWords bits))
      (initial (SemiprimeD1BinaryPublicAcquisitionComponents.result bits bankRole))=
      some (done (originalWords bits)) := by
  change C.run program (totalTime (originalWords bits)) (initial (vectorBits (originalWords bits)))=_
  exact acquire_run _

/-- The counted physical marker word equals ORIGINAL digitCount, derived from the acquired cache. -/
theorem original_count (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits)
    (hN:0<SemiprimeBitArithmetic.bitValue bits) :
    ((done (originalWords bits)).data Stack.count).length=
      SemiprimeMacroParameters.digitCount (SemiprimeMacroParameters.bitLength (SemiprimeBitArithmetic.bitValue bits)) := by
  change (List.replicate (originalWords bits).length true).length=_
  rw [List.length_replicate]
  exact SemiprimeD1BinaryPublicAcquisitionBounds.original_count bits hc hN
end RiemannGaussian.SemiprimeD1StackDigitCountBounds
