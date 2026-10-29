/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetPointLoops
/-! # Closed physical original jet-coefficient execution
The finite program is fixed before every input. Its axes, precision/rank/index
counters and encoded coefficient vectors are prepared physical tapes. Context
acquisition is explicit in the caller, and is not claimed free by this interface.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1StackJetPointCorrectness
open SemiprimeD1StackJetPoint SemiprimeD1StackJetPointExecution SemiprimeD1StackJetPointLoops
open SemiprimeD1StackProcedureTrace (Runs runs_trans At)
open SemiprimeD1StackUnaryDivmod (unary)
open SemiprimeD1JetAxes (Context)

/-- The literal prepared entry has no live routing/reader/arithmetic work. -/
theorem initial_data (c : Cache) :
    (initial c.a c.b c.axes c.width c.rank c.target).data=resting c [] [] [] := by
  funext k
  rcases k with k|k
  · rfl
  · rcases k with k|k
    · rcases k with k|k
      · rfl
      · cases k <;> rfl
    · rcases k with k|k
      · rfl
      · cases k <;> rfl

/-- Actual original-data transition envelope before numeric simplification. -/
def totalClock (ctx : Context) (c : Cache) (a b : List (List Bool)) (k : ℕ) : ℕ :=
  5*c.rank.length+5+outerClock ctx c a b k ctx.rank ctx.rank []

/-- The complete fixed program executes every physical pair visit and returns
EXACT original canonical coefficient bytes, with all temporary/operand counters
cleared and all persistent input/context caches preserved. -/
theorem source_run (ctx : Context) (hp : ctx.Positive) (c : Cache) (a b : List (List Bool)) (k : ℕ)
    (ha : c.a=SemiprimeD1TensorTapeCodec.vectorBits a)
    (hb : c.b=SemiprimeD1TensorTapeCodec.vectorBits b)
    (haxes : c.axes=SemiprimeD1TensorTapeCodec.vectorBits (ctx.axes.map unary))
    (hwidth : c.width.length=ctx.precision) (htarget : c.target.length=k) (hrank : c.rank=unary ctx.rank) :
    ∃ m ≤ totalClock ctx c a b k,
      SemiprimeD1StackCalls.run program m (initial c.a c.b c.axes c.width c.rank c.target)=
        some (⟨none,none,none,resting c [] [] (SemiprimeD1JetRingBits.mulAt ctx a b k).bits,[]⟩:
          SemiprimeD1StackCalls.State Stack Label) := by
  have hstart:=copy_call .rankI .start .outer (resting c [] [] []) rfl (by rfl) (by rfl)
  change Runs program (5*c.rank.length+4) .start (resting c [] [] []) .outer
    (Function.update (resting c [] [] []) (aux .i) c.rank) at hstart
  rw [resting_i_update] at hstart
  obtain ⟨mo,ho,houter⟩:=outer_run ctx hp c a b k ctx.rank ctx.rank [] ha hb haxes hwidth htarget hrank
  rw [←hrank,outerValue_original] at houter
  have h:=runs_trans program _ _ _ _ _ _ _ _ hstart houter
  have hinit : At .start (resting c [] [] []) [] (initial c.a c.b c.axes c.width c.rank c.target) :=
    ⟨rfl,initial_data c,rfl⟩
  obtain ⟨out,hout,houtAt⟩:=h [] _ hinit
  have hhalt:=SemiprimeD1StackProcedureTrace.halt_run program .done rfl
    (resting c [] [] (SemiprimeD1JetRingBits.mulAt ctx a b k).bits) [] out houtAt
  refine ⟨(5*c.rank.length+4)+mo+1,?_,?_⟩
  · unfold totalClock
    omega
  · rw [SemiprimeD1StackReturnLink.run_add,hout,Option.bind_some]
    exact hhalt

/-- Genuine original coefficient execution certificate for the source machine. -/
noncomputable def sourcePoint (ctx : Context) (hp : ctx.Positive) (c : Cache) (a b : List (List Bool)) (k : ℕ)
    (ha : c.a=SemiprimeD1TensorTapeCodec.vectorBits a)
    (hb : c.b=SemiprimeD1TensorTapeCodec.vectorBits b)
    (haxes : c.axes=SemiprimeD1TensorTapeCodec.vectorBits (ctx.axes.map unary))
    (hwidth : c.width.length=ctx.precision) (htarget : c.target.length=k) (hrank : c.rank=unary ctx.rank) :
    StateTransition.EvalsToInTime (SemiprimeD1StackCalls.step program)
      (initial c.a c.b c.axes c.width c.rank c.target)
      (some (⟨none,none,none,resting c [] [] (SemiprimeD1JetRingBits.mulAt ctx a b k).bits,[]⟩:
        SemiprimeD1StackCalls.State Stack Label)) (totalClock ctx c a b k) := by
  let h:=source_run ctx hp c a b k ha hb haxes hwidth htarget hrank
  let m:=Classical.choose h
  have hm:=Classical.choose_spec h
  exact ⟨⟨m,hm.2⟩,hm.1⟩

/-- The actual compiled finite-stack machine returns the original coefficient,
without a native evaluator, route oracle or assumed subroutine clock. -/
noncomputable def machinePoint (ctx : Context) (hp : ctx.Positive) (c : Cache) (a b : List (List Bool)) (k : ℕ)
    (ha : c.a=SemiprimeD1TensorTapeCodec.vectorBits a)
    (hb : c.b=SemiprimeD1TensorTapeCodec.vectorBits b)
    (haxes : c.axes=SemiprimeD1TensorTapeCodec.vectorBits (ctx.axes.map unary))
    (hwidth : c.width.length=ctx.precision) (htarget : c.target.length=k) (hrank : c.rank=unary ctx.rank) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial c.a c.b c.axes c.width c.rank c.target))
      (some (SemiprimeD1StackCalls.configuration
        (⟨none,none,none,resting c [] [] (SemiprimeD1JetRingBits.mulAt ctx a b k).bits,[]⟩:
          SemiprimeD1StackCalls.State Stack Label))) (totalClock ctx c a b k) :=
  SemiprimeD1StackCalls.evalsCorrect (aux .a) (aux .acc) Label.start program _ _ _
    (sourcePoint ctx hp c a b k ha hb haxes hwidth htarget hrank)

end RiemannGaussian.SemiprimeD1StackJetPointCorrectness
