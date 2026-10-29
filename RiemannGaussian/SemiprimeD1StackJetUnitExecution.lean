/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetUnit
import RiemannGaussian.SemiprimeD1JetAffineCoefficient
/-! # Actual literal seeding and dense-unit byte refinement -/
set_option autoImplicit false
set_option synthInstance.maxSize 8192
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace RiemannGaussian.SemiprimeD1StackJetUnitExecution
open SemiprimeD1StackJetUnit
open SemiprimeD1StackProcedureTrace (Runs one_base runs_trans At)
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeD1JetAxes (Context)

/-- The original dense arithmetic itself computes the exact canonical unit. -/
theorem add_unit_words (ctx : Context) :
    (SemiprimeD1JetRingBits.add ctx [[true]] []).words=(SemiprimeD1JetAffineCoefficient.one ctx).words := by
  simp only [SemiprimeD1JetRingBits.add,List.map_map,Function.comp_def,SemiprimeD1JetAffineCoefficient.one]
  apply List.map_congr_left
  intro i hi
  cases i with
  | zero =>
    simp [SemiprimeD1JetRingBits.addAt,SemiprimeD1JetRingBits.read,SemiprimeD1JetScalarBits.add,
      SemiprimeBitArithmetic.addBits,SemiprimeBitArithmetic.fullAdder]
  | succ i =>
    change (SemiprimeD1JetScalarBits.add ctx.precision [] []).bits=[]
    cases ctx.precision <;> simp [SemiprimeD1JetScalarBits.add,SemiprimeBitArithmetic.addBits,
      SemiprimeD1JetScalarBits.reduce,SemiprimeD1JetScalarBits.takeBits,SemiprimeSourceCompactBits.trim]

/-- One actual left-vector literal bit push preserves all context/work fields. -/
theorem push_left (width rank a b : List Bool) (bit : Bool) (pc next : Label)
    (hcode : program pc=.base (.push (.inr .leftTape) bit next)) :
    Runs program 1 pc (bank width rank a b []) next (bank width rank (bit::a) b []) := by
  apply one_base program pc next (.push (.inr .leftTape) bit next) _ _ hcode
  · rfl
  · funext k
    rcases k with k|k
    · rfl
    · cases k <;> rfl

/-- All six input-vector bits are physically seeded; no array constructor runs. -/
theorem seed_run (width rank : List Bool) :
    Runs program 6 .seed0 (bank width rank [] [] []) .callAdd
      (bank width rank (vectorBits [[true]]) (vectorBits []) []) := by
  have h1:=push_left width rank [] [] false .seed0 .seed1 rfl
  have h2:=push_left width rank [false] [] false .seed1 .seed2 rfl
  have h3:=push_left width rank [false,false] [] true .seed2 .seed3 rfl
  have h4:=push_left width rank [true,false,false] [] true .seed3 .seed4 rfl
  have h5:=push_left width rank [true,true,false,false] [] true .seed4 .seed5 rfl
  have h6 : Runs program 1 .seed5 (bank width rank [true,true,true,false,false] [] []) .callAdd
      (bank width rank [true,true,true,false,false] [false] []) := by
    apply one_base program .seed5 .callAdd (.push (.inr .rightTape) false .callAdd) _ _ rfl
    · rfl
    · funext k
      rcases k with k|k
      · rfl
      · cases k <;> rfl
  exact runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _
    (runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _
      (runs_trans program _ _ _ _ _ _ _ _ h1 h2) h3) h4) h5) h6

/-- The actual dense adder canonicalizes the literal seed using cached counters. -/
theorem add_call (width rank : List Bool) :
    Runs program (SemiprimeD1StackJetAddExecution.totalTime width rank [[true]] []+1) .callAdd
      (bank width rank (vectorBits [[true]]) (vectorBits []) []) .done
      (bank width rank [] [] (vectorBits (SemiprimeD1StackJetAddExecution.rows rank width [[true]] []))) := by
  apply SemiprimeD1StackProcedureInclusion.included_call program id Label.add Function.injective_id
    A.program .start (fun _=>rfl) .callAdd .done rfl _
    (SemiprimeD1StackJetAdd.state (some .start) none none [] [] [] [] width []
      (vectorBits [[true]]) (vectorBits []) rank [] [] [] [] [] [])
    (SemiprimeD1StackJetAdd.state none none none [] [] [] [] width [] [] [] rank [] []
      (vectorBits (SemiprimeD1StackJetAddExecution.rows rank width [[true]] [])) [] [] [])
  · rfl
  · rfl
  · rfl
  · rfl
  · exact SemiprimeD1StackJetAddExecution.source_run width rank [[true]] []
  · constructor
    · intro k; rfl
    · intro k hk; exact False.elim (hk k rfl)
  · constructor
    · intro k; rfl
    · intro k hk; exact False.elim (hk k rfl)

/-- Exact source time includes all literal seeding, real call/return and final halt. -/
def totalTime (width rank : List Bool) : ℕ :=
  SemiprimeD1StackJetAddExecution.totalTime width rank [[true]] []+8

/-- Closed actual unit construction from cached physical counters only. -/
theorem source_run (ctx : Context) (width rank : List Bool) (hw : width.length=ctx.precision)
    (hr : rank.length=ctx.rank) :
    SemiprimeD1StackCalls.run program (totalTime width rank) (initial width rank)=
      some (⟨none,none,none,bank width rank [] [] (vectorBits (SemiprimeD1JetAffineCoefficient.one ctx).words),[]⟩:
        SemiprimeD1StackCalls.State Stack Label) := by
  have h1:=seed_run width rank
  have h2:=add_call width rank
  have hrows:=SemiprimeD1StackJetAddExecution.rows_eq_original ctx width rank [[true]] [] hw hr
  rw [add_unit_words] at hrows
  rw [hrows] at h2
  have h:=runs_trans program _ _ _ _ _ _ _ _ h1 h2
  obtain ⟨out,hout,hAt⟩:=h [] (initial width rank) ⟨rfl,rfl,rfl⟩
  have hhalt:=SemiprimeD1StackProcedureTrace.halt_run program .done rfl
    (bank width rank [] [] (vectorBits (SemiprimeD1JetAffineCoefficient.one ctx).words)) [] out hAt
  have hh : SemiprimeD1StackCalls.run program
      ((6+(SemiprimeD1StackJetAddExecution.totalTime width rank [[true]] []+1))+1) (initial width rank)=
      some (⟨none,none,none,bank width rank [] [] (vectorBits (SemiprimeD1JetAffineCoefficient.one ctx).words),[]⟩:
        SemiprimeD1StackCalls.State Stack Label) := by
    rw [SemiprimeD1StackReturnLink.run_add,hout,Option.bind_some]
    exact hhalt
  simpa only [totalTime,show 6+(SemiprimeD1StackJetAddExecution.totalTime width rank [[true]] []+1)+1=
    SemiprimeD1StackJetAddExecution.totalTime width rank [[true]] []+8 by omega] using hh

/-- Fixed polynomial time in original physical cache lengths. -/
def timeBound (precision rank : ℕ) : ℕ := 200*(rank+1)*(precision+8)+8

/-- The unit producer has no advised scalar/rank answer or operation budget. -/
theorem totalTime_le (width rank : List Bool) : totalTime width rank ≤ timeBound width.length rank.length := by
  have h:=SemiprimeD1StackJetAddExecution.totalTime_le width rank [[true]] []
  change SemiprimeD1StackJetAddExecution.totalTime width rank [[true]] [] ≤
    200*(rank.length+1)*(5+1+width.length+2) at h
  rw [show 5+1+width.length+2=width.length+8 by omega] at h
  exact Nat.add_le_add_right h 8

/-- Genuine actual finite-stack dense-unit acquisition, including precision zero. -/
def machineUnit (ctx : Context) (width rank : List Bool) (hw : width.length=ctx.precision)
    (hr : rank.length=ctx.rank) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial width rank))
      (some (SemiprimeD1StackCalls.configuration
        (⟨none,none,none,bank width rank [] [] (vectorBits (SemiprimeD1JetAffineCoefficient.one ctx).words),[]⟩:
          SemiprimeD1StackCalls.State Stack Label))) (timeBound width.length rank.length) := by
  apply SemiprimeD1StackCalls.evalsCorrect widthCache output Label.seed0 program
  exact ⟨⟨totalTime width rank,source_run ctx width rank hw hr⟩,totalTime_le width rank⟩

end RiemannGaussian.SemiprimeD1StackJetUnitExecution
