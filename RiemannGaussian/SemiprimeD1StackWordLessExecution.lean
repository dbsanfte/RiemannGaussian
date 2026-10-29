/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackWordLess
import RiemannGaussian.SemiprimeMacroEntryBitPrimitives

/-! # Exact physical canonicality guard and complete bit-cell bounds
Both input words and all difference cells are consumed. The Boolean answer is
the actually computed borrow, including unequal padding and all zero encodings.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackWordLessExecution
open SemiprimeD1StackWordLess SemiprimeD1StackProcedureTrace

/-- Proof-side raw difference bytes from the actual subtractor. -/
def difference (a b : List Bool) : List Bool := (SemiprimeBitDivision.subBits a b false).result.bits
/-- The actual computed borrow prefix; never a caller operand. -/
def answer (a b : List Bool) : Bool := (SemiprimeBitDivision.subBits a b false).borrow
/-- Exact literal subtractor trace length. -/
def subtractTime (a b : List Bool) : ℕ := 3*(max a.length b.length+1)+2*(difference a b).length+3
/-- Every actual call, borrow read/write, difference pop and halt is counted. -/
def totalTime (a b : List Bool) : ℕ := (subtractTime a b+1)+2+((difference a b).length+1)+1
/-- Final actual state has only the computed Boolean answer. -/
def done (a b : List Bool) : C.State Stack Label :=
  ⟨none,none,none,store [] [] [] [] [answer a b],[]⟩

/-- The complete actual ripple/borrow procedure executes inside this caller. -/
theorem subtract_call (a b : List Bool) :
    Runs program (subtractTime a b+1) .start (store a b [] [] [])
      .readBorrow (store [] [] [] (answer a b::difference a b) []) := by
  apply included_call program Sum.inl Label.subtract Sum.inl_injective SemiprimeD1StackSubtractor.code
    (.start false) (fun _=>rfl) .start .readBorrow rfl (subtractTime a b)
    (SemiprimeD1StackSubtractor.state (some (.start false)) none a b [] [])
    (SemiprimeD1StackSubtractor.state none none [] [] [] (answer a b::difference a b))
    (store a b [] [] []) (store [] [] [] (answer a b::difference a b) [])
  · rfl
  · rfl
  · exact SemiprimeD1StackSubtractorExecution.source_run a b false
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k
      · exact False.elim (hk k rfl)
      · rfl

/-- The actual borrow bit is read and physically copied to the Boolean output. -/
theorem borrow_run (bit : Bool) (diff : List Bool) :
    Runs program 2 .readBorrow (store [] [] [] (bit::diff) [])
      .clearDifference (store [] [] [] diff [bit]) := by
  have h0 : Runs program 1 .readBorrow (store [] [] [] (bit::diff) [])
      (.save bit) (store [] [] [] diff []) := by
    apply one_base program .readBorrow (.save bit)
      (.pop (.inl .output) (.save false) (.save false) (.save true)) _ _ rfl
    · cases bit <;> rfl
    · funext k
      rcases k with k|k
      · cases k <;> rfl
      · rfl
  have h1 : Runs program 1 (.save bit) (store [] [] [] diff [])
      .clearDifference (store [] [] [] diff [bit]) := by
    apply one_base program (.save bit) .clearDifference (.push output bit .clearDifference) _ _ rfl
    · rfl
    · funext k
      rcases k with k|k
      · rfl
      · cases k;rfl
  exact runs_trans program 1 1 _ _ _ _ _ _ h0 h1

/-- Every unneeded difference cell is physically erased before returning. -/
theorem clear_run (diff : List Bool) (bit : Bool) :
    Runs program (diff.length+1) .clearDifference (store [] [] [] diff [bit])
      .done (store [] [] [] [] [bit]) := by
  have h:=SemiprimeD1StackPhysicalLoops.drain program .clearDifference .done
    (.inl .output) rfl (store [] [] [] [] [bit]) diff
  have hi : Function.update (store [] [] [] [] [bit]) (.inl .output) diff=store [] [] [] diff [bit] := by
    funext k
    rcases k with k|k
    · cases k <;> simp [Function.update,store,S.store]
    · cases k;simp [Function.update,store]
  have ho : Function.update (store [] [] [] [] [bit]) (.inl .output) []=store [] [] [] [] [bit] :=
    Function.update_eq_self _ _
  rw [hi,ho] at h
  exact h

/-- Complete exact source trace from physical operand words to a sole Boolean. -/
theorem source_run (a b : List Bool) :
    C.run program (totalTime a b) (initial a b)=some (done a b) := by
  have h0:=subtract_call a b
  have h1:=borrow_run (answer a b) (difference a b)
  have h2:=clear_run (difference a b) (answer a b)
  have hh:=runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2
  obtain ⟨finish,hfinish,hout⟩:=hh [] (initial a b) ⟨rfl,rfl,rfl⟩
  have hf:=halt_run program .done rfl (store [] [] [] [] [answer a b]) [] finish hout
  rw [totalTime,SemiprimeD1StackReturnLink.run_add,hfinish,Option.bind_some,hf]
  rfl

/-- Linear elapsed bound depends only on actual bit lengths, never values. -/
theorem totalTime_le (a b : List Bool) : totalTime a b ≤ 6*(a.length+b.length)+12 := by
  have hd:=(SemiprimeBitDivision.subBits_counts a b false).2.2.2.2
  change (difference a b).length=max a.length b.length at hd
  have hm : max a.length b.length ≤ a.length+b.length := max_le (by omega) (by omega)
  unfold totalTime subtractTime
  omega

/-- Actual transition certificate of this closed canonicality guard. -/
def sourceLess (a b : List Bool) :
    StateTransition.EvalsToInTime (C.step program) (initial a b) (some (done a b))
      (6*(a.length+b.length)+12) := ⟨⟨_,source_run a b⟩,totalTime_le a b⟩
/-- Genuine finite-machine comparison with the SAME actual elapsed bound. -/
def machineLess (a b : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial a b))
      (some (SemiprimeD1StackCalls.configuration (done a b))) (6*(a.length+b.length)+12) :=
  SemiprimeD1StackCalls.evalsCorrect (K:=Stack) (L:=Label) (Sum.inl .left) output Label.start program
    _ _ _ (sourceLess a b)
/-- Exact original public checker's canonicality guard, including malformed words. -/
theorem original_answer (a b : List Bool) : answer a b=(SemiprimeMacroEntryBitPrimitives.lessBits a b).accepted := rfl
/-- The physically computed answer has the ordinary integer order semantics. -/
theorem answer_true (a b : List Bool) :
    answer a b=true ↔ SemiprimeBitArithmetic.bitValue a < SemiprimeBitArithmetic.bitValue b := by
  rw [original_answer]
  exact SemiprimeMacroEntryBitPrimitives.lessBits_correct a b

/-- No successful executed prefix can extend past the actual halt. -/
theorem prefix_fuel_le (a b : List Bool) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (initial a b)=some out) : fuel ≤ 6*(a.length+b.length)+12 := by
  have hf : fuel ≤ totalTime a b := by
    by_contra hn
    have he : fuel=totalTime a b+(1+(fuel-(totalTime a b+1))) := by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,source_run,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add] at hr
    have hz : C.run program 1 (done a b)=none := rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans (totalTime_le a b)
/-- Every prefix includes all data, subtraction workspace and real return tags. -/
theorem prefix_cells (a b : List Bool) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (initial a b)=some out) :
    (∑k : Stack,(out.data k).length)+out.frames.length ≤ 100*(a.length+b.length+1) := by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (a.length+b.length) _ out (by
    intro k
    rcases k with k|k
    · cases k <;> simp [initial,store,S.store]
    · cases k;simp [initial,store]) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length ≤ 0+fuel at hf
  have hs : (∑k : Stack,(out.data k).length) ≤ 5*(a.length+b.length+fuel) := by
    calc
      _ ≤ ∑_k : Stack,(a.length+b.length+fuel) := Finset.sum_le_sum (fun k _=>hd k)
      _ = _ := by
        have hc : Fintype.card Stack=5 := by decide
        simp only [Finset.sum_const,Finset.card_univ,hc,smul_eq_mul]
  have ht:=prefix_fuel_le a b fuel out hr
  omega
/-- All prefixes of the compiled machine satisfy the SAME linear storage bound. -/
theorem machine_prefix_cells (a b : List Bool) (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial a b)))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤ 100*(a.length+b.length+1) := by
  have he:=SemiprimeD1StackCalls.run_correct (Sum.inl .left) output Label.start program fuel (initial a b)
  change (C.run program fuel (initial a b)).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration (initial a b))) at he
  have hh:=he.trans hr
  cases hc:C.run program fuel (initial a b) with
  | none => rw [hc] at hh;cases hh
  | some out =>
    rw [hc] at hh
    have hcfg : SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj hh
    subst cfg
    exact prefix_cells a b fuel out hc

end RiemannGaussian.SemiprimeD1StackWordLessExecution
