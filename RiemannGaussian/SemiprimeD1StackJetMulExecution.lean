/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetMul
/-! # Real linked dense-jet coefficient execution and output assembly -/
set_option autoImplicit false
set_option synthInstance.maxSize 8192
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1StackJetMulExecution
open SemiprimeD1StackJetMul
open SemiprimeD1StackProcedureTrace (Runs one_base runs_trans)
open SemiprimeD1StackJetPointExecution (Cache resting)
open SemiprimeD1StackUnaryDivmod (unary)
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeD1JetAxes (Context)

/-- Proof-side cache invariant for the actual physically updated target register. -/
def indexed (c : Cache) (index : List Bool) : Cache := {c with target:=index}
/-- Clean full-vector loop state; only coefficient and output are temporary payloads. -/
def data (c : Cache) (index word tail : List Bool) : Stack → List Bool
  | .inl k => resting (indexed c index) [] [] word k
  | .inr false => tail
  | .inr true => []

/-- Literal full-vector entry has no target/coefficient/output answer prepared. -/
theorem initial_data (c : Cache) : (initial c.a c.b c.axes c.width c.rank).data=data c [] [] [] := by
  funext k
  rcases k with k|k
  · exact congrFun (SemiprimeD1StackJetPointCorrectness.initial_data (indexed c [])) k
  · cases k <;> rfl

/-- Exact physical output-stack replacement. -/
theorem data_output_update (c : Cache) (index word tail newTail : List Bool) :
    Function.update (data c index word tail) output newTail=data c index word newTail := by
  funext k
  rcases k with k|k
  · rfl
  · cases k <;> rfl

/-- Exact physical target-counter replacement. -/
theorem data_index_update (c : Cache) (index word tail newIndex : List Bool) :
    Function.update (data c index word tail) counter newIndex=data c newIndex word tail := by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rfl
    · rcases k with k|k
      · rcases k with k|k
        · rfl
        · cases k <;> rfl
      · rcases k with k|k
        · rfl
        · cases k <;> rfl
  · cases k <;> rfl

/-- Exact physical coefficient-work replacement. -/
theorem data_coefficient_update (c : Cache) (index word tail newWord : List Bool) :
    Function.update (data c index word tail) coefficient newWord=data c index newWord tail := by
  funext k
  rcases k with k|k
  · simpa only [data,coefficient,Function.update_apply,Sum.inl.injEq] using
      congrFun (SemiprimeD1StackJetPointExecution.resting_acc_update (indexed c index) [] [] word newWord) k
  · cases k <;> rfl

/-- Actual rank-copy call acquires the full output-index counter once. -/
theorem rank_call (c : Cache) (tail : List Bool) :
    Runs program (5*c.rank.length+4) .copyRank (data c [] [] tail) .loop (data c c.rank [] tail) := by
  apply SemiprimeD1StackProcedureTrace.included_call program copyStack Label.copy copyStack_injective
    SemiprimeD1StackCopy.code (0:Fin 9) (fun _=>rfl) .copyRank .loop rfl (5*c.rank.length+3)
    (SemiprimeD1StackCopy.state 0 none c.rank [] []) (SemiprimeD1StackCopy.done c.rank c.rank)
  · rfl
  · rfl
  · simpa only [List.append_nil] using SemiprimeD1StackCopy.copy_words c.rank [] none
  · constructor
    · intro k
      fin_cases k <;> rfl
    · intro k hk
      rfl
  · constructor
    · intro k
      fin_cases k <;> rfl
    · intro k hk
      have hn : k ≠ counter := fun he=>hk 1 he.symm
      rw [←data_index_update c [] [] tail c.rank]
      exact Function.update_of_ne hn _ _

/-- Closed literal point-program call for the actual current physical target.
Original arrays are proof-side encodings, never executed coefficient getters. -/
theorem point_call (ctx : Context) (hp : ctx.Positive) (c : Cache) (a b : List (List Bool))
    (index tail : List Bool) (ha : c.a=vectorBits a) (hb : c.b=vectorBits b)
    (haxes : c.axes=vectorBits (ctx.axes.map unary)) (hwidth : c.width.length=ctx.precision)
    (hrank : c.rank=unary ctx.rank) :
    ∃ m ≤ 1000000*(SemiprimeD1StackJetPointBounds.inputSize ctx (indexed c index)+1)^5+1,
      Runs program m .callPoint (data c index [] tail) .callFrame
        (data c index (SemiprimeD1JetRingBits.mulAt ctx a b index.length).bits tail) := by
  obtain ⟨m,hm,hr⟩:=SemiprimeD1StackJetPointBounds.source_run_polynomial ctx hp (indexed c index) a b index.length
    ha hb haxes hwidth rfl hrank
  refine ⟨m+1,by omega,?_⟩
  apply SemiprimeD1StackProcedureInclusion.included_call program Sum.inl Label.point Sum.inl_injective
    SemiprimeD1StackJetPoint.program .start (fun _=>rfl) .callPoint .callFrame rfl m
    (SemiprimeD1StackJetPoint.initial c.a c.b c.axes c.width c.rank index)
    (⟨none,none,none,resting (indexed c index) [] [] (SemiprimeD1JetRingBits.mulAt ctx a b index.length).bits,[]⟩:
      SemiprimeD1StackCalls.State P.Stack P.Label)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact hr
  · constructor
    · intro k
      exact (congrFun (SemiprimeD1StackJetPointCorrectness.initial_data (indexed c index)) k).symm
    · intro k hk
      rfl
  · constructor
    · intro k
      rfl
    · intro k hk
      rcases k with k|k
      · exact False.elim (hk k rfl)
      · cases k <;> rfl

/-- Actual binary framing call preserves its source coefficient until cleanup. -/
theorem frame_call (c : Cache) (index word tail : List Bool) :
    Runs program (6*word.length+5) .callFrame (data c index word tail) .cons
      (data c index word (SemiprimeSourceHistogramKeyBits.frame word tail)) := by
  apply SemiprimeD1StackProcedureTrace.included_call program frameStack Label.frame frameStack_injective
    SemiprimeD1StackFrame.code (0:Fin 11) (fun _=>rfl) .callFrame .cons rfl (6*word.length+4)
    (SemiprimeD1StackFrame.state 0 none word tail [])
    (SemiprimeD1StackFrame.done word (SemiprimeSourceHistogramKeyBits.frame word tail))
  · rfl
  · rfl
  · exact SemiprimeD1StackFrame.frame_words word tail none
  · constructor
    · intro k
      fin_cases k <;> rfl
    · intro k hk
      rfl
  · constructor
    · intro k
      fin_cases k <;> rfl
    · intro k hk
      have hn : k ≠ output := fun he=>hk 1 he.symm
      rw [←data_output_update c index word tail (SemiprimeSourceHistogramKeyBits.frame word tail)]
      exact Function.update_of_ne hn _ _

/-- Actual coefficient cleanup consumes every binary payload cell. -/
theorem clear_run (c : Cache) (index word tail : List Bool) :
    Runs program (word.length+1) .clear (data c index word tail) .loop (data c index [] tail) := by
  induction word with
  | nil =>
    apply one_base program .clear .loop (.pop coefficient .loop .clear .clear) _ _ rfl
    · rfl
    · exact data_coefficient_update c index [] tail []
  | cons bit word ih =>
    have hs : Runs program 1 .clear (data c index (bit::word) tail) .clear (data c index word tail) := by
      apply one_base program .clear .clear (.pop coefficient .loop .clear .clear) _ _ rfl
      · cases bit <;> simp [SemiprimeD1StackBytecode.execute,SemiprimeD1StackBytecode.choose,
          coefficient,data,resting,SemiprimeD1StackJetPoint.aux]
      · exact data_coefficient_update c index (bit::word) tail word
    have h:=runs_trans program _ _ _ _ _ _ _ _ hs ih
    simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

/-- Real framing, vector-cons emission and source-word cleanup are all paid. -/
theorem emit_run (c : Cache) (index word : List Bool) (tail : List (List Bool)) :
    Runs program (7*word.length+7) .callFrame (data c index word (vectorBits tail)) .loop
      (data c index [] (vectorBits (word::tail))) := by
  have h1:=frame_call c index word (vectorBits tail)
  have h2 : Runs program 1 .cons
      (data c index word (SemiprimeSourceHistogramKeyBits.frame word (vectorBits tail))) .clear
      (data c index word (vectorBits (word::tail))) := by
    apply one_base program .cons .clear (.push output true .clear) _ _ rfl
    · rfl
    · exact data_output_update c index word _ _
  have h3:=clear_run c index word (vectorBits (word::tail))
  have h:=runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h1 h2) h3
  simpa only [show (6*word.length+5)+1+(word.length+1)=7*word.length+7 by omega] using h

/-- Concrete original-data per-coordinate bound for the actual included point,
framing and cleanup procedures; all partial coefficient widths are derived. -/
def bodyBudget (ctx : Context) (c : Cache) (n : ℕ) : ℕ :=
  1000000*(SemiprimeD1StackJetPointBounds.inputSize ctx (indexed c (unary n))+1)^5+7*ctx.precision+8

/-- Complete closed physical coefficient/body path, with no output or cost supplier. -/
theorem body_run (ctx : Context) (hp : ctx.Positive) (c : Cache) (a b : List (List Bool))
    (n : ℕ) (tail : List (List Bool)) (ha : c.a=vectorBits a) (hb : c.b=vectorBits b)
    (haxes : c.axes=vectorBits (ctx.axes.map unary)) (hwidth : c.width.length=ctx.precision)
    (hrank : c.rank=unary ctx.rank) :
    ∃ m ≤ bodyBudget ctx c n,
      Runs program m .callPoint (data c (unary n) [] (vectorBits tail)) .loop
        (data c (unary n) [] (vectorBits ((SemiprimeD1JetRingBits.mulAt ctx a b n).bits::tail))) := by
  obtain ⟨mp,hpbound,hpRun⟩:=point_call ctx hp c a b (unary n) (vectorBits tail) ha hb haxes hwidth hrank
  simp only [unary,List.length_replicate] at hpRun
  have hemit:=emit_run c (unary n) (SemiprimeD1JetRingBits.mulAt ctx a b n).bits tail
  refine ⟨mp+(7*(SemiprimeD1JetRingBits.mulAt ctx a b n).bits.length+7),?_,
    runs_trans program _ _ _ _ _ _ _ _ hpRun hemit⟩
  have hl:=SemiprimeD1JetRingBits.mulAt_length ctx a b n
  unfold bodyBudget
  omega

/-- One actual output-counter decrement acquires the next target index. -/
theorem loop_pop (c : Cache) (n : ℕ) (tail : List Bool) :
    Runs program 1 .loop (data c (unary (n+1)) [] tail) .callPoint (data c (unary n) [] tail) := by
  apply one_base program .loop .callPoint (.pop counter .done .callPoint .callPoint) _ _ rfl
  · simp [SemiprimeD1StackBytecode.execute,SemiprimeD1StackBytecode.choose,counter,data,resting,
      indexed,SemiprimeD1StackJetPoint.aux,unary,List.replicate_succ]
  · exact data_index_update c (unary (n+1)) [] tail (unary n)

/-- The actual EOF test reaches the literal halt label with no counter residue. -/
theorem loop_empty (c : Cache) (tail : List Bool) :
    Runs program 1 .loop (data c [] [] tail) .done (data c [] [] tail) := by
  apply one_base program .loop .done (.pop counter .done .callPoint .callPoint) _ _ rfl
  · rfl
  · exact data_index_update c [] [] tail []

/-- Proof-side original coordinate list in actual descending-prepend order. -/
def rows (ctx : Context) (a b : List (List Bool)) : ℕ → List (List Bool) → List (List Bool)
  | 0,tail => tail
  | n+1,tail => rows ctx a b n ((SemiprimeD1JetRingBits.mulAt ctx a b n).bits::tail)

/-- Original-dimension bound of the literal physical output-index loop. -/
def loopClock (ctx : Context) (c : Cache) : ℕ → ℕ
  | 0 => 1
  | n+1 => 1+bodyBudget ctx c n+loopClock ctx c n

/-- Whole physical dense traversal; each coordinate calls the original closed
point procedure and is emitted by actual framed Boolean-stack operations. -/
theorem loop_run (ctx : Context) (hp : ctx.Positive) (c : Cache) (a b : List (List Bool))
    (n : ℕ) (tail : List (List Bool)) (ha : c.a=vectorBits a) (hb : c.b=vectorBits b)
    (haxes : c.axes=vectorBits (ctx.axes.map unary)) (hwidth : c.width.length=ctx.precision)
    (hrank : c.rank=unary ctx.rank) :
    ∃ m ≤ loopClock ctx c n,
      Runs program m .loop (data c (unary n) [] (vectorBits tail)) .done
        (data c [] [] (vectorBits (rows ctx a b n tail))) := by
  induction n generalizing tail with
  | zero => exact ⟨1,le_rfl,loop_empty c (vectorBits tail)⟩
  | succ n ih =>
    have h1:=loop_pop c n (vectorBits tail)
    obtain ⟨mb,hbnd,h2⟩:=body_run ctx hp c a b n tail ha hb haxes hwidth hrank
    obtain ⟨mr,hrb,h3⟩:=ih ((SemiprimeD1JetRingBits.mulAt ctx a b n).bits::tail)
    refine ⟨1+mb+mr,?_,runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h1 h2) h3⟩
    change 1+mb+mr ≤ 1+bodyBudget ctx c n+loopClock ctx c n
    omega

end RiemannGaussian.SemiprimeD1StackJetMulExecution

