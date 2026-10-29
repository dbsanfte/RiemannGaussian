/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackExprDotExecution
import RiemannGaussian.SemiprimeD1StackJetPointBounds

/-! # Closed physical dot-source cost and storage
The inventory includes the entire encoded input vector and all physically
acquired marker words. Products and repeated syntax construction are paid by
their actual traces. This is a prepared-cache source builder; original-input
acquisition of those caches is still the enclosing caller's work.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackExprDotBounds
open SemiprimeD1StackExprDot SemiprimeD1StackExprDotExecution
open SemiprimeD1StackUnaryDivmod (unary)
open SemiprimeD1TensorTapeCodec (vectorBits)

/-- Actual physical argument inventory, including complete source and metadata. -/
def inputSize (c : Cache) : ℕ :=
  c.base.length+c.words.length+c.stride.length+c.frequency.length+c.count.length+1

/-- Fixed polynomial envelope for a single whole term, not an advised clock. -/
def termBound (S : ℕ) : ℕ :=
  (5*S+4)+(5*(S*(2*S+3)+1)+1)+(5*((S*S)*(2*S+3)+1)+1)+
    (S^3*(5*S+18)+17)+(S^3+1)+(5*S+4)+(30*(2*S+2)+1)+
    (6*S+5)+4+(S+1)

/-- Every selected word and both acquired exponent products are bounded by the
physical input inventory; no selected value or exponent cap is a premise. -/
theorem budget_le (c : Cache) (words : List (List Bool)) (stride frequency j S : ℕ)
    (hb : c.base.length ≤ S) (hw : (vectorBits words).length ≤ S)
    (hs : stride ≤ S) (hf : frequency ≤ S) (hj : j ≤ S) :
    SemiprimeD1StackExprDotTerm.budget c words stride frequency j ≤ termBound S := by
  have hword : (SemiprimeD1StackExprDotSpec.wordAt words j).length ≤ S :=
    (SemiprimeD1StackJetPointBounds.coefficient_length words j).trans hw
  have hjf : j*frequency ≤ S*S := Nat.mul_le_mul hj hf
  have he : stride*(j*frequency) ≤ S^3 := by
    calc
      _ ≤ S*(S*S) := Nat.mul_le_mul hs hjf
      _ = _ := by ring
  have hp1 : 5*(j*(2*frequency+3)+1)+1 ≤ 5*(S*(2*S+3)+1)+1 := by gcongr
  have hp2 : 5*((j*frequency)*(2*stride+3)+1)+1 ≤ 5*((S*S)*(2*S+3)+1)+1 := by
    gcongr
  have hpower : stride*(j*frequency)*(5*c.base.length+18)+17 ≤ S^3*(5*S+18)+17 := by
    gcongr
  have hr := SemiprimeD1StackJetReadExecution.totalTime_le (unary j) words
  simp only [SemiprimeD1StackJetReadExecution.timeBound,unary,List.length_replicate] at hr
  have hread : SemiprimeD1StackJetReadExecution.totalTime (unary j) words ≤ 30*(2*S+2) := by
    simp only [unary]
    omega
  unfold SemiprimeD1StackExprDotTerm.budget termBound
  rw [SemiprimeD1StackExprPowerBounds.totalTime_eq]
  simp only [unary,List.length_replicate]
  omega

/-- Uniform fourth degree envelope includes every copied base subtree. -/
theorem termBound_le (S : ℕ) : termBound S ≤ 1000*(S+1)^4 := by
  unfold termBound
  nlinarith [Nat.zero_le (S^2),Nat.zero_le (S^3),Nat.zero_le (S^4)]

/-- All visits of the actual decreasing counter are counted. -/
theorem loopBudget_le (c : Cache) (words : List (List Bool)) (stride frequency S : ℕ)
    (hb : c.base.length ≤ S) (hw : (vectorBits words).length ≤ S)
    (hs : stride ≤ S) (hf : frequency ≤ S) (n : ℕ) (hn : n ≤ S) :
    loopBudget c words stride frequency n ≤ (n+1)*(termBound S+1) := by
  induction n with
  | zero => simp only [loopBudget,Nat.zero_add,Nat.one_mul];omega
  | succ n ih =>
    have hprev := ih (by omega)
    have hterm := budget_le c words stride frequency n S hb hw hs hf (by omega)
    simp only [loopBudget]
    nlinarith

/-- Derived fifth degree own-program bound from actual cache bytes only. -/
theorem timeBound_le (c : Cache) (words : List (List Bool)) (stride frequency n : ℕ)
    (hs : c.stride=unary stride) (hf : c.frequency=unary frequency)
    (hn : c.count=unary n) (hc : c.words=vectorBits words) :
    timeBound c words stride frequency n ≤ 10000*(inputSize c+1)^5 := by
  let S:=inputSize c
  have hb : c.base.length ≤ S := by dsimp [S,inputSize];omega
  have hw : (vectorBits words).length ≤ S := by dsimp [S,inputSize];rw [hc];omega
  have hstride : stride ≤ S := by dsimp [S,inputSize];rw [hs];simp only [unary,List.length_replicate];omega
  have hfreq : frequency ≤ S := by dsimp [S,inputSize];rw [hf];simp only [unary,List.length_replicate];omega
  have hcount : n ≤ S := by dsimp [S,inputSize];rw [hn];simp only [unary,List.length_replicate];omega
  have hloop:=loopBudget_le c words stride frequency S hb hw hstride hfreq n hcount
  have hterm:=termBound_le S
  have hprod : (n+1)*(termBound S+1) ≤ (S+1)*(1000*(S+1)^4+1) := by gcongr
  have hp : (S+1)*(1000*(S+1)^4+1)+13*S+13 ≤ 10000*(S+1)^5 := by
    nlinarith [Nat.zero_le (S^2),Nat.zero_le (S^3),Nat.zero_le (S^4),Nat.zero_le (S^5)]
  change timeBound c words stride frequency n ≤ 10000*(S+1)^5
  unfold timeBound
  omega

/-- An actual source certificate for the complete program, never a callback. -/
noncomputable def sourceBuild (c : Cache) (words : List (List Bool)) (stride frequency n : ℕ)
    (hs : c.stride=unary stride) (hf : c.frequency=unary frequency)
    (hn : c.count=unary n) (hc : c.words=vectorBits words) (tail : List Bool) :
    StateTransition.EvalsToInTime (C.step program) (initial c tail)
      (some (done c words stride frequency n tail)) (10000*(inputSize c+1)^5) := by
  let h:=source_run c words stride frequency n hs hf hn hc tail
  let m:=Classical.choose h
  have hm:=Classical.choose_spec h
  exact ⟨⟨m,hm.2⟩,hm.1.trans (timeBound_le c words stride frequency n hs hf hn hc)⟩

/-- The same completed trace on a fixed finite-stack bit machine. -/
noncomputable def machineBuild (c : Cache) (words : List (List Bool)) (stride frequency n : ℕ)
    (hs : c.stride=unary stride) (hf : c.frequency=unary frequency)
    (hn : c.count=unary n) (hc : c.words=vectorBits words) (tail : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial c tail))
      (some (SemiprimeD1StackCalls.configuration (done c words stride frequency n tail)))
      (10000*(inputSize c+1)^5) :=
  SemiprimeD1StackCalls.evalsCorrect (K:=Stack) (L:=Label) Stack.base Stack.output (Label.control .start) program _ _ _
    (sourceBuild c words stride frequency n hs hf hn hc tail)

/-- Exact original dot-expression source bytes and retained physical suffix. -/
theorem output_original (c : Cache) (baseExpr : SemiprimeMacroEntryBitPrimitives.Expr)
    (hbase : c.base=SemiprimeD1StackExprCodec.encode baseExpr [])
    (words : List (List Bool)) (stride frequency n : ℕ) (tail : List Bool) :
    (done c words stride frequency n tail).data .output=
      SemiprimeD1StackExprCodec.encode
        (SemiprimeMacroEntryBitPrimitives.dotExpr baseExpr stride frequency
          (SemiprimeD1StackExprDotSpec.wordAt words) n) tail := by
  change SemiprimeD1StackExprDotSpec.result n c.base words stride frequency tail=_
  rw [hbase]
  exact SemiprimeD1StackExprDotSpec.result_original baseExpr words stride frequency n tail

/-- Every successful prefix stops by the proved own-program halt. -/
theorem prefix_fuel_le (c : Cache) (words : List (List Bool)) (stride frequency n : ℕ)
    (hs : c.stride=unary stride) (hf : c.frequency=unary frequency)
    (hn : c.count=unary n) (hc : c.words=vectorBits words) (tail : List Bool)
    (fuel : ℕ) (out : C.State Stack Label) (hr : C.run program fuel (initial c tail)=some out) :
    fuel ≤ 10000*(inputSize c+1)^5 := by
  obtain ⟨m,hm,he⟩:=source_run c words stride frequency n hs hf hn hc tail
  have hfm : fuel ≤ m := by
    by_contra h
    have hh : fuel=m+(1+(fuel-(m+1))) := by omega
    rw [hh,SemiprimeD1StackReturnLink.run_add,he,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add] at hr
    have hz : C.run program 1 (done c words stride frequency n tail)=none := rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hfm.trans (hm.trans (timeBound_le c words stride frequency n hs hf hn hc))

/-- Every prefix counts all22 Boolean stacks and real finite-label return cells. -/
theorem prefix_cells (c : Cache) (words : List (List Bool)) (stride frequency n : ℕ)
    (hs : c.stride=unary stride) (hf : c.frequency=unary frequency)
    (hn : c.count=unary n) (hc : c.words=vectorBits words) (tail : List Bool)
    (fuel : ℕ) (out : C.State Stack Label) (hr : C.run program fuel (initial c tail)=some out) :
    (∑k : Stack,(out.data k).length)+out.frames.length ≤
      23*(inputSize c+tail.length+10000*(inputSize c+1)^5) := by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (inputSize c+tail.length) _ out
    (by intro k;cases k <;> simp [initial,bank,inputSize] <;> omega) hr
  have hfuel:=prefix_fuel_le c words stride frequency n hs hf hn hc tail fuel out hr
  have hframe:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length ≤ 0+fuel at hframe
  have hsum : (∑k : Stack,(out.data k).length) ≤ 22*(inputSize c+tail.length+fuel) := by
    calc
      _ ≤ ∑_k : Stack,(inputSize c+tail.length+fuel) := Finset.sum_le_sum (fun k _=>hd k)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  omega

/-- The same every-prefix storage bound on the actual finite machine. -/
theorem machine_prefix_cells (c : Cache) (words : List (List Bool)) (stride frequency n : ℕ)
    (hs : c.stride=unary stride) (hf : c.frequency=unary frequency)
    (hn : c.count=unary n) (hc : c.words=vectorBits words) (tail : List Bool)
    (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial c tail)))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤
      23*(inputSize c+tail.length+10000*(inputSize c+1)^5) := by
  have he:=SemiprimeD1StackCalls.run_correct Stack.base Stack.output (.control .start) program fuel (initial c tail)
  change (C.run program fuel (initial c tail)).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial c tail))) at he
  have hh:=he.trans hr
  cases hrun:C.run program fuel (initial c tail) with
  | none => rw [hrun] at hh;cases hh
  | some out =>
    rw [hrun] at hh
    have hcfg : SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj hh
    subst cfg
    exact prefix_cells c words stride frequency n hs hf hn hc tail fuel out hrun

end RiemannGaussian.SemiprimeD1StackExprDotBounds
