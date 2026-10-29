/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackVectorTableExecution
/-! # Complete same-source static-table time and every physical prefix cell -/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackVectorTableBounds
open SemiprimeD1StackVectorTable SemiprimeD1StackVectorTableSpec
open SemiprimeD1StackVectorTableExecution SemiprimeD1StackVectorTableDFS
open SemiprimeD1TensorTapeCodec (vectorBits tape)
variable {K L : Type} [DecidableEq K] [Fintype K] (s : Static K L)
/-- Every leaf's physical complete-vector payload is bounded by its proved actual source trace. -/
theorem answer_length (original : K→List Bool) (answer : List Bool→List (List Bool)) (budget : Nat→Nat)
    (hc : CheckerTrace s original answer budget) (raw : List Bool) :
    (vectorBits (answer raw)).length ≤ inputBytes original+raw.length+budget raw.length := by
  obtain ⟨t,ht,finish,_,_,hr,hv⟩ := hc raw
  have hh := output_cell_le s original raw t finish hr s.output
  rw [hv] at hh
  omega
/-- Whole physical tree bytes retain every bit of each actually produced word. -/
theorem tree_length (original : K→List Bool) (answer : List Bool→List (List Bool)) (budget : Nat→Nat)
    (hc : CheckerTrace s original answer budget) (front : List Bool) (n : Nat) :
    (tape (tree answer front n)).length+1 ≤
      (2*(inputBytes original+front.length+n+budget (front.length+n))+5)*2^n := by
  induction n generalizing front with
  | zero =>
    have hw := answer_length s original answer budget hc front
    rw [←SemiprimeD1StackVectorTableEmit.leaf_bytes,SemiprimeD1StackVectorTableEmit.leafBytes_length]
    simp only [Nat.add_zero,pow_zero,Nat.mul_one]
    omega
  | succ n ih =>
    have hl := ih (front++[false])
    have hr := ih (front++[true])
    change (true::(tape (tree answer (front++[false]) n)++tape (tree answer (front++[true]) n))).length+1 ≤ _
    have hfalse : (front++[false]).length+n=front.length+(n+1) := by simp only [List.length_append,List.length_singleton];omega
    have htrue : (front++[true]).length+n=front.length+(n+1) := by simp only [List.length_append,List.length_singleton];omega
    have hcf : inputBytes original+(front++[false]).length+n=inputBytes original+front.length+(n+1) := by
      simp only [List.length_append,List.length_singleton];omega
    have hct : inputBytes original+(front++[true]).length+n=inputBytes original+front.length+(n+1) := by
      simp only [List.length_append,List.length_singleton];omega
    rw [hfalse,hcf] at hl
    rw [htrue,hct] at hr
    simp only [List.length_cons,List.length_append,pow_succ,←Nat.mul_assoc]
    omega
/-- Every physical record contributes actual bytes, including an empty zero ID. -/
theorem scope_count_le (words : List (List Bool)) : words.length≤(vectorBits words).length := by
  induction words with
  | nil=>decide
  | cons w ws ih=>
    simp only [List.length_cons,vectorBits,SemiprimeSourceHistogramKeyBits.frame_length]
    omega
/-- Closed own source clock: physical scope bytes plus a fixed per-leaf
polynomial in original input, actual arity and PROVED checker bit time. -/
def runBound (original : K→List Bool) (words : List (List Bool)) (budget : Nat→Nat) : Nat :=
  (11*(vectorBits words).length+weight s original budget words.length+
    4*(inputBytes original+words.length+budget words.length)+40)*2^words.length
/-- Counter, every actual leaf/cleanup/return and complete physical final
reversal satisfy the same own source bound, without an old native report. -/
theorem timeBound_le (original : K→List Bool) (words : List (List Bool))
    (answer : List Bool→List (List Bool)) (budget : Nat→Nat) (hc : CheckerTrace s original answer budget) :
    timeBound s original words answer budget≤ runBound s original words budget := by
  have hcount:=SemiprimeD1StackDigitCountExecution.totalTime_le words
  have ht := tree_length s original answer budget hc [] words.length
  simp only [List.length_nil,Nat.zero_add,Nat.add_zero] at ht
  change (outputTape answer words).length+1 ≤ (2*(inputBytes original+words.length+budget words.length)+5)*2^words.length at ht
  have hp:1≤(2:Nat)^words.length:=by
    have h:0<(2:Nat)^words.length:=by positivity
    omega
  have hh:=Nat.mul_le_mul_left (11*(vectorBits words).length+12) hp
  simp only [Nat.mul_one] at hh
  unfold timeBound runBound
  nlinarith
/-- The complete proved source trace, using its own uniform whole-table clock. -/
theorem source_run_bounded (original : K→List Bool) (hraw : original s.raw=[])
    (answer : List Bool→List (List Bool)) (budget : Nat→Nat) (hc : CheckerTrace s original answer budget)
    (words : List (List Bool)) :
    ∃t≤ runBound s original words budget,C.run (program s) t (initial s original (vectorBits words))=
      some (done s original words answer) := by
  obtain ⟨t,ht,hr⟩:=source_run s original hraw answer budget hc words
  exact ⟨t,ht.trans (timeBound_le s original words answer budget hc),hr⟩
/-- Genuine fixed finite-machine time, with only original input template and
physical scope bytes initially present. No source evaluator or clock is run. -/
noncomputable def tableInTime [Fintype L] (original : K→List Bool) (hraw : original s.raw=[])
    (answer : List Bool→List (List Bool)) (budget : Nat→Nat) (hc : CheckerTrace s original answer budget)
    (words : List (List Bool)) :
    StateTransition.EvalsToInTime (machine s).step
      (SemiprimeD1StackCalls.configuration (initial s original (vectorBits words)))
      (some (SemiprimeD1StackCalls.configuration (done s original words answer))) (runBound s original words budget) := by
  apply SemiprimeD1StackCalls.evalsCorrect (counter .bank) (aux .output) .start (program s)
  let h:=source_run_bounded s original hraw answer budget hc words
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
omit [DecidableEq K] in
/-- Every initialized physical field is paid by template and actual scope bytes. -/
theorem initial_cell_le (original : K→List Bool) (bank : List Bool) (key : Stack K) :
    ((initial s original bank).data key).length≤ inputBytes original+bank.length := by
  rcases key with k|k
  · exact Nat.zero_le _
  · rcases k with k|k
    · have hs:(original k).length≤ inputBytes original:=by
        change (original k).length≤∑j:K,(original j).length
        exact Finset.single_le_sum (f:=fun j:K=>(original j).length) (fun _ _=>Nat.zero_le _) (Finset.mem_univ k)
      change (original k).length≤_
      omega
    · rcases k with k|k
      · cases k <;> simp [initial,data,store,D.data]
      · cases k <;> exact Nat.zero_le _
/-- Every successful physical prefix precedes this actual source's halt. -/
theorem prefix_fuel_le (original : K→List Bool) (hraw : original s.raw=[])
    (answer : List Bool→List (List Bool)) (budget : Nat→Nat) (hc : CheckerTrace s original answer budget)
    (words : List (List Bool)) (fuel : Nat) (finish : C.State (Stack K) (Label L s.roles.length))
    (hr : C.run (program s) fuel (initial s original (vectorBits words))=some finish) :
    fuel≤ runBound s original words budget := by
  obtain ⟨t,ht,he⟩:=source_run_bounded s original hraw answer budget hc words
  have hf:fuel≤ t:=by
    by_contra hn
    have hs:fuel=t+(1+(fuel-(t+1))):=by omega
    rw [hs,SemiprimeD1StackReturnLink.run_add,he,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
    have hz:C.run (program s) 1 (done s original words answer)=none:=rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans ht
/-- ALL checker AND read-only template roles, all7 count roles, all5 DFS roles
and every real nested return cell are bounded at EVERY actual prefix. -/
theorem prefix_cells (original : K→List Bool) (hraw : original s.raw=[])
    (answer : List Bool→List (List Bool)) (budget : Nat→Nat) (hc : CheckerTrace s original answer budget)
    (words : List (List Bool)) (fuel : Nat) (finish : C.State (Stack K) (Label L s.roles.length))
    (hr : C.run (program s) fuel (initial s original (vectorBits words))=some finish) :
    (∑k:Stack K,(finish.data k).length)+finish.frames.length≤
      (2*Fintype.card K+13)*(inputBytes original+(vectorBits words).length+runBound s original words budget+1) := by
  let I:=inputBytes original+(vectorBits words).length
  have hd:=SemiprimeD1StackReturnLink.run_data_bound (program s) fuel I _ finish
    (initial_cell_le s original (vectorBits words)) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound (program s) fuel _ finish hr
  change finish.frames.length≤0+fuel at hf
  have hs:(∑k:Stack K,(finish.data k).length)≤(2*Fintype.card K+12)*(I+fuel):=by
    calc
      _≤∑_k:Stack K,(I+fuel):=Finset.sum_le_sum (fun k _=>hd k)
      _= _:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel_le s original hraw answer budget hc words fuel finish hr
  have hmul:=Nat.mul_le_mul_left (2*Fintype.card K+13) ht
  dsimp [I] at hs
  nlinarith
/-- Every prefix of the ACTUAL compiled finite machine has the same complete
Boolean payload and real return-cell bound; no shadow/readonly role is omitted. -/
theorem machine_prefix_cells [Fintype L] (original : K→List Bool) (hraw : original s.raw=[])
    (answer : List Bool→List (List Bool)) (budget : Nat→Nat) (hc : CheckerTrace s original answer budget)
    (words : List (List Bool)) (fuel : Nat) (cfg : (machine s).Cfg)
    (hr : (fun q=>q.bind (machine s).step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial s original (vectorBits words))))=some cfg) :
    (∑k:Stack K,(cfg.stk (some k)).length)+(cfg.stk none).length≤
      (2*Fintype.card K+13)*(inputBytes original+(vectorBits words).length+runBound s original words budget+1) := by
  have he:=SemiprimeD1StackCalls.run_correct (counter .bank) (aux .output) .start (program s) fuel
    (initial s original (vectorBits words))
  have hh:(C.run (program s) fuel (initial s original (vectorBits words))).map
      SemiprimeD1StackCalls.configuration=some cfg:=he.trans hr
  cases hrun:C.run (program s) fuel (initial s original (vectorBits words)) with
  | none=>rw [hrun] at hh;cases hh
  | some finish=>
    rw [hrun] at hh
    have hcfg:SemiprimeD1StackCalls.configuration finish=cfg:=Option.some.inj hh
    subst cfg
    exact prefix_cells s original hraw answer budget hc words fuel finish hrun
/-- Every actual data and return alphabet is finite before any input. -/
theorem all_alphabets_finite [Fintype L] (k : (machine s).K) : Finite ((machine s).Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite (counter .bank) (aux .output) .start (program s) k
/-- Every included actual source instruction compiles to at most four
fundamental commands; static checker calls remain real physical calls. -/
theorem compile_depth [Fintype L] (pc : Label L s.roles.length) :
    SemiprimeD1StackBytecode.statementDepth ((machine s).m pc)≤4 :=
  SemiprimeD1StackCalls.compile_depth (.start : Label L s.roles.length) (program s pc)
end RiemannGaussian.SemiprimeD1StackVectorTableBounds
