/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackGuardedDotEvaluate
/-! # Actual computed canonicality branch, then whole numerical dot execution -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 4096
namespace RiemannGaussian.SemiprimeD1StackGuardedDotExecution
open SemiprimeD1StackGuardedDotEvaluate SemiprimeD1StackProcedureTrace
open SemiprimeD1StackUnaryDivmod (unary)
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeMacroEntryBitPrimitives (Expr Valid)
/-- Actual guard's computed answer; never an initial runtime operand. -/
def answer (cached : List Bool) (words : List (List Bool)) : Bool :=
  SemiprimeD1StackVectorCanonicalExecution.answer cached words
/-- Exact reached store after the real guard, with the original dot inputs intact. -/
def afterGuard (c : D.Cache) (cached : List Bool) (words : List (List Bool)) (tail : List Bool) : Stack→List Bool :=
  store (D.initial c cached tail).data [answer cached words]
/-- Actual rejected halt, independent of every unevaluated base/metadata format. -/
def rejected (c : D.Cache) (cached tail : List Bool) : C.State Stack Label :=
  ⟨none,none,none,store (D.initial c cached tail).data [false],[]⟩
/-- Exact original successful dot result or untouched rejected input, chosen by
THE PHYSICALLY ACQUIRED guard Boolean rather than supplied canonicality advice. -/
def finalData (c : D.Cache) (cached : List Bool) (baseExpr : Expr) (words : List (List Bool))
    (stride frequency n : ℕ) (tail : List Bool) : Stack→List Bool :=
  store (if answer cached words then
    (SemiprimeD1StackDotEvaluateExecution.done c cached baseExpr words stride frequency n tail).data
    else (D.initial c cached tail).data) [answer cached words]
/-- Actual complete clean halt. -/
def done (c : D.Cache) (cached : List Bool) (baseExpr : Expr) (words : List (List Bool))
    (stride frequency n : ℕ) (tail : List Bool) : C.State Stack Label :=
  ⟨none,none,none,finalData c cached baseExpr words stride frequency n tail,[]⟩
/-- Only the EXECUTED true branch incurs a dot-source/evaluator bound. -/
def timeBound (c : D.Cache) (cached : List Bool) (baseExpr : Expr) (words : List (List Bool))
    (stride frequency n : ℕ) : ℕ :=
  SemiprimeD1StackVectorCanonicalExecution.timeBound words cached+
    (if answer cached words then SemiprimeD1StackDotEvaluateExecution.timeBound c cached baseExpr words stride frequency n else 0)+5
/-- Real whole guard shares the original SAME vector and binary modulus. -/
theorem guard_call (c : D.Cache) (cached : List Bool) (words : List (List Bool))
    (hc : c.words=vectorBits words) (tail : List Bool) :
    ∃t ≤ SemiprimeD1StackVectorCanonicalExecution.timeBound words cached+1,
      Runs program t .start (initial c cached tail).data .branch (afterGuard c cached words tail) := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackVectorCanonicalExecution.source_run words cached
  refine ⟨t+1,Nat.add_le_add_right ht 1,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program guardStack Label.check guard_injective
    V.program .start (fun _=>rfl) .start .branch rfl t
    (V.initial (vectorBits words) cached) (SemiprimeD1StackVectorCanonicalExecution.done words cached)
    _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k;cases k <;> first | rfl | exact hc
    · intro k _;rfl
  · constructor
    · intro k;cases k <;> first | rfl | exact hc
    · intro k hk;rcases k with k|k
      · rfl
      · cases k <;> first | rfl | exact (hk .output rfl).elim
/-- The ACTUAL guard bit is popped before any numerical source/evaluation call. -/
theorem branch_run (c : D.Cache) (cached : List Bool) (words : List (List Bool)) (tail : List Bool) :
    Runs program 1 .branch (afterGuard c cached words tail)
      (if answer cached words then .evaluate else .reject) (initial c cached tail).data := by
  apply one_base program .branch _ (.pop status .bad .reject .evaluate) _ _ rfl
  · change some (SemiprimeD1StackBytecode.choose Label.bad Label.reject Label.evaluate (some (answer cached words)))=some _
    cases answer cached words <;> rfl
  · change Function.update (afterGuard c cached words tail) status []=(initial c cached tail).data
    funext k;rcases k with k|k
    · rfl
    · cases k <;> rfl
/-- False is physically recorded without reading/evaluating base code or metadata. -/
theorem reject_run (c : D.Cache) (cached tail : List Bool) :
    Runs program 1 .reject (initial c cached tail).data .done (rejected c cached tail).data := by
  apply one_base program .reject .done (.push status false .done) _ _ rfl
  · rfl
  · change Function.update (initial c cached tail).data status [false]=(rejected c cached tail).data
    funext k;rcases k with k|k
    · rfl
    · cases k <;> rfl
/-- A failed actual guard closes with unchanged prepared inputs, EMPTY numerical
result and no canonicality, base validity, positivity or metadata-count premise. -/
theorem reject_source_run (c : D.Cache) (cached : List Bool) (words : List (List Bool))
    (hc : c.words=vectorBits words) (tail : List Bool) (ha : answer cached words=false) :
    ∃t ≤ SemiprimeD1StackVectorCanonicalExecution.timeBound words cached+4,
      C.run program t (initial c cached tail)=some (rejected c cached tail) := by
  obtain ⟨t,ht,h0⟩:=guard_call c cached words hc tail
  have h1:=branch_run c cached words tail
  rw [ha] at h1
  have h:=runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h0 h1) (reject_run c cached tail)
  obtain ⟨finish,hfinish,hout⟩:=h [] (initial c cached tail) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program .done rfl (rejected c cached tail).data [] finish hout
  refine ⟨t+1+1+1,by omega,?_⟩
  rw [SemiprimeD1StackReturnLink.run_add,hfinish,Option.bind_some,hh]
  rfl
/-- Every defaulted source word is canonical FROM THE COMPUTED GUARD. No
relation between term count and vector length is assumed; absent words are []=0. -/
theorem defaulted_canonical (cached : List Bool) (words : List (List Bool))
    (hm : 0<SemiprimeBitArithmetic.bitValue cached) (ha : answer cached words=true) (j : ℕ) :
    SemiprimeBitArithmetic.bitValue (SemiprimeD1StackExprDotSpec.wordAt words j)<SemiprimeBitArithmetic.bitValue cached := by
  have hw:=SemiprimeD1StackVectorCanonicalExecution.answer_true cached words |>.mp ha
  cases hg : words[j]? with
  | none=>simpa only [SemiprimeD1StackExprDotSpec.wordAt,hg,Option.getD_none,SemiprimeBitArithmetic.bitValue] using hm
  | some word=>
    have hj:=hw word (List.mem_of_getElem? hg)
    simpa only [SemiprimeD1StackExprDotSpec.wordAt,hg,Option.getD_some] using hj
/-- Whole-source validity is derived INTERNALLY, after the actual true guard. -/
theorem expression_valid (cached : List Bool) (baseExpr : Expr) (words : List (List Bool))
    (stride frequency n : ℕ) (hm : 1<SemiprimeBitArithmetic.bitValue cached)
    (hb : Valid cached baseExpr) (ha : answer cached words=true) :
    Valid cached (SemiprimeD1StackDotEvaluateExecution.expression baseExpr words stride frequency n) :=
  SemiprimeD1StackDotEvaluateExecution.expression_valid cached baseExpr words stride frequency n hm hb
    (fun j _=>defaulted_canonical cached words (by omega) ha j)
/-- Real whole source+evaluator call. Every word/whole-expression validity fact
is derived from the actual guard; only original base validity remains. -/
theorem dot_call (c : D.Cache) (cached : List Bool) (baseExpr : Expr)
    (hbase : c.base=SemiprimeD1StackExprCodec.encode baseExpr []) (words : List (List Bool))
    (stride frequency n : ℕ) (hs : c.stride=unary stride) (hf : c.frequency=unary frequency)
    (hn : c.count=unary n) (hc : c.words=vectorBits words) (tail : List Bool)
    (hm : 1<SemiprimeBitArithmetic.bitValue cached) (hb : Valid cached baseExpr) (ha : answer cached words=true) :
    ∃t ≤ SemiprimeD1StackDotEvaluateExecution.timeBound c cached baseExpr words stride frequency n+1,
      Runs program t .evaluate (initial c cached tail).data .accept
        (store (SemiprimeD1StackDotEvaluateExecution.done c cached baseExpr words stride frequency n tail).data []) := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackDotEvaluateExecution.source_run c cached baseExpr hbase words stride frequency n
    hs hf hn hc tail (by omega) (expression_valid cached baseExpr words stride frequency n hm hb ha)
  refine ⟨t+1,Nat.add_le_add_right ht 1,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program Sum.inl Label.dot Sum.inl_injective
    D.program .start (fun _=>rfl) .evaluate .accept rfl t (D.initial c cached tail)
    (SemiprimeD1StackDotEvaluateExecution.done c cached baseExpr words stride frequency n tail)
    _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk;rcases k with k|k
      · exact (hk k rfl).elim
      · rfl
/-- Successful completion physically pushes the true status only AFTER evaluation. -/
theorem accept_run (dot : D.Stack→List Bool) :
    Runs program 1 .accept (store dot []) .done (store dot [true]) := by
  apply one_base program .accept .done (.push status true .done) _ _ rfl
  · rfl
  · change Function.update (store dot []) status [true]=store dot [true]
    funext k;rcases k with k|k
    · rfl
    · cases k <;> rfl
/-- CLOSED computed-guard caller. No canonical input words, n=vector.length,
whole-expression validity, word/count/result/backend or clock advice is assumed. -/
theorem source_run (c : D.Cache) (cached : List Bool) (baseExpr : Expr)
    (hbase : c.base=SemiprimeD1StackExprCodec.encode baseExpr []) (words : List (List Bool))
    (stride frequency n : ℕ) (hs : c.stride=unary stride) (hf : c.frequency=unary frequency)
    (hn : c.count=unary n) (hc : c.words=vectorBits words) (tail : List Bool)
    (hm : 1<SemiprimeBitArithmetic.bitValue cached) (hb : Valid cached baseExpr) :
    ∃t ≤ timeBound c cached baseExpr words stride frequency n,
      C.run program t (initial c cached tail)=some (done c cached baseExpr words stride frequency n tail) := by
  cases ha : answer cached words with
  | false=>
    obtain ⟨t,ht,hr⟩:=reject_source_run c cached words hc tail ha
    refine ⟨t,?_,?_⟩
    · simp only [timeBound,ha,Bool.false_eq_true,ite_false];omega
    · simpa only [done,finalData,ha,Bool.false_eq_true,ite_false,rejected] using hr
  | true=>
    obtain ⟨t,ht,h0⟩:=guard_call c cached words hc tail
    have h1:=branch_run c cached words tail
    rw [ha] at h1
    obtain ⟨m,hmul,h2⟩:=dot_call c cached baseExpr hbase words stride frequency n hs hf hn hc tail hm hb ha
    have h3:=accept_run (SemiprimeD1StackDotEvaluateExecution.done c cached baseExpr words stride frequency n tail).data
    have h:=runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2) h3
    obtain ⟨finish,hfinish,hout⟩:=h [] (initial c cached tail) ⟨rfl,rfl,rfl⟩
    have hh:=halt_run program .done rfl
      (store (SemiprimeD1StackDotEvaluateExecution.done c cached baseExpr words stride frequency n tail).data [true]) [] finish hout
    refine ⟨t+1+m+1+1,?_,?_⟩
    · simp only [timeBound,ha,ite_true];omega
    · rw [SemiprimeD1StackReturnLink.run_add,hfinish,Option.bind_some,hh]
      simp only [done,finalData,ha,ite_true]
/-- The status is exactly the actual canonical-vector guard's computed verdict. -/
theorem status_original (c : D.Cache) (cached : List Bool) (baseExpr : Expr) (words : List (List Bool))
    (stride frequency n : ℕ) (tail : List Bool) :
    (done c cached baseExpr words stride frequency n tail).data status=[answer cached words] := rfl
/-- Success has literally the original numerical execute bytes, rejection has NONE. -/
theorem output_original (c : D.Cache) (cached : List Bool) (baseExpr : Expr) (words : List (List Bool))
    (stride frequency n : ℕ) (tail : List Bool) :
    (done c cached baseExpr words stride frequency n tail).data output=
      if answer cached words then (SemiprimeMacroEntryBitPrimitives.execute cached
        (SemiprimeD1StackDotEvaluateExecution.expression baseExpr words stride frequency n)).bits else [] := by
  cases ha : answer cached words <;>
    simp only [done,finalData,ha,Bool.false_eq_true,ite_false,ite_true,store,output,Sum.elim_inl] <;> rfl
/-- Every non-result original dot input/work role has the exact initial payload;
this simultaneously preserves all caches/suffix/modulus and clears all dot work. -/
theorem dot_cleanup (c : D.Cache) (cached : List Bool) (baseExpr : Expr) (words : List (List Bool))
    (stride frequency n : ℕ) (tail : List Bool) (k : D.Stack) (hk : k≠D.output) :
    (done c cached baseExpr words stride frequency n tail).data (.inl k)=(D.initial c cached tail).data k := by
  cases ha : answer cached words with
  | false=>simp only [done,finalData,ha,Bool.false_eq_true,ite_false,store,Sum.elim_inl]
  | true=>
    simp only [done,finalData,ha,ite_true,store,Sum.elim_inl]
    rcases k with k|k
    · rfl
    · cases k <;> first | rfl | exact (hk rfl).elim
/-- All guard parser/comparison/shadow roles are empty except the final status. -/
theorem guard_cleanup (c : D.Cache) (cached : List Bool) (baseExpr : Expr) (words : List (List Bool))
    (stride frequency n : ℕ) (tail : List Bool) (k : V.Stack) (hk : k≠.output) :
    (done c cached baseExpr words stride frequency n tail).data (.inr k)=[] := by
  simp only [done,finalData,store,Sum.elim_inr,flags,ite_eq_right_iff]
  exact fun h=>False.elim (hk h)
end RiemannGaussian.SemiprimeD1StackGuardedDotExecution
