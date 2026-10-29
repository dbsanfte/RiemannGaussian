/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackDotEvaluate

/-! # Whole acquired dot execution
Both included traces are complete fixed programs. The first creates the actual
syntax; the second consumes that same physical stack and returns original bytes.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackDotEvaluateExecution
open SemiprimeD1StackDotEvaluate SemiprimeD1StackProcedureTrace
open SemiprimeD1StackUnaryDivmod (unary)
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeMacroEntryBitPrimitives (Expr Valid dotExpr dotExpr_valid)

/-- Original dot expression, used only in the correctness specification. -/
def expression (baseExpr : Expr) (words : List (List Bool)) (stride frequency n : ℕ) : Expr :=
  dotExpr baseExpr stride frequency (SemiprimeD1StackExprDotSpec.wordAt words) n
/-- Actual physical payload after the whole source call, before execution. -/
def afterSource (c : D.Cache) (cached : List Bool) (words : List (List Bool))
    (stride frequency n : ℕ) (tail : List Bool) : Stack→List Bool :=
  store c (SemiprimeD1StackExprDotSpec.result n c.base words stride frequency tail) (E.input [] cached)
/-- Exact clean final state; all original caches, binary modulus and suffix remain. -/
def done (c : D.Cache) (cached : List Bool) (baseExpr : Expr) (words : List (List Bool))
    (stride frequency n : ℕ) (tail : List Bool) : C.State Stack Label :=
  ⟨none,none,none,store c tail
    (SemiprimeD1StackExprExecution.finalData cached (expression baseExpr words stride frequency n) []),[]⟩

/-- Real whole source call with every metadata and selected-word operation retained. -/
theorem source_call (c : D.Cache) (cached : List Bool) (words : List (List Bool)) (stride frequency n : ℕ)
    (hs : c.stride=unary stride) (hf : c.frequency=unary frequency)
    (hn : c.count=unary n) (hc : c.words=vectorBits words) (tail : List Bool) :
    ∃m ≤ SemiprimeD1StackExprDotExecution.timeBound c words stride frequency n,
      Runs program (m+1) .start (initial c cached tail).data .evaluate
        (afterSource c cached words stride frequency n tail) := by
  obtain ⟨m,hm,hr⟩:=SemiprimeD1StackExprDotExecution.source_run c words stride frequency n hs hf hn hc tail
  refine ⟨m,hm,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program Sum.inl Label.source Sum.inl_injective
    D.program (.control .start) (fun _=>rfl) .start .evaluate rfl m (D.initial c tail)
    (SemiprimeD1StackExprDotExecution.done c words stride frequency n tail)
    (initial c cached tail).data (afterSource c cached words stride frequency n tail)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k
      · exact False.elim (hk k rfl)
      · rfl

/-- Original positivity and input canonicality imply the whole acquired source is
valid; no executed child answer or intermediate width is assumed. -/
theorem expression_valid (cached : List Bool) (baseExpr : Expr) (words : List (List Bool))
    (stride frequency n : ℕ) (hm : 1<SemiprimeBitArithmetic.bitValue cached) (hb : Valid cached baseExpr)
    (hw : ∀j<n,SemiprimeBitArithmetic.bitValue (SemiprimeD1StackExprDotSpec.wordAt words j)<
      SemiprimeBitArithmetic.bitValue cached) :
    Valid cached (expression baseExpr words stride frequency n) :=
  dotExpr_valid cached hm baseExpr hb stride frequency n _ hw

/-- The evaluator consumes precisely the code physically created by the source
call. Only original expression validity is needed for its completed trace. -/
theorem evaluate_call (c : D.Cache) (cached : List Bool) (baseExpr : Expr)
    (hbase : c.base=SemiprimeD1StackExprCodec.encode baseExpr []) (words : List (List Bool))
    (stride frequency n : ℕ) (tail : List Bool)
    (hm : 0<SemiprimeBitArithmetic.bitValue cached)
    (hv : Valid cached (expression baseExpr words stride frequency n)) :
    Runs program (SemiprimeD1StackExprExecution.totalTime cached (expression baseExpr words stride frequency n)+1)
      .evaluate (afterSource c cached words stride frequency n tail) .done
      (done c cached baseExpr words stride frequency n tail).data := by
  have hsyntax : SemiprimeD1StackExprDotSpec.result n c.base words stride frequency tail=
      SemiprimeD1StackExprCodec.encode (expression baseExpr words stride frequency n) tail := by
    rw [hbase]
    exact SemiprimeD1StackExprDotSpec.result_original baseExpr words stride frequency n tail
  apply SemiprimeD1StackProcedureCallsTrace.included_call program expressionStack Label.expression expressionStack_injective
    E.program .start (fun _=>rfl) .evaluate .done rfl
    (SemiprimeD1StackExprExecution.totalTime cached (expression baseExpr words stride frequency n))
    (E.initial (SemiprimeD1StackExprCodec.encode (expression baseExpr words stride frequency n) tail) cached)
    (SemiprimeD1StackExprExecution.done cached (expression baseExpr words stride frequency n) tail)
    (afterSource c cached words stride frequency n tail) (done c cached baseExpr words stride frequency n tail).data
  · rfl
  · rfl
  · rfl
  · rfl
  · exact SemiprimeD1StackExprExecution.source_run cached _ tail hm hv
  · constructor
    · intro k;cases k <;> simp [expressionStack,code,afterSource,store,E.initial,E.input,E.bank,D.bank,hsyntax]
    · intro k _;rfl
  · constructor
    · intro k;cases k <;> rfl
    · intro k hk
      rcases k with k|k
      · cases k <;> first | rfl | exact False.elim (hk .code rfl)
      · cases k <;> first | rfl | exact False.elim (hk .result rfl)

/-- Own complete-program budget, including both real calls and final halt. -/
def timeBound (c : D.Cache) (cached : List Bool) (baseExpr : Expr) (words : List (List Bool))
    (stride frequency n : ℕ) : ℕ :=
  SemiprimeD1StackExprDotExecution.timeBound c words stride frequency n+
    SemiprimeD1StackExprExecution.totalTime cached (expression baseExpr words stride frequency n)+3

/-- COMPLETE original dot execution from original prepared physical caches and
binary modulus. The original AST appears only in the proved semantic equality. -/
theorem source_run (c : D.Cache) (cached : List Bool) (baseExpr : Expr)
    (hbase : c.base=SemiprimeD1StackExprCodec.encode baseExpr []) (words : List (List Bool))
    (stride frequency n : ℕ) (hs : c.stride=unary stride) (hf : c.frequency=unary frequency)
    (hn : c.count=unary n) (hc : c.words=vectorBits words) (tail : List Bool)
    (hm : 0<SemiprimeBitArithmetic.bitValue cached)
    (hv : Valid cached (expression baseExpr words stride frequency n)) :
    ∃t ≤ timeBound c cached baseExpr words stride frequency n,
      C.run program t (initial c cached tail)=some (done c cached baseExpr words stride frequency n tail) := by
  obtain ⟨m,hmul,h0⟩:=source_call c cached words stride frequency n hs hf hn hc tail
  have h1:=evaluate_call c cached baseExpr hbase words stride frequency n tail hm hv
  have h:=runs_trans program _ _ _ _ _ _ _ _ h0 h1
  obtain ⟨finish,hr,ho⟩:=h [] (initial c cached tail) ⟨rfl,rfl,rfl⟩
  have he:=halt_run program .done rfl (done c cached baseExpr words stride frequency n tail).data [] finish ho
  refine ⟨(m+1)+(SemiprimeD1StackExprExecution.totalTime cached (expression baseExpr words stride frequency n)+1)+1,?_,?_⟩
  · unfold timeBound
    omega
  · rw [SemiprimeD1StackReturnLink.run_add,hr,Option.bind_some,he]
    rfl

/-- Exact original numerical output, including the original physical padding. -/
theorem output_original (c : D.Cache) (cached : List Bool) (baseExpr : Expr)
    (words : List (List Bool)) (stride frequency n : ℕ) (tail : List Bool) :
    (done c cached baseExpr words stride frequency n tail).data output=
      (SemiprimeMacroEntryBitPrimitives.execute cached (expression baseExpr words stride frequency n)).bits := rfl

end RiemannGaussian.SemiprimeD1StackDotEvaluateExecution
