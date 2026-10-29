/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicTransformLoopState
/-! # Actual per-output dot and residue multiplication
The source/word/normalizer functions below are expected images of ACTUAL prior
acquisition. No evaluator or local-result/clock supplier is an executing input.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackPublicTransformQuery
open SemiprimeD1StackPublicTransform SemiprimeD1StackPublicTransformState
open SemiprimeD1StackPublicTransformWords SemiprimeD1StackPublicTransformGuards
open SemiprimeD1StackPublicTransformMetadata SemiprimeD1StackPublicTransformLoopState
open SemiprimeD1StackPublicTransformPrimitives SemiprimeD1StackProcedureTrace SemiprimeBitArithmetic
open SemiprimeD1StackUnaryDivmod (unary)
/-- Actual original dot expression, solely a correctness specification. -/
def dotExpression (bits raw : List Bool) (second inverse : Bool) (k : ℕ) : SemiprimeMacroEntryBitPrimitives.Expr :=
  SemiprimeD1StackDotEvaluateExecution.expression (expression bits inverse) (inputs (rootData bits) raw second)
    (size bits (!second)) k (size bits second)
/-- Actual computed dot bytes, never supplied numeric output. -/
def dotWord (bits raw : List Bool) (second inverse : Bool) (k : ℕ) : List Bool :=
  (SemiprimeMacroEntryBitPrimitives.execute (cached bits) (dotExpression bits raw second inverse k)).bits
/-- Actual state after the WHOLE dot call at frequency k. -/
def dotted (bits raw : List Bool) (second inverse : Bool) (k : ℕ) : Parts :=
  {steady bits raw second inverse k k with dot:=(SemiprimeD1StackDotEvaluateExecution.done
    (queryCache bits raw second inverse k) (cached bits) (expression bits inverse) (inputs (rootData bits) raw second)
      (size bits (!second)) k (size bits second) []).data}
/-- Actual dot-result preserving copy into the multiplier's second operand. -/
def dotCopied (bits raw : List Bool) (second inverse : Bool) (k : ℕ) : Parts := copied (dotted bits raw second inverse k) .dotOperand
/-- Every dot-result byte is physically drained before the next iteration. -/
def dotCleared (bits raw : List Bool) (second inverse : Bool) (k : ℕ) : Parts := set (dotCopied bits raw second inverse k) (.dot D.output) []
/-- Actual cached-normalizer copy into the multiplier's first operand. -/
def mulReady (bits raw : List Bool) (second inverse : Bool) (k : ℕ) : Parts := copied (dotCleared bits raw second inverse k) .normOperand
/-- Source validity is derived INSIDE the true actual input-guard branch; no
whole-source validity or canonical word family is an endpoint advice premise. -/
theorem dot_valid (bits raw : List Bool) (second inverse : Bool) (k : ℕ)
    (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (hg : inputFlag (rootData bits) raw second=true) :
    SemiprimeMacroEntryBitPrimitives.Valid (cached bits) (dotExpression bits raw second inverse k) := by
  obtain ⟨hm,hb⟩:=original_valid bits hc hN inverse
  exact SemiprimeD1StackGuardedDotExecution.expression_valid (cached bits) (expression bits inverse)
    (inputs (rootData bits) raw second) (size bits (!second)) k (size bits second) hm hb hg
/-- WHOLE dot source/evaluator executes on actual copied original caches and
actual produced input words, with every dynamic source byte retained in its cost. -/
theorem dot_call (bits raw : List Bool) (second inverse : Bool) (k : ℕ)
    (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (hg : inputFlag (rootData bits) raw second=true) :
    ∃t≤SemiprimeD1StackDotEvaluateExecution.timeBound (queryCache bits raw second inverse k) (cached bits)
      (expression bits inverse) (inputs (rootData bits) raw second) (size bits (!second)) k (size bits second)+1,
      Runs program t .evaluate (data (steady bits raw second inverse k k)) .copyDot
        (data (dotted bits raw second inverse k)) := by
  have hm:=(original_valid bits hc hN inverse).1
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackDotEvaluateExecution.source_run (queryCache bits raw second inverse k)
    (cached bits) (expression bits inverse) (source_code bits inverse) (inputs (rootData bits) raw second)
    (size bits (!second)) k (size bits second) (stride_unary bits second) rfl (count_unary bits second) rfl []
    (by omega) (dot_valid bits raw second inverse k hc hN hg)
  refine ⟨t+1,Nat.add_le_add_right ht 1,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program Stack.dot Label.dot
    (by intro i j h;exact Stack.dot.inj h) D.program .start (fun _=>rfl) .evaluate .copyDot rfl t
    (D.initial (queryCache bits raw second inverse k) (cached bits) [])
    (SemiprimeD1StackDotEvaluateExecution.done (queryCache bits raw second inverse k) (cached bits)
      (expression bits inverse) (inputs (rootData bits) raw second) (size bits (!second)) k (size bits second) [])
    _ _ rfl rfl rfl rfl hr
  · constructor
    · intro q;exact congrFun (steady_dot bits raw second inverse k k) q
    · intro q _;rfl
  · constructor
    · intro q;rfl
    · intro q hq;cases q <;> first | rfl | exact (hq _ rfl).elim
/-- Literal actual dot bytes are copied, without a numeric-result input. -/
theorem copy_dot (bits raw : List Bool) (second inverse : Bool) (k : ℕ) :
    Runs program (5*(dotWord bits raw second inverse k).length+4) .copyDot (data (dotted bits raw second inverse k))
      .clearDot (data (dotCopied bits raw second inverse k)) :=
  copy_run .dotOperand .copyDot .clearDot rfl (dotted bits raw second inverse k) rfl rfl
/-- Actual dynamic dot-result work is physically cleared. -/
theorem clear_dot (bits raw : List Bool) (second inverse : Bool) (k : ℕ) :
    Runs program ((dotWord bits raw second inverse k).length+1) .clearDot (data (dotCopied bits raw second inverse k))
      .copyNorm (data (dotCleared bits raw second inverse k)) := by
  have h:=drain .clearDot .copyNorm (.dot D.output) rfl (data (dotCopied bits raw second inverse k))
  have hv : data (dotCopied bits raw second inverse k) (.dot D.output)=dotWord bits raw second inverse k := rfl
  rw [hv,←data_set] at h;exact h
/-- Literal retained normalization WORD is copied for this actual multiply. -/
theorem copy_normalizer (bits raw : List Bool) (second inverse : Bool) (k : ℕ) :
    Runs program (5*(normalizer bits second inverse).length+4) .copyNorm (data (dotCleared bits raw second inverse k))
      .multiply (data (mulReady bits raw second inverse k)) :=
  copy_run .normOperand .copyNorm .multiply rfl (dotCleared bits raw second inverse k) rfl rfl
/-- Copied ACTUAL operands and cached M exactly form the multiplier's real input. -/
theorem multiplier_initial (bits raw : List Bool) (second inverse : Bool) (k : ℕ) :
    (mulReady bits raw second inverse k).multiplication=
      (M.initial (normalizer bits second inverse) (dotWord bits raw second inverse k) (cached bits)).data := by
  funext q
  rcases q with q|q
  · rcases q with q|q
    · cases q <;> rfl
    · rcases q with q|q
      · fin_cases q <;> rfl
      · cases q <;> rfl
  · rcases q with q|q
    · rcases q with q|q <;> cases q <;> rfl
    · cases q <;> rfl
/-- Actual postmultiply state, with its computed residue retained for comparison. -/
def multiplied (bits raw : List Bool) (second inverse : Bool) (k : ℕ) : Parts :=
  {mulReady bits raw second inverse k with multiplication:=
    (SemiprimeD1StackResidueMulExecution.done (normalizer bits second inverse) (dotWord bits raw second inverse k) (cached bits)).data}
/-- WHOLE real multiplier/divider executes; no product, residue or clock answer is
supplied. Its output is the actually computed modular normalization of the dot. -/
theorem multiply_call (bits raw : List Bool) (second inverse : Bool) (k : ℕ) :
    Runs program (SemiprimeD1StackResidueMulExecution.totalTime (normalizer bits second inverse) (dotWord bits raw second inverse k) (cached bits)+1)
      .multiply (data (mulReady bits raw second inverse k)) .copyProduct (data (multiplied bits raw second inverse k)) := by
  apply SemiprimeD1StackProcedureCallsTrace.included_call program Stack.multiply Label.multiplication
    (by intro i j h;exact Stack.multiply.inj h) M.program .start (fun _=>rfl) .multiply .copyProduct rfl
    (SemiprimeD1StackResidueMulExecution.totalTime (normalizer bits second inverse) (dotWord bits raw second inverse k) (cached bits))
    (M.initial (normalizer bits second inverse) (dotWord bits raw second inverse k) (cached bits))
    (SemiprimeD1StackResidueMulExecution.done (normalizer bits second inverse) (dotWord bits raw second inverse k) (cached bits))
    _ _ rfl rfl rfl rfl (SemiprimeD1StackResidueMulExecution.source_run _ _ _)
  · constructor
    · intro q;exact congrFun (multiplier_initial bits raw second inverse k) q
    · intro q _;rfl
  · constructor
    · intro q;rfl
    · intro q hq;cases q <;> first | rfl | exact (hq _ rfl).elim
end RiemannGaussian.SemiprimeD1StackPublicTransformQuery
