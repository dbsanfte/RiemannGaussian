/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRationalOperationEncoding
import RiemannGaussian.SemiprimeD1StackRationalOperationPrimitives
/-! # Actual shared-bank arithmetic, normalization and fitting calls -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRationalOperationCalls
open SemiprimeD1StackRationalOperation SemiprimeD1StackRationalOperationEncoding
open SemiprimeD1StackProcedureTrace
namespace P
export SemiprimeD1StackRationalOperationPrimitives (join copy_call push_run pop_run peek_run drain_loop)
end P
/-- Four real ripple operands replace the same four physical shared words. -/
def rippleReady (w:Words) (xs ys:List Bool) :Words:={w with left:=xs,right:=ys,scratch:=[],difference:=[]}
/-- A real ripple call consumes both operands and retains only its literal output. -/
def rippleDone (w:Words) (bits:List Bool) :Words:={w with left:=[],right:=[],scratch:=[],difference:=bits}
/-- Actual four-word adder call, with arbitrary other caller words and real returns retained. -/
theorem adder_call (w:Words) (xs ys:List Bool) (pc next:Label)
    (hc:program pc=.call (.adder (.start false)) next) :
    Runs program (3*(max xs.length ys.length+1)+2*(SemiprimeBitArithmetic.addBits xs ys false).bits.length+2+1)
      pc (bank (rippleReady w xs ys)) next (bank (rippleDone w (SemiprimeBitArithmetic.addBits xs ys false).bits)):=by
  apply included_call program adderStack Label.adder adder_injective A.code (.start false) (fun _=>rfl) pc next hc
    _ (SemiprimeD1StackAdder.state (some (.start false)) none xs ys [] [])
    (SemiprimeD1StackAdder.state none none [] [] [] (SemiprimeBitArithmetic.addBits xs ys false).bits)
    _ _ rfl rfl (SemiprimeD1StackAdderExecution.source_run xs ys false)
  · constructor
    · intro k;cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;cases k <;> rfl
    · intro k hk;rcases k with k|k
      · rcases k with k|k
        · rcases k with k|k
          · rcases k with k|k
            · cases k
              · exact (hk (.left) rfl).elim
              · exact (hk (.right) rfl).elim
              · exact (hk (.scratch) rfl).elim
              · exact (hk (.output) rfl).elim
            · cases k
              · rfl
              · rfl
              · rfl
              · rfl
              · rfl
              · rfl
              · rfl
          · cases k
            · rfl
            · rfl
            · rfl
            · rfl
            · rfl
            · rfl
            · rfl
        · cases k
          · rfl
          · rfl
          · rfl
          · rfl
      · rcases k with k|k
        · rcases k with k|k
          · fin_cases k
            · rfl
            · rfl
            · rfl
          · cases k
            · rfl
            · rfl
        · cases k
          · rfl
          · rfl
          · rfl
          · rfl
          · rfl
          · rfl
          · rfl
          · rfl
          · rfl

/-- Actual subtraction includes its physical borrow head; no comparison oracle is supplied. -/
theorem subtractor_call (w:Words) (xs ys:List Bool) (pc next:Label)
    (hc:program pc=.call (.subtractor (.start false)) next) :
    Runs program (3*(max xs.length ys.length+1)+2*(SemiprimeBitDivision.subBits xs ys false).result.bits.length+3+1)
      pc (bank (rippleReady w xs ys)) next
      (bank (rippleDone w ((SemiprimeBitDivision.subBits xs ys false).borrow::(SemiprimeBitDivision.subBits xs ys false).result.bits))):=by
  apply included_call program adderStack Label.subtractor adder_injective S.code (.start false) (fun _=>rfl) pc next hc
    _ (SemiprimeD1StackSubtractor.state (some (.start false)) none xs ys [] [])
    (SemiprimeD1StackSubtractor.state none none [] [] [] ((SemiprimeBitDivision.subBits xs ys false).borrow::(SemiprimeBitDivision.subBits xs ys false).result.bits))
    _ _ rfl rfl (SemiprimeD1StackSubtractorExecution.source_run xs ys false)
  · constructor
    · intro k;cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;cases k <;> rfl
    · intro k hk;rcases k with k|k
      · rcases k with k|k
        · rcases k with k|k
          · rcases k with k|k
            · cases k
              · exact (hk (.left) rfl).elim
              · exact (hk (.right) rfl).elim
              · exact (hk (.scratch) rfl).elim
              · exact (hk (.output) rfl).elim
            · cases k
              · rfl
              · rfl
              · rfl
              · rfl
              · rfl
              · rfl
              · rfl
          · cases k
            · rfl
            · rfl
            · rfl
            · rfl
            · rfl
            · rfl
            · rfl
        · cases k
          · rfl
          · rfl
          · rfl
          · rfl
      · rcases k with k|k
        · rcases k with k|k
          · fin_cases k
            · rfl
            · rfl
            · rfl
          · cases k
            · rfl
            · rfl
        · cases k
          · rfl
          · rfl
          · rfl
          · rfl
          · rfl
          · rfl
          · rfl
          · rfl
          · rfl

/-- Complete real multiplier initialization resets all nine actually aliased words. -/
def multiplyReady (w:Words) (xs ys:List Bool) :Words:=
  {w with left:=[],right:=[],scratch:=[],difference:=[],multFactor:=ys,multCopied:=[],multScratch:=[],multInput:=xs,multDigits:=[]}
/-- Complete real multiplier halt has only its raw accumulator nonempty in its nine-word bank. -/
def multiplyDone (w:Words) (bits:List Bool) :Words:=
  {w with left:=[],right:=bits,scratch:=[],difference:=[],multFactor:=[],multCopied:=[],multScratch:=[],multInput:=[],multDigits:=[]}
/-- Actual full multiplier call, preserving all27 other physical words and every outer return. -/
theorem multiplier_call (w:Words) (xs ys:List Bool) (pc next:Label)
    (hc:program pc=.call (.multiply (.control .start)) next) :
    Runs program (2*xs.length+1+SemiprimeD1StackMultiplierExecution.loopClock ys xs.reverse []+1)
      pc (bank (multiplyReady w xs ys)) next
      (bank (multiplyDone w (SemiprimeBitArithmetic.mulBits xs ys).bits)):=by
  apply SemiprimeD1StackProcedureCallsTrace.included_call program multiplierStack Label.multiply multiplier_injective M.code
    (.control .start) (fun _=>rfl) pc next hc _
    (SemiprimeD1StackMultiplier.state (some (.control .start)) none none xs ys [] [] [] [] [] [] [])
    (SemiprimeD1StackMultiplier.state none none none [] [] [] [] (SemiprimeBitArithmetic.mulBits xs ys).bits [] [] [] [])
    _ _ rfl rfl rfl rfl (SemiprimeD1StackMultiplierExecution.source_run xs ys)
  · constructor
    · intro k;rcases k with k|k
      · cases k <;> rfl
      · rcases k with k|k
        · fin_cases k <;> rfl
        · cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;rcases k with k|k
      · cases k <;> rfl
      · rcases k with k|k
        · fin_cases k <;> rfl
        · cases k <;> rfl
    · intro k hk;rcases k with k|k
      · rcases k with k|k
        · rcases k with k|k
          · rcases k with k|k
            · cases k
              · exact (hk (.inl (.left)) rfl).elim
              · exact (hk (.inl (.right)) rfl).elim
              · exact (hk (.inl (.scratch)) rfl).elim
              · exact (hk (.inl (.output)) rfl).elim
            · cases k
              · rfl
              · rfl
              · rfl
              · rfl
              · rfl
              · rfl
              · rfl
          · cases k
            · rfl
            · rfl
            · rfl
            · rfl
            · rfl
            · rfl
            · rfl
        · cases k
          · rfl
          · rfl
          · rfl
          · rfl
      · rcases k with k|k
        · rcases k with k|k
          · fin_cases k
            · exact (hk (.inr (.inl 0)) rfl).elim
            · exact (hk (.inr (.inl 1)) rfl).elim
            · exact (hk (.inr (.inl 2)) rfl).elim
          · cases k
            · exact (hk (.inr (.inr false)) rfl).elim
            · exact (hk (.inr (.inr true)) rfl).elim
        · cases k
          · rfl
          · rfl
          · rfl
          · rfl
          · rfl
          · rfl
          · rfl
          · rfl
          · rfl

/-- Every one of the22 normalization inputs is physically empty except acquired raw signed numerator and denominator. -/
def normalizeReady (w:Words) (signed den:List Bool) :Words:=
  {w with x:=[],y:=[],digits:=[],left:=[],right:=[],scratch:=[],difference:=[],remainder:=[],quotient:=[],copyScratch:=[],template:=[],originalLeft:=[],originalRight:=den,fuel:=[],scan:=[],next:=[],trimScratch:=[],output:=[],originalSigned:=signed,numeratorOutput:=[],denominatorOutput:=[],signOutput:=[]}
/-- Exact complete normalization bank; original raw words and sign remain until physically drained/fitted. -/
def normalizeDone (w:Words) (negative:Bool) (num den:List Bool) :Words:=
  {normalizeReady w (negative::num) den with
    signOutput:=[(SemiprimeD1StackRationalNormalizeSpec.word negative num den).numerator.negative],
    numeratorOutput:=(SemiprimeD1StackRationalNormalizeSpec.word negative num den).numerator.magnitude,
    denominatorOutput:=(SemiprimeD1StackRationalNormalizeSpec.word negative num den).denominator}
/-- Real Normalize22 call from its actually acquired two-word front door. -/
theorem normalize_call (w:Words) (negative:Bool) (num den:List Bool) (pc next:Label)
    (hc:program pc=.call (.normalize .start) next) :
    Runs program (SemiprimeD1StackRationalNormalizeExecution.runBound num den+1)
      pc (bank (normalizeReady w (negative::num) den)) next (bank (normalizeDone w negative num den)):=by
  apply SemiprimeD1StackProcedureCallsTrace.included_call program normalizeStack Label.normalize normalize_injective N.program
    .start (fun _=>rfl) pc next hc _ (SemiprimeD1StackRationalNormalize.initial (negative::num) den)
    (SemiprimeD1StackRationalNormalizeEncoding.done negative num den) _ _ rfl rfl rfl rfl
    (SemiprimeD1StackRationalNormalizeExecution.source_run negative num den)
  · constructor
    · intro k;rcases k with k|k
      · rcases k with k|k
        · rcases k with k|k <;> cases k <;> rfl
        · cases k <;> rfl
      · cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;rcases k with k|k
      · rcases k with k|k
        · rcases k with k|k <;> cases k <;> rfl
        · cases k <;> rfl
      · cases k <;> rfl
    · intro k hk;rcases k with k|k
      · exact (hk k rfl).elim
      · rcases k with k|k
        · rcases k with k|k
          · fin_cases k <;> rfl
          · cases k <;> rfl
        · cases k <;> rfl

/-- Actual fit input bank resets precisely its five distinct real roles. -/
def fitReady (w:Words) (den:Bool) (word cached:List Bool) :Words:=
  if den then {w with denominatorOutput:=word,templateInput:=cached,x:=[],y:=[],finalDenominator:=[]}
  else {w with numeratorOutput:=word,templateInput:=cached,x:=[],y:=[],finalNumerator:=[]}
/-- Actual fit consumes all original excess bytes and retains only template and exact fixed-width result. -/
def fitDone (w:Words) (den:Bool) (word cached:List Bool) :Words:=
  if den then {w with denominatorOutput:=[],templateInput:=cached,x:=[],y:=[],finalDenominator:=(SemiprimeBitDivision.fitBits word cached).bits}
  else {w with numeratorOutput:=[],templateInput:=cached,x:=[],y:=[],finalNumerator:=(SemiprimeBitDivision.fitBits word cached).bits}
/-- One real WordFit5 call; all31 other roles, including normalized sign, are preserved. -/
theorem fit_call (w:Words) (den:Bool) (word cached:List Bool) (pc next:Label)
    (hc:program pc=.call (.fit den .start) next) :
    Runs program (SemiprimeD1StackWordFitExecution.totalTime word cached+1)
      pc (bank (fitReady w den word cached)) next (bank (fitDone w den word cached)):=by
  apply SemiprimeD1StackProcedureCallsTrace.included_call program (fitStack den) (Label.fit den) (fit_injective den) F.program
    .start (fun _=>rfl) pc next hc _ (SemiprimeD1StackWordFit.initial word cached)
    (SemiprimeD1StackWordFitExecution.done word cached) _ _ rfl rfl rfl rfl
    (SemiprimeD1StackWordFitExecution.source_run word cached)
  · constructor
    · intro k;cases den <;> fin_cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;cases den <;> fin_cases k <;> rfl
    · intro k hk
      cases den with
      | false=>
        rcases k with k|k
        · rcases k with k|k
          · rcases k with k|k
            · rcases k with k|k
              · cases k
                · rfl
                · rfl
                · rfl
                · rfl
              · cases k
                · exact (hk ((2:Fin 5)) rfl).elim
                · exact (hk ((3:Fin 5)) rfl).elim
                · rfl
                · rfl
                · rfl
                · rfl
                · rfl
            · cases k
              · rfl
              · rfl
              · rfl
              · rfl
              · rfl
              · rfl
              · rfl
          · cases k
            · rfl
            · exact (hk ((0:Fin 5)) rfl).elim
            · rfl
            · rfl
        · rcases k with k|k
          · rcases k with k|k
            · fin_cases k
              · rfl
              · rfl
              · rfl
            · cases k
              · rfl
              · rfl
          · cases k
            · rfl
            · rfl
            · rfl
            · rfl
            · exact (hk ((1:Fin 5)) rfl).elim
            · rfl
            · rfl
            · exact (hk ((4:Fin 5)) rfl).elim
            · rfl
      | true=>
        rcases k with k|k
        · rcases k with k|k
          · rcases k with k|k
            · rcases k with k|k
              · cases k
                · rfl
                · rfl
                · rfl
                · rfl
              · cases k
                · exact (hk ((2:Fin 5)) rfl).elim
                · exact (hk ((3:Fin 5)) rfl).elim
                · rfl
                · rfl
                · rfl
                · rfl
                · rfl
            · cases k
              · rfl
              · rfl
              · rfl
              · rfl
              · rfl
              · rfl
              · rfl
          · cases k
            · rfl
            · rfl
            · exact (hk ((0:Fin 5)) rfl).elim
            · rfl
        · rcases k with k|k
          · rcases k with k|k
            · fin_cases k
              · rfl
              · rfl
              · rfl
            · cases k
              · rfl
              · rfl
          · cases k
            · rfl
            · rfl
            · rfl
            · rfl
            · exact (hk ((1:Fin 5)) rfl).elim
            · rfl
            · rfl
            · rfl
            · exact (hk ((4:Fin 5)) rfl).elim
end RiemannGaussian.SemiprimeD1StackRationalOperationCalls
