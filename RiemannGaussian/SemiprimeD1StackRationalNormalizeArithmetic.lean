/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRationalNormalizeCalls
/-! # Two literal quotient phases reuse the complete actual Divider11 bank -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRationalNormalizeArithmetic
open SemiprimeD1StackRationalNormalize SemiprimeD1StackRationalNormalizeEncoding SemiprimeD1StackRationalNormalizeCalls
open SemiprimeD1StackProcedureTrace
/-- Real whole GCD call from the parsed two-word source boundary, including its caller return. -/
theorem gcd_ready (negative:Bool) (num den:List Bool) :
    Runs program (SemiprimeD1StackEuclidGCDExecution.runBound num den+1) .gcdCall (bank (parsed negative num den))
      (.copyInput false) (bank (ready negative num den (SemiprimeD1StackRationalNormalizeSpec.gcd num den) [] [])) :=by
  have h:=gcd_call (bank (parsed negative num den)) num den (by
    intro k;rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl)
  have he:Sum.elim (SemiprimeD1StackEuclidGCDEncoding.result num den)
      (fun k=>bank (parsed negative num den) (aux k))=
      bank (ready negative num den (SemiprimeD1StackRationalNormalizeSpec.gcd num den) [] []):=by
    funext k;rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  rw [he] at h
  exact h
/-- Every operand copy, restoring instruction, output copy, discarded remainder and erased quotient is counted. -/
def quotientTime (xs g:List Bool) :Nat:=
  (5*xs.length+4)+(5*g.length+4)+(SemiprimeD1StackDividerExecution.executionTime xs g+1)+
    (5*(SemiprimeBitDivision.divideLoop xs g).quotient.length+4)+
    ((SemiprimeBitDivision.divideLoop xs g).quotient.length+1)+((SemiprimeBitDivision.divideLoop xs g).remainder.length+1)
/-- Actual numerator quotient phase preserves all other source/sign/cache/output words. -/
theorem numerator_run (negative:Bool) (num den g n d:List Bool) :
    Runs program (quotientTime num g) (.copyInput false) (bank (ready negative num den g n d)) (.copyInput true)
      (bank {ready negative num den g n d with numeratorOutput:=(SemiprimeBitDivision.divideLoop num g).quotient++n}) :=by
  have h0:=P.copy_call .numeratorInput (.copyInput false) (.copyGcd false) rfl
    (bank (ready negative num den g n d)) num [] rfl rfl rfl
  change Runs _ _ _ _ _ (Function.update (bank _) (dividerStack (.inr .input)) (num++[])) at h0
  rw [List.append_nil,update_x] at h0
  have h1:=P.copy_call .gcdInput (.copyGcd false) (.divide false) rfl
    (bank {ready negative num den g n d with x:=num}) g [] rfl rfl rfl
  change Runs _ _ _ _ _ (Function.update (bank _) (dividerStack (.inr .divisor)) (g++[])) at h1
  rw [List.append_nil,update_y] at h1
  have h2:=divide_call false (bank {ready negative num den g n d with x:=num,y:=g}) num g
    (by intro k;rcases k with k|k <;> cases k <;> rfl)
  change Runs _ _ _ _ _ (Function.update (Function.update (Function.update (Function.update (bank _)
    (dividerStack (.inr .input)) []) (dividerStack (.inr .divisor)) []) (dividerStack (.inr .remainder)) _)
    (dividerStack (.inr .quotient)) _) at h2
  rw [update_x,update_y,update_remainder,update_quotient] at h2
  let quo:=(SemiprimeBitDivision.divideLoop num g).quotient
  let rem:=(SemiprimeBitDivision.divideLoop num g).remainder
  have h3:=P.copy_call .numeratorOutput (.save false) (.clearQuotient false) rfl
    (bank {ready negative num den g n d with quotient:=quo,remainder:=rem}) quo n rfl rfl rfl
  change Runs _ _ _ _ _ (Function.update (bank _) (aux .numeratorOutput) (quo++n)) at h3
  rw [update_numeratorOutput] at h3
  have h4:=P.drain_loop (.clearQuotient false) (.clearRemainder false) quotient rfl
    (bank {ready negative num den g n d with quotient:=quo,remainder:=rem,numeratorOutput:=quo++n}) quo rfl
  change Runs _ _ _ _ _ (Function.update (bank _) (dividerStack (.inr .quotient)) []) at h4
  rw [update_quotient] at h4
  have h5:=P.drain_loop (.clearRemainder false) (.copyInput true) remainder rfl
    (bank {ready negative num den g n d with remainder:=rem,numeratorOutput:=quo++n}) rem rfl
  change Runs _ _ _ _ _ (Function.update (bank _) (dividerStack (.inr .remainder)) []) at h5
  rw [update_remainder] at h5
  exact P.join (P.join (P.join (P.join (P.join h0 h1) h2) h3) h4) h5
/-- Actual denominator quotient phase preserves all other source/sign/cache/output words. -/
theorem denominator_run (negative:Bool) (num den g n d:List Bool) :
    Runs program (quotientTime den g) (.copyInput true) (bank (ready negative num den g n d)) .clearGcd
      (bank {ready negative num den g n d with denominatorOutput:=(SemiprimeBitDivision.divideLoop den g).quotient++d}) :=by
  have h0:=P.copy_call .denominatorInput (.copyInput true) (.copyGcd true) rfl
    (bank (ready negative num den g n d)) den [] rfl rfl rfl
  change Runs _ _ _ _ _ (Function.update (bank _) (dividerStack (.inr .input)) (den++[])) at h0
  rw [List.append_nil,update_x] at h0
  have h1:=P.copy_call .gcdInput (.copyGcd true) (.divide true) rfl
    (bank {ready negative num den g n d with x:=den}) g [] rfl rfl rfl
  change Runs _ _ _ _ _ (Function.update (bank _) (dividerStack (.inr .divisor)) (g++[])) at h1
  rw [List.append_nil,update_y] at h1
  have h2:=divide_call true (bank {ready negative num den g n d with x:=den,y:=g}) den g
    (by intro k;rcases k with k|k <;> cases k <;> rfl)
  change Runs _ _ _ _ _ (Function.update (Function.update (Function.update (Function.update (bank _)
    (dividerStack (.inr .input)) []) (dividerStack (.inr .divisor)) []) (dividerStack (.inr .remainder)) _)
    (dividerStack (.inr .quotient)) _) at h2
  rw [update_x,update_y,update_remainder,update_quotient] at h2
  let quo:=(SemiprimeBitDivision.divideLoop den g).quotient
  let rem:=(SemiprimeBitDivision.divideLoop den g).remainder
  have h3:=P.copy_call .denominatorOutput (.save true) (.clearQuotient true) rfl
    (bank {ready negative num den g n d with quotient:=quo,remainder:=rem}) quo d rfl rfl rfl
  change Runs _ _ _ _ _ (Function.update (bank _) (aux .denominatorOutput) (quo++d)) at h3
  rw [update_denominatorOutput] at h3
  have h4:=P.drain_loop (.clearQuotient true) (.clearRemainder true) quotient rfl
    (bank {ready negative num den g n d with quotient:=quo,remainder:=rem,denominatorOutput:=quo++d}) quo rfl
  change Runs _ _ _ _ _ (Function.update (bank _) (dividerStack (.inr .quotient)) []) at h4
  rw [update_quotient] at h4
  have h5:=P.drain_loop (.clearRemainder true) .clearGcd remainder rfl
    (bank {ready negative num den g n d with remainder:=rem,denominatorOutput:=quo++d}) rem rfl
  change Runs _ _ _ _ _ (Function.update (bank _) (dividerStack (.inr .remainder)) []) at h5
  rw [update_remainder] at h5
  exact P.join (P.join (P.join (P.join (P.join h0 h1) h2) h3) h4) h5
/-- Both actual private GCD bytes and the acquired magnitude are physically drained before halt. -/
theorem cleanup_run (negative:Bool) (num den g n d:List Bool) :
    Runs program ((g.length+1)+(num.length+1)) .clearGcd (bank (ready negative num den g n d)) .done
      (bank {originalSigned:=negative::num,originalRight:=den,signOutput:=[negative],numeratorOutput:=n,denominatorOutput:=d}) :=by
  have h0:=P.drain_loop .clearGcd .clearMagnitude gcdOutput rfl (bank (ready negative num den g n d)) g rfl
  change Runs _ _ _ _ _ (Function.update (bank _) (gcdStack (SemiprimeD1StackEuclidGCD.aux .output)) []) at h0
  rw [update_output] at h0
  have h1:=P.drain_loop .clearMagnitude .done numerator rfl (bank (ready negative num den [] n d)) num rfl
  change Runs _ _ _ _ _ (Function.update (bank _) (gcdStack (SemiprimeD1StackEuclidGCD.aux .left)) []) at h1
  rw [update_originalLeft] at h1
  exact P.join h0 h1
end RiemannGaussian.SemiprimeD1StackRationalNormalizeArithmetic
