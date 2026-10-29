/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryGridCalls
/-! # Physically acquired recovery-grid height -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryGridHeight
open SemiprimeD1StackRecoveryGrid SemiprimeD1StackRecoveryGridView SemiprimeD1StackRecoveryGridCalls
open SemiprimeD1StackProcedureTrace
/-- The six actual divider words, with both temporary words explicitly empty. -/
def words (w:Words) (input divisor quotient remainder:List Bool) :Words:=
  {w with division:=SemiprimeD1StackUnaryDivmod.contents input divisor [] [] quotient remainder}
/-- Actual input write in the complete six-word divider. -/
theorem update_input (w:Words) (input divisor quotient remainder xs:List Bool) :
    Function.update (bank (words w input divisor quotient remainder)) (divisionStack .input) xs=
      bank (words w xs divisor quotient remainder):=by
  rw [update_division]
  congr 1
  congr 1
  funext k
  cases k <;> simp [words,SemiprimeD1StackUnaryDivmod.contents]
/-- Actual divisor write in the complete six-word divider. -/
theorem update_divisor (w:Words) (input divisor quotient remainder xs:List Bool) :
    Function.update (bank (words w input divisor quotient remainder)) (divisionStack .divisor) xs=
      bank (words w input xs quotient remainder):=by
  rw [update_division]
  congr 1
  congr 1
  funext k
  cases k <;> simp [words,SemiprimeD1StackUnaryDivmod.contents]
/-- Actual quotient write in the complete six-word divider. -/
theorem update_quotient (w:Words) (input divisor quotient remainder xs:List Bool) :
    Function.update (bank (words w input divisor quotient remainder)) (divisionStack .quotient) xs=
      bank (words w input divisor xs remainder):=by
  rw [update_division]
  congr 1
  congr 1
  funext k
  cases k <;> simp [words,SemiprimeD1StackUnaryDivmod.contents]
/-- Actual remainder write in the complete six-word divider. -/
theorem update_remainder (w:Words) (input divisor quotient remainder xs:List Bool) :
    Function.update (bank (words w input divisor quotient remainder)) (divisionStack .remainder) xs=
      bank (words w input divisor quotient xs):=by
  rw [update_division]
  congr 1
  congr 1
  funext k
  cases k <;> simp [words,SemiprimeD1StackUnaryDivmod.contents]
/-- A genuinely restoring physical metadata copy prepends the acquired numerator bytes. -/
theorem input_copy (what:Copy) (pc next:Label) (hc:program pc=.call (.copier what 0) next)
    (ht:copyTarget what=divisionStack .input) (w:Words) (xs ys ds qs rs:List Bool)
    (hx:bank (words w ys ds qs rs) (copySource what)=xs) (hs:w.auxiliary .copyScratch=[]) :
    Runs program (5*xs.length+4) pc (bank (words w ys ds qs rs)) next
      (bank (words w (xs++ys) ds qs rs)):=by
  have hy:bank (words w ys ds qs rs) (copyTarget what)=ys:=by rw [ht];rfl
  have h:=PTrace.copy_call what pc next hc (bank (words w ys ds qs rs)) xs ys hx hy hs
  change Runs program (5*xs.length+4) pc _ next (Function.update _ (copyTarget what) (xs++ys)) at h
  rw [ht,update_input] at h
  exact h
/-- Three actual M copies and the one actual u copy precede the literal subtraction marker. -/
theorem numerator_run (w:Words) (M u:Nat)
    (hM:w.auxiliary .originalM=List.replicate M true)
    (hu:w.auxiliary .originalU=List.replicate u true) (hs:w.auxiliary .copyScratch=[]) :
    Runs program (3*(5*M+4)+(5*u+4)) (.local (.heightM 0)) (bank (words w [] [] [] []))
      (.local .minusOne) (bank (words w (List.replicate (3*M+u) true) [] [] [])):=by
  have h0:=input_copy .heightM (.local (.heightM 0)) (.local (.heightM 1)) rfl rfl w
    (List.replicate M true) [] [] [] [] hM hs
  have h1:=input_copy .heightM (.local (.heightM 1)) (.local (.heightM 2)) rfl rfl w
    (List.replicate M true) (List.replicate M true) [] [] [] hM hs
  have h2:=input_copy .heightM (.local (.heightM 2)) (.local .heightU) rfl rfl w
    (List.replicate M true) (List.replicate (2*M) true) [] [] [] hM hs
  have h3:=input_copy .heightU (.local .heightU) (.local .minusOne) rfl rfl w
    (List.replicate u true) (List.replicate (3*M) true) [] [] [] hu hs
  simp only [List.length_replicate,List.append_nil] at h0 h1 h2 h3
  rw [←List.replicate_add] at h1 h2 h3
  rw [show M+M=2*M by omega] at h1
  rw [show M+2*M=3*M by omega] at h2
  rw [show u+3*M=3*M+u by omega] at h3
  have h:=PTrace.join (PTrace.join (PTrace.join h0 h1) h2) h3
  simpa only [show 5*M+4+(5*M+4)+(5*M+4)+(5*u+4)=3*(5*M+4)+(5*u+4) by omega] using h
/-- Actual positive-u preparation physically removes one marker and copies the retained actual divisor. -/
theorem divide_input_run (w:Words) (M u:Nat)
    (hu:w.auxiliary .originalU=List.replicate (u+1) true) (hs:w.auxiliary .copyScratch=[]) :
    Runs program (1+(5*(u+1)+4)) (.local .minusOne)
      (bank (words w (List.replicate (3*M+(u+1)) true) [] [] [])) (.local .divide)
      (bank (words w (List.replicate (3*M+u) true) (List.replicate (u+1) true) [] [])):=by
  have h0:=PTrace.pop_run (.local .minusOne) (.local .abort) (.local .abort) (.local .divisor)
    (divisionStack .input) (bank (words w (List.replicate (3*M+(u+1)) true) [] [] []))
    (true::List.replicate (3*M+u) true) rfl (by change List.replicate (3*M+(u+1)) true=true::List.replicate (3*M+u) true;rw [show 3*M+(u+1)=(3*M+u)+1 by omega,List.replicate_succ])
  rw [update_input] at h0
  change Runs program 1 _ _ (.local .divisor) _ at h0
  have h1:=PTrace.copy_call .divisor (.local .divisor) (.local .divide) rfl
    (bank (words w (List.replicate (3*M+u) true) [] [] [])) (List.replicate (u+1) true) [] hu rfl hs
  change Runs program (5*(List.replicate (u+1) true).length+4) _ _ _
    (Function.update _ (divisionStack .divisor) (List.replicate (u+1) true++[])) at h1
  rw [List.append_nil,update_divisor] at h1
  simpa only [List.length_replicate] using PTrace.join h0 h1
/-- Both actual remainder and divisor tails, including their EOF branches, are physically discarded. -/
theorem cleanup_run (w:Words) (d q r:Nat) :
    Runs program ((r+1)+(d+1)) (.local .clearRemainder)
      (bank (words w [] (List.replicate d true) (List.replicate q true) (List.replicate r true)))
      (.local .node) (bank (words w [] [] (List.replicate q true) [])):=by
  have h0:=PTrace.drain_loop (.local .clearRemainder) (.local .clearDivisor) (divisionStack .remainder) rfl
    (bank (words w [] (List.replicate d true) (List.replicate q true) (List.replicate r true))) (List.replicate r true) rfl
  rw [update_remainder] at h0
  have h1:=PTrace.drain_loop (.local .clearDivisor) (.local .node) (divisionStack .divisor) rfl
    (bank (words w [] (List.replicate d true) (List.replicate q true) [])) (List.replicate d true) rfl
  rw [update_divisor] at h1
  simpa only [List.length_replicate] using PTrace.join h0 h1
/-- Honest actual source-byte height acquisition, with a physical zero-u branch. -/
theorem height_run (w:Words) (M u:Nat)
    (hM:w.auxiliary .originalM=List.replicate M true)
    (hu:w.auxiliary .originalU=List.replicate u true) (hs:w.auxiliary .copyScratch=[]) :
    ∃t≤1000*(M+u+1),Runs program t (.local .heightCheck) (bank (words w [] [] [] []))
      (.local .node) (bank (words w [] [] (List.replicate ((3*M+u-1)/u) true) [])):=by
  cases u with
  | zero=>
    have h:=PTrace.peek_run (.local .heightCheck) (.local .node) (.local .abort) (.local (.heightM 0))
      (aux .originalU) (bank (words w [] [] [] [])) [] rfl hu
    refine ⟨1,by omega,?_⟩
    change Runs program 1 _ _ (.local .node) _ at h
    simpa only [Nat.div_zero,List.replicate_zero] using h
  | succ u=>
    have h0:=PTrace.peek_run (.local .heightCheck) (.local .node) (.local .abort) (.local (.heightM 0))
      (aux .originalU) (bank (words w [] [] [] [])) (true::List.replicate u true) rfl
      (by change w.auxiliary .originalU=true::List.replicate u true;simpa only [List.replicate_succ] using hu)
    change Runs program 1 _ _ (.local (.heightM 0)) _ at h0
    have h1:=numerator_run w M (u+1) hM hu hs
    have h2:=divide_input_run w M u hu hs
    obtain ⟨q,hq,h3⟩:=division_call (words w (List.replicate (3*M+u) true) (List.replicate (u+1) true) [] [])
      (3*M+u) (u+1) rfl
    change Runs program q _ _ _
      (bank (words w [] (List.replicate (u+1) true) (List.replicate ((3*M+u)/(u+1)) true)
        (List.replicate ((3*M+u)%(u+1)) true))) at h3
    have h4:=cleanup_run w (u+1) ((3*M+u)/(u+1)) ((3*M+u)%(u+1))
    have h:=PTrace.join (PTrace.join (PTrace.join (PTrace.join h0 h1) h2) h3) h4
    refine ⟨1+(3*(5*M+4)+(5*(u+1)+4))+(1+(5*(u+1)+4))+q+
      (((3*M+u)%(u+1)+1)+(u+1+1)),?_,?_⟩
    · have hm:=Nat.mod_lt (3*M+u) (by omega :0<u+1)
      omega
    · simpa only [show 3*M+(u+1)-1=3*M+u by omega] using h
end RiemannGaussian.SemiprimeD1StackRecoveryGridHeight
