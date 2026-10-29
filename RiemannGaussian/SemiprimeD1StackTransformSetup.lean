/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackTransformComponents

/-! # Actual original-width threshold and initial dyadic acquisition
Sixteen literal Copy calls acquire16*WIDTH markers. Two real pushes then
initialize R and its square to one. No threshold/counter answer is supplied.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackTransformSetup
open SemiprimeD1StackTransform SemiprimeD1StackTransformComponents
open SemiprimeD1StackProcedureFragments (At Runs included_call one_base)

/-- Each fixed setup label below sixteen is an actual Copy call to its literal successor. -/
theorem setup_code (i:Fin 17) (hi:i.val<16) :
    program (setupLabel i)=.call (copyLabel 0 0) (setupLabel ⟨i.val+1,by omega⟩) := by
  simp only [program,setupLabel,hi,dite_true]

/-- Actual first k literal copies, with threshold markers acquired from WIDTH each time. -/
theorem threshold_prefix (bits:List Bool) (k:ℕ) (hk:k≤16) :
    Runs program (k*(5*bits.length+4)) (setupLabel 0) (data bits [] [] [] [] [] [] [] [])
      (setupLabel ⟨k,by omega⟩)
      (data bits (List.replicate (k*bits.length) true) [] [] [] [] [] [] []) := by
  induction k with
  | zero =>
    simp only [Nat.zero_mul,List.replicate_zero]
    convert Runs.refl program (setupLabel 0) (data bits [] [] [] [] [] [] [] []) using 1
    apply congrArg setupLabel
    apply Fin.ext
    rfl
  | succ k ih =>
    have hk0:k≤16:=by omega
    have hlt:k<16:=by omega
    have h0:=ih hk0
    have h1:=copy_call 0 (data bits (List.replicate (k*bits.length) true) [] [] [] [] [] [] []) rfl
      (setupLabel ⟨k,by omega⟩) (setupLabel ⟨k+1,by omega⟩) (setup_code ⟨k,by omega⟩ hlt)
    have hd:Function.update (data bits (List.replicate (k*bits.length) true) [] [] [] [] [] [] []) Stack.threshold
        (List.replicate bits.length true++List.replicate (k*bits.length) true)=
        data bits (List.replicate ((k+1)*bits.length) true) [] [] [] [] [] [] []:=by
      have hn:bits.length+k*bits.length=(k+1)*bits.length:=by ring
      funext stack
      cases stack <;> simp [data,Function.update,List.replicate_append_replicate,hn]
    simp only [copyInput,copyOutput,data,ite_true,List.length_replicate] at h1
    rw [hd] at h1
    have h:=h0.trans h1
    simpa only [Nat.succ_mul] using h

/-- Actual acquired threshold and two literal unit pushes, ready for the first comparison. -/
theorem threshold_initial (bits:List Bool) :
    Runs program (80*bits.length+66) (setupLabel 0) (data bits [] [] [] [] [] [] [] [])
      (.inl .copySquare) (data bits (List.replicate (16*bits.length) true) [true] [true] [] [] [] [] []) := by
  have h0:=threshold_prefix bits 16 (le_refl _)
  have h1:Runs program 1 (setupLabel 16)
      (data bits (List.replicate (16*bits.length) true) [] [] [] [] [] [] [])
      (.inl .initSquare) (data bits (List.replicate (16*bits.length) true) [true] [] [] [] [] [] []):=by
    apply one_base program _ _ (.push .radius true (.inl .initSquare)) _ _ rfl
    · rfl
    · funext k;cases k <;> simp [B.execute,data,Function.update]
  have h2:Runs program 1 (.inl .initSquare)
      (data bits (List.replicate (16*bits.length) true) [true] [] [] [] [] [] [])
      (.inl .copySquare) (data bits (List.replicate (16*bits.length) true) [true] [true] [] [] [] [] []):=by
    apply one_base program _ _ (.push .square true (.inl .copySquare)) _ _ rfl
    · rfl
    · funext k;cases k <;> simp [B.execute,data,Function.update]
  have h:=h0.trans (h1.trans h2)
  convert h using 1
  omega

/-- Original binary input alone acquires WIDTH, predicate, threshold, R and square. -/
theorem prepare (bits:List Bool) :
    Runs program (85*bits.length+71) (.inl .start) (input bits)
      (.inl .copySquare) (data bits (List.replicate (16*bits.length) true) [true] [true] [] [] [] [] []) := by
  have h:=(bootstrap_call bits).trans (threshold_initial bits)
  convert h using 1
  omega
end RiemannGaussian.SemiprimeD1StackTransformSetup
