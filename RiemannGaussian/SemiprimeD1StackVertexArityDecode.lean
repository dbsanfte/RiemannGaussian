/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackVertexArityCopies

/-! # Actual bounded unary constructor dispatch for original arity -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option synthInstance.maxSize 8192
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackVertexArityDecode
open SemiprimeD1StackVertexArity SemiprimeD1StackVertexArityView SemiprimeD1StackVertexArityCopies
open SemiprimeD1StackProcedureFragments (Runs one_base)
open SemiprimeD1StackUnaryDivmod (unary unary_succ)

/-- Literal finite next-decode continuation, independent of input dimensions. -/
def nextDecode (count:Fin 18) : Label :=
  if h:count.val<17 then .inl (.decode ⟨count.val+1,by omega⟩) else .inl .invalidClear
/-- Every unary tag marker is actually consumed, and the EOF selects its fixed recipe. -/
theorem decode_run (n i:ℕ) (hi:i+n<18) (h:Source→List Bool) (arity multiplier right limit result:List Bool) :
    Runs program (n+1) (.inl (.decode ⟨i,by omega⟩))
      (store h arity (unary n) multiplier right limit result) (recipe ⟨i+n,hi⟩)
      (store h arity [] multiplier right limit result) := by
  induction n generalizing i with
  | zero =>
    apply one_base program _ _ (.pop (aux .tagReader) (recipe ⟨i,by omega⟩)
      (nextDecode ⟨i,by omega⟩) (nextDecode ⟨i,by omega⟩)) _ _ rfl
    · rfl
    · change Function.update (data h (work arity [] multiplier right limit result)) (aux .tagReader) []=_
      rw [update_aux,work_tagReader]
      rfl
  | succ n ih =>
    have hit:i<17:=by omega
    have hc:program (.inl (.decode ⟨i,by omega⟩))=.base (.pop (aux .tagReader) (recipe ⟨i,by omega⟩)
        (.inl (.decode ⟨i+1,by omega⟩)) (.inl (.decode ⟨i+1,by omega⟩))):=by simp [program,hit]
    have h0:Runs program 1 (.inl (.decode ⟨i,by omega⟩)) (store h arity (unary (n+1)) multiplier right limit result)
        (.inl (.decode ⟨i+1,by omega⟩)) (store h arity (unary n) multiplier right limit result):=by
      apply one_base program _ _ (.pop (aux .tagReader) (recipe ⟨i,by omega⟩)
        (.inl (.decode ⟨i+1,by omega⟩)) (.inl (.decode ⟨i+1,by omega⟩))) _ _ hc
      · rfl
      · change Function.update (data h (work arity (unary (n+1)) multiplier right limit result))
          (aux .tagReader) (unary (n+1)).tail=_
        simp only [unary_succ,List.tail_cons]
        rw [update_aux,work_tagReader]
        rfl
    have h1:=ih (i+1) (by omega)
    have he:(⟨i+1+n,by omega⟩:Fin 18)=⟨i+(n+1),hi⟩:=by
      apply Fin.ext
      change i+1+n=i+(n+1)
      omega
    rw [he] at h1
    simpa only [show 1+(n+1)=n+1+1 by omega] using h0.trans h1

/-- Whole actual tag copy and bounded dispatch, before original arity arithmetic. -/
theorem tag_run (code:Fin 18) (index radius first second digits:ℕ) :
    Runs program (6*code.val+5) (.inl .main)
      (store (header code.val index radius first second digits) [] [] [] [] [] []) (recipe code)
      (store (header code.val index radius first second digits) [] [] [] [] [] []) := by
  have h0:=copy_tag code.val index radius first second digits [] [] [] [] [] [] (.inl .main) (.inl (.decode 0)) rfl
  rw [List.append_nil] at h0
  have h1:=decode_run code.val 0 (by omega) (header code.val index radius first second digits) [] [] [] [] []
  have he:(⟨0+code.val,by omega⟩:Fin 18)=code:=by
    apply Fin.ext
    change 0+code.val=code.val
    omega
  rw [he] at h1
  have h:=h0.trans h1
  convert h using 1;omega
end RiemannGaussian.SemiprimeD1StackVertexArityDecode
