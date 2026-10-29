/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceAlphabet64Primitives
/-! # Real fixed six-bit colour-block parsing, with no numeric coordinate callback -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceAlphabet64Digits
open SemiprimeD1StackSourceAlphabet64 SemiprimeD1StackSourceAlphabet64Primitives
open SemiprimeD1StackProcedureTrace
/-- The bounded control physically consumes exactly its remaining block bits,
reversing them onto the actual colour word while preserving the unread tail. -/
theorem read_colour (n:Nat) (i:Fin 7) (hi:i.val+n=6) (bank:Stack→List Bool) (bits tail:List Bool)
    (hlen:bits.length=n) (hbits:bank (aux .bitsReverse)=bits++tail) :
    Runs program (2*n+1) (.readColour i) bank .reverseColour
      (Function.update (Function.update bank (aux .bitsReverse) tail) (aux .colourRaw)
        (bits.reverse++bank (aux .colourRaw))) :=by
  induction n generalizing i bank bits with
  | zero=>
    have hi':¬i.val<6:=by omega
    have hb:bits=[]:=List.length_eq_zero_iff.mp hlen
    subst bits
    have he:Function.update (Function.update bank (aux .bitsReverse) tail) (aux .colourRaw)
        ([].reverse++bank (aux .colourRaw))=bank:=by
      simp only [List.reverse_nil,List.nil_append] at hbits ⊢
      rw [←hbits,Function.update_eq_self,Function.update_eq_self]
    rw [he]
    apply one_base program _ _ (.jump .reverseColour) _ _ (by simp only [program,dite_eq_right hi'])
    · rfl
    · rfl
  | succ n ih=>
    cases bits with
    | nil=>simp only [List.length_nil] at hlen;omega
    | cons b bits=>
      have hi':i.val<6:=by omega
      let j:Fin 7:=⟨i.val+1,by omega⟩
      let p:=Function.update bank (aux .bitsReverse) (bits++tail)
      let q:=Function.update p (aux .colourRaw) (b::bank (aux .colourRaw))
      have h0:Runs program 1 (.readColour i) bank (.saveColour ⟨i.val,hi'⟩ b) p:=by
        apply one_base program _ _ (.pop (aux .bitsReverse) .abort
          (.saveColour ⟨i.val,hi'⟩ false) (.saveColour ⟨i.val,hi'⟩ true)) _ _
          (by simp only [program,dite_eq_left hi'])
        · cases b <;> simp [SemiprimeD1StackBytecode.execute,SemiprimeD1StackBytecode.choose,hbits]
        · simp [SemiprimeD1StackBytecode.execute,hbits,p]
      have h1:Runs program 1 (.saveColour ⟨i.val,hi'⟩ b) p (.readColour j) q:=by
        apply one_base program _ _ (.push (aux .colourRaw) b (.readColour j)) _ _ rfl
        · rfl
        · change Function.update p (aux .colourRaw) (b::p (aux .colourRaw))=q
          dsimp only [p,q]
          rw [Function.update_of_ne (by decide:aux .colourRaw≠aux .bitsReverse)]
      have hq:q (aux .bitsReverse)=bits++tail:=by simp [q,p,aux]
      have h2:=ih j (by dsimp only [j];omega) q bits (by simp only [List.length_cons] at hlen;omega) hq
      have he:Function.update (Function.update q (aux .bitsReverse) tail) (aux .colourRaw)
          (bits.reverse++q (aux .colourRaw))=
        Function.update (Function.update bank (aux .bitsReverse) tail) (aux .colourRaw)
          ((b::bits).reverse++bank (aux .colourRaw)):=by
        funext k
        by_cases hk:k=aux .bitsReverse
        · subst k;simp [q,p,aux]
        · by_cases hk':k=aux .colourRaw
          · subst k;simp [q,p,aux,List.reverse_cons,List.append_assoc]
          · simp [q,p,Function.update_of_ne hk,Function.update_of_ne hk']
      rw [he] at h2
      have h:=compose (compose h0 h1) h2
      simpa only [show 1+1+(2*n+1)=2*(n+1)+1 by omega] using h
end RiemannGaussian.SemiprimeD1StackSourceAlphabet64Digits
