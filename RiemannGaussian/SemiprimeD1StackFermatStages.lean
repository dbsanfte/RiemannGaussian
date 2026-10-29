/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackFermatLocal

/-! # Executed modulus and inverse construction from retained metadata -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackFermatStages
open SemiprimeD1StackFermatConstants SemiprimeD1StackFermatComponents SemiprimeD1StackFermatLocal
open SemiprimeD1StackProcedureFragments (Runs one_base)
namespace Words
export SemiprimeD1StackFermatWords (modulusWord normalizerWord)
end Words

/-- The radius copy executes against its retained source, with empty actual scratch. -/
theorem copy_radius (base:Meta.Stack→List Bool) (R:ℕ) (hr:base .radius=List.replicate R true)
    (modulus normalizer:List Bool) (pc next:Label)
    (hcall:program pc=.call (copyLabel false 0) next) :
    Runs program (5*R+4) pc (data base [] [] [] modulus normalizer) next
      (data base (List.replicate R true) [] [] modulus normalizer) := by
  have h:=copy_call false (data base [] [] [] modulus normalizer) rfl pc next hcall
  have hd:Function.update (data base [] [] [] modulus normalizer) (copyOutput false)
      ((data base [] [] [] modulus normalizer) (copyInput false)++
        (data base [] [] [] modulus normalizer) (copyOutput false))=
      data base (List.replicate R true) [] [] modulus normalizer:=by
    change Function.update (data base [] [] [] modulus normalizer) (.inl .squareWork)
      (base .radius++[]) = _
    rw [hr,List.append_nil]
    funext k;cases k with
    | inl k => cases k <;> simp [data,Function.update]
    | inr bit => cases bit <;> simp [data,Function.update]
  rw [hd] at h
  change Runs program (5*(base .radius).length+4) _ _ _ _ at h
  simpa only [hr,List.length_replicate] using h

/-- The exponent copy is likewise a real included call. -/
theorem copy_exponent (base:Meta.Stack→List Bool) (E:ℕ) (he:base .exponent=List.replicate E true)
    (rw modulus normalizer:List Bool) :
    Runs program (5*E+4) (.inl .normCopyE) (data base rw [] [] modulus normalizer) (.inl .normLoop)
      (data base rw (List.replicate E true) [] modulus normalizer) := by
  have h:=copy_call true (data base rw [] [] modulus normalizer) rfl (.inl .normCopyE) (.inl .normLoop) rfl
  have hd:Function.update (data base rw [] [] modulus normalizer) (copyOutput true)
      ((data base rw [] [] modulus normalizer) (copyInput true)++
        (data base rw [] [] modulus normalizer) (copyOutput true))=
      data base rw (List.replicate E true) [] modulus normalizer:=by
    change Function.update (data base rw [] [] modulus normalizer) (.inl .thresholdWork)
      (base .exponent++[]) = _
    rw [he,List.append_nil]
    funext k;cases k with
    | inl k => cases k <;> simp [data,Function.update]
    | inr bit => cases bit <;> simp [data,Function.update]
  rw [hd] at h
  change Runs program (5*(base .exponent).length+4) _ _ _ _ at h
  simpa only [he,List.length_replicate] using h

/-- A copied positive radius emits the complete canonical modulus word. -/
theorem modulus_run (base:Meta.Stack→List Bool) (n:ℕ)
    (hr:base .radius=List.replicate (n+1) true) :
    Runs program (7*(n+1)+6) (.inl .modStart) (data base [] [] [] [] []) (.inl .normStart)
      (data base [] [] [] (Words.modulusWord (n+1)) []) := by
  have h0:=copy_radius base (n+1) hr [] [] (.inl .modStart) (.inl .modDrop) rfl
  have h1:Runs program 1 (.inl .modDrop) (data base (true::List.replicate n true) [] [] [] []) (.inl .modHigh) (data base (List.replicate n true) [] [] [] []):=by
    apply one_base program _ _ (.pop (.inl .squareWork) (.inl .bad) (.inl .modHigh) (.inl .modHigh)) _ _ rfl
    · rfl
    · funext k;cases k with
      | inl k => cases k <;> simp [B.execute,data,Function.update]
      | inr bit => cases bit <;> simp [B.execute,data,Function.update]
  have h2:Runs program 1 (.inl .modHigh) (data base (List.replicate n true) [] [] [] []) (.inl .modLoop) (data base (List.replicate n true) [] [] [true] []):=by
    apply one_base program _ _ (.push (.inr false) true (.inl .modLoop)) _ _ rfl
    · rfl
    · funext k;cases k with
      | inl k => cases k <;> simp [B.execute,data,Function.update]
      | inr bit => cases bit <;> simp [B.execute,data,Function.update]
  have h3:=mod_zeros n base [] [] [true] []
  have h4:Runs program 1 (.inl .modLow) (data base [] [] [] (List.replicate n false++[true]) []) (.inl .normStart) (data base [] [] [] (true::(List.replicate n false++[true])) []):=by
    apply one_base program _ _ (.push (.inr false) true (.inl .normStart)) _ _ rfl
    · rfl
    · funext k;cases k with
      | inl k => cases k <;> simp [B.execute,data,Function.update]
      | inr bit => cases bit <;> simp [B.execute,data,Function.update]
  have h:=h0.trans (h1.trans (h2.trans (h3.trans h4)))
  simpa only [List.replicate_succ,Words.modulusWord,Nat.add_sub_cancel,
    show (5*(n+1)+4)+(1+(1+((2*n+1)+1)))=7*(n+1)+6 by omega] using h

/-- The actual exponent/radius cancellation emits the complete normalizer word. -/
theorem normalizer_run (base:Meta.Stack→List Bool) (E gap:ℕ)
    (hr:base .radius=List.replicate (E+gap+1) true)
    (he:base .exponent=List.replicate E true) (modulus:List Bool) :
    Runs program (7*(E+gap+1)+6*E+10) (.inl .normStart) (data base [] [] [] modulus []) (.inl .halt)
      (data base [] [] [] modulus (Words.normalizerWord (E+gap+1) E)) := by
  have h0:=copy_radius base (E+gap+1) hr modulus [] (.inl .normStart) (.inl .normDrop) rfl
  have h1:Runs program 1 (.inl .normDrop) (data base (true::List.replicate (E+gap) true) [] [] modulus []) (.inl .normCopyE) (data base (List.replicate (E+gap) true) [] [] modulus []):=by
    apply one_base program _ _ (.pop (.inl .squareWork) (.inl .bad) (.inl .normCopyE) (.inl .normCopyE)) _ _ rfl
    · rfl
    · funext k;cases k with
      | inl k => cases k <;> simp [B.execute,data,Function.update]
      | inr bit => cases bit <;> simp [B.execute,data,Function.update]
  have h2:=copy_exponent base E he (List.replicate (E+gap) true) modulus []
  have h3:=norm_pairs E gap base [] modulus []
  have h4:=norm_zeros gap base [] [] modulus (List.replicate E true++[])
  have h5:Runs program 1 (.inl .normLow) (data base [] [] [] modulus (List.replicate gap false++(List.replicate E true++[]))) (.inl .halt) (data base [] [] [] modulus (true::(List.replicate gap false++(List.replicate E true++[])))):=by
    apply one_base program _ _ (.push (.inr true) true (.inl .halt)) _ _ rfl
    · rfl
    · funext k;cases k with
      | inl k => cases k <;> simp [B.execute,data,Function.update]
      | inr bit => cases bit <;> simp [B.execute,data,Function.update]
  have h:=h0.trans (h1.trans (h2.trans (h3.trans (h4.trans h5))))
  have hg:E+gap+1-E-1=gap:=by omega
  simpa only [List.replicate_succ,Words.normalizerWord,hg,List.append_nil,
    show (5*(E+gap+1)+4)+(1+((5*E+4)+((3*E+1)+((2*gap+1)+1))))=
      7*(E+gap+1)+6*E+10 by omega] using h
end RiemannGaussian.SemiprimeD1StackFermatStages
