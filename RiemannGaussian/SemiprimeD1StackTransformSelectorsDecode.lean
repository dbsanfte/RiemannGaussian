/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackTransformSelectorsPrimitives
/-! # Literal bounded physical unary constructor/transform decoding -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
namespace RiemannGaussian.SemiprimeD1StackTransformSelectorsDecode
open SemiprimeD1StackTransformSelectors SemiprimeD1StackTransformSelectorsPrimitives
open SemiprimeD1StackProcedureTrace
/-- Exactly n true markers are popped into fixed constructor control, retaining
an arbitrary copied suffix. False markers and overflow have literal abort branches. -/
theorem tag_prefix (n i : Nat) (hi:i+n<18) (tag tr tail : List Bool) :
    Runs program n (.tag ⟨i,by omega⟩) (data tag tr (List.replicate n true++tail) [] [] [])
      (.tag ⟨i+n,hi⟩) (data tag tr tail [] [] []) :=by
  induction n generalizing i with
  | zero=>simpa only [List.replicate_zero,List.nil_append,Nat.add_zero] using
      runs_refl program (.tag ⟨i,hi⟩) (data tag tr tail [] [] [])
  | succ n ih=>
    have hit:i<17:=by omega
    have hc:program (.tag ⟨i,by omega⟩)=.base (.pop .tagReader (tagDispatch ⟨i,by omega⟩)
      .abort (.tag ⟨i+1,by omega⟩)):=by simp only [program,nextTag,dite_eq_left hit]
    have h0:Runs program 1 (.tag ⟨i,by omega⟩) (data tag tr (List.replicate (n+1) true++tail) [] [] [])
      (.tag ⟨i+1,by omega⟩) (data tag tr (List.replicate n true++tail) [] [] []):=by
      apply one_base program _ _ (.pop .tagReader (tagDispatch ⟨i,by omega⟩) .abort (.tag ⟨i+1,by omega⟩)) _ _ hc
      · rfl
      · change Function.update (data tag tr (List.replicate (n+1) true++tail) [] [] []) .tagReader
          (List.replicate (n+1) true++tail).tail=_
        simp only [List.replicate_succ,List.cons_append,List.tail_cons]
        exact update_tagReader _ _ _ _ _ _ _
    have h1:=ih (i+1) (by omega)
    have he:(⟨i+1+n,by omega⟩:Fin 18)=⟨i+(n+1),hi⟩:=by apply Fin.ext;change i+1+n=i+(n+1);omega
    rw [he] at h1
    simpa only [show 1+n=n+1 by omega] using compose h0 h1
/-- Physical constructor EOF dispatch after every copied marker is consumed. -/
theorem tag_decode (n i : Nat) (hi:i+n<18) (tag tr : List Bool) :
    Runs program (n+1) (.tag ⟨i,by omega⟩) (data tag tr (List.replicate n true) [] [] [])
      (tagDispatch ⟨i+n,hi⟩) (data tag tr [] [] [] []) :=by
  have h0:=tag_prefix n i hi tag tr []
  simp only [List.append_nil] at h0
  have h1:Runs program 1 (.tag ⟨i+n,hi⟩) (data tag tr [] [] [] [])
      (tagDispatch ⟨i+n,hi⟩) (data tag tr [] [] [] []):=by
    apply one_base program _ _ (.pop .tagReader (tagDispatch ⟨i+n,hi⟩) .abort (nextTag ⟨i+n,hi⟩)) _ _ rfl
    · rfl
    · exact update_tagReader _ _ _ _ _ _ _
  exact compose h0 h1
/-- Exactly n true coord0 markers are physically popped into three-code control. -/
theorem transform_prefix (n i : Nat) (hi:i+n<3) (tag tr tail : List Bool) (second : Bool) :
    Runs program n (.transform second ⟨i,by omega⟩) (data tag tr [] (List.replicate n true++tail) [] [])
      (.transform second ⟨i+n,hi⟩) (data tag tr [] tail [] []) :=by
  induction n generalizing i with
  | zero=>simpa only [List.replicate_zero,List.nil_append,Nat.add_zero] using
      runs_refl program (.transform second ⟨i,hi⟩) (data tag tr [] tail [] [])
  | succ n ih=>
    have hit:i<2:=by omega
    have hc:program (.transform second ⟨i,by omega⟩)=.base (.pop .transformReader (transformDispatch second ⟨i,by omega⟩)
      .abort (.transform second ⟨i+1,by omega⟩)):=by simp only [program,nextTransform,dite_eq_left hit]
    have h0:Runs program 1 (.transform second ⟨i,by omega⟩) (data tag tr [] (List.replicate (n+1) true++tail) [] [])
      (.transform second ⟨i+1,by omega⟩) (data tag tr [] (List.replicate n true++tail) [] []):=by
      apply one_base program _ _ (.pop .transformReader (transformDispatch second ⟨i,by omega⟩)
        .abort (.transform second ⟨i+1,by omega⟩)) _ _ hc
      · rfl
      · change Function.update (data tag tr [] (List.replicate (n+1) true++tail) [] []) .transformReader
          (List.replicate (n+1) true++tail).tail=_
        simp only [List.replicate_succ,List.cons_append,List.tail_cons]
        exact update_transformReader _ _ _ _ _ _ _
    have h1:=ih (i+1) (by omega)
    have he:(⟨i+1+n,by omega⟩:Fin 3)=⟨i+(n+1),hi⟩:=by apply Fin.ext;change i+1+n=i+(n+1);omega
    rw [he] at h1
    simpa only [show 1+n=n+1 by omega] using compose h0 h1
/-- Physical coord0 EOF selects the inverse bit only after the complete copy
has been consumed; no singleton selector exists earlier in the store. -/
theorem transform_decode (n i : Nat) (hi:i+n<3) (tag tr : List Bool) (second : Bool) :
    Runs program (n+1) (.transform second ⟨i,by omega⟩) (data tag tr [] (List.replicate n true) [] [])
      (transformDispatch second ⟨i+n,hi⟩) (data tag tr [] [] [] []) :=by
  have h0:=transform_prefix n i hi tag tr [] second
  simp only [List.append_nil] at h0
  have h1:Runs program 1 (.transform second ⟨i+n,hi⟩) (data tag tr [] [] [] [])
      (transformDispatch second ⟨i+n,hi⟩) (data tag tr [] [] [] []):=by
    apply one_base program _ _ (.pop .transformReader (transformDispatch second ⟨i+n,hi⟩)
      .abort (nextTransform second ⟨i+n,hi⟩)) _ _ rfl
    · rfl
    · exact update_transformReader _ _ _ _ _ _ _
  exact compose h0 h1
end RiemannGaussian.SemiprimeD1StackTransformSelectorsDecode
