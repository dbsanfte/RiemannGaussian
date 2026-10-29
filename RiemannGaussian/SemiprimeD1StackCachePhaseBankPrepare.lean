/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackCachePhaseBankPrimitives
import RiemannGaussian.SemiprimeD1StackCachePhaseBankStopped
/-! # Both real retained-vector copies and one physical output sentinel
The copy scratch is derived empty from the actual initial callee bank; both
whole vectors remain retained and no count or phase cache is preinstalled.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackCachePhaseBankPrepare
open SemiprimeD1StackCachePhaseBank SemiprimeD1StackCachePhaseBankState
open SemiprimeD1StackCachePhaseBankPrimitives SemiprimeD1StackProcedureTrace
/-- Actual two preserving copies plus their real returns and literal false output seed. -/
def prepareTime (refs children:List Bool):Nat:=5*(refs.length+children.length)+9
/-- SAME four-input source physically prepares both readers, retaining all original words. -/
theorem prepare_run (hp cn refs children:List Bool):
    Runs program (prepareTime refs children) (.local .start) (initial hp cn refs children).data (.local .header)
      (data (P.input hp cn [] []) (words {references:=refs,children:=children,referenceReader:=refs,childReader:=children,output:=[false]})):=by
  rw [initial_data]
  let bank:=P.input hp cn [] []
  let v:Words:={references:=refs,children:=children}
  let copied:Words:={v with referenceReader:=refs}
  let both:Words:={copied with childReader:=children}
  have h0:=copy_call false .start .copyChildren rfl (data bank (words v)) refs [] rfl rfl rfl
  simp only [List.append_nil] at h0
  change Runs program _ _ _ _ (Function.update (data bank (words v)) (aux .referenceReader) refs) at h0
  rw [←data_update_aux,words_update] at h0
  have h1:=copy_call true .copyChildren .sentinel rfl (data bank (words copied)) children [] rfl rfl rfl
  simp only [List.append_nil] at h1
  change Runs program _ _ _ _ (Function.update (data bank (words copied)) (aux .childReader) children) at h1
  rw [←data_update_aux,words_update] at h1
  have h2:=push_run .sentinel (.local .header) output false (data bank (words both)) rfl
  change Runs program 1 _ _ _ (Function.update (data bank (words both)) (aux .output) [false]) at h2
  rw [←data_update_aux,words_update] at h2
  have h:=join (join h0 h1) h2
  have ht:prepareTime refs children=(5*refs.length+4)+(5*children.length+4)+1:=by
    unfold prepareTime
    omega
  rw [ht]
  exact h
end RiemannGaussian.SemiprimeD1StackCachePhaseBankPrepare
