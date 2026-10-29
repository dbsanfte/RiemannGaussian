/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortOwnerRecipeDecision
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
namespace RiemannGaussian.SemiprimeD1StackPortOwnerRecipeClassify
open SemiprimeD1StackPortOwnerRecipe SemiprimeD1StackPortOwnerRecipeSpec
open SemiprimeD1StackPortOwnerRecipeEmit SemiprimeD1StackPortOwnerRecipeDecision
open SemiprimeD1StackProcedureTrace (Runs one_base runs_trans)
open SemiprimeD1StackUnaryDivmod (unary)
/-- Literal store during physical consumption of the copied original tag field. -/
def store (p:Counters) (remaining:ℕ) : Stack→List Bool :=
  Function.update (prepared p) (reg .tagReader) (unary remaining)
/-- The actual acquired tag counter starts with its exact original bytes. -/
theorem store_initial (p:Counters) : store p p.tag=prepared p := by
  have he:prepared p (reg .tagReader)=unary p.tag:=rfl
  unfold store
  rw [←he]
  exact Function.update_eq_self _ _
/-- The original eight finite tags select exactly their original constructor branch. -/
theorem tagEnd_code (tag:Tag) : tagEnd (tagCode tag)=.local (.half tag) := by cases tag <;> rfl
/-- Every tag marker and the final EOF are physically consumed. -/
theorem classify_suffix (p:Counters) (tag:Tag) (remaining count:ℕ)
    (hc:count+remaining=(tagCode tag).val) :
    Runs program (remaining+1) (.local (.classify ⟨count,by omega⟩))
      (store p remaining) (.local (.half tag)) (ready p) := by
  induction remaining generalizing count with
  | zero=>
    have he:count=(tagCode tag).val:=by omega
    subst count
    change Runs program 1 (.local (.classify (tagCode tag))) (ready p) (.local (.half tag)) (ready p)
    apply one_base program _ _
      (.pop (reg .tagReader) (tagEnd (tagCode tag))
        (if h:(tagCode tag).val<17 then .local (.classify ⟨(tagCode tag).val+1,by omega⟩) else .local .abort)
        (if h:(tagCode tag).val<17 then .local (.classify ⟨(tagCode tag).val+1,by omega⟩) else .local .abort))
      _ _ rfl
    · change some (tagEnd (tagCode tag))=some (.local (.half tag))
      rw [tagEnd_code]
    · change Function.update (ready p) (reg .tagReader) []=ready p
      have hz:ready p (reg .tagReader)=[]:=Function.update_self _ _ _
      rw [←hz]
      exact Function.update_eq_self _ _
  | succ remaining ih=>
    have hcount:count<17:=by omega
    have hn:count+1+remaining=(tagCode tag).val:=by omega
    have hr:=ih (count+1) hn
    let j:Fin 18:=⟨count,by omega⟩
    let next:Label:=.local (.classify ⟨count+1,by omega⟩)
    have hp:program (.local (.classify j))=.base (.pop (reg .tagReader) (tagEnd j) next next):=by
      simp [program,j,next,hcount]
    have hs:Runs program 1 (.local (.classify j)) (store p (remaining+1)) next (store p remaining):=by
      apply one_base program _ _ (.pop (reg .tagReader) (tagEnd j) next next) _ _ hp
      · rfl
      · change Function.update (store p (remaining+1)) (reg .tagReader)
          ((store p (remaining+1)) (reg .tagReader)).tail=store p remaining
        unfold store
        rw [Function.update_self,Function.update_idem]
        rw [SemiprimeD1StackUnaryDivmod.unary_succ]
        rfl
    have h:=runs_trans program _ _ _ _ _ _ _ _ hs hr
    simpa only [j,next,show 1+(remaining+1)=remaining+1+1 by omega] using h
/-- Actual tag acquisition/classification, with at most eighteen literal reads. -/
theorem classify_run (p:Counters) (tag:Tag) (ht:p.tag=(tagCode tag).val) :
    Runs program (p.tag+1) (.local (.classify 0)) (prepared p) (.local (.half tag)) (ready p) := by
  have h:=classify_suffix p tag p.tag 0 (by omega)
  rw [store_initial] at h
  exact h
/-- Original tag cases are a proof-side observation of the acquired edge fields. -/
def originalTag {r t digits:ℕ} (e:SemiprimeMacroGraph.Edge r t digits) : Tag :=
  match e.1 with
  | .inl (.input _ _,_)=>.input
  | .inl (.first _ _ _,_)=>.first
  | .inl (.twiddle _ _ _,_)=>.twiddle
  | .inl (.second _ _ _,_)=>.second
  | .inl (.product _,_)=>.product
  | .inl (.carry _,_)=>.carry
  | .inr (.digit _ _)=>.digit
  | .inr (.orOut _ _)=>.orOut
/-- Every actual original edge produces one of the eight physically classified tag words. -/
theorem original_tag {r t digits:ℕ} (e:SemiprimeMacroGraph.Edge r t digits) :
    (original e).tag=(tagCode (originalTag e)).val := by
  rcases e with ⟨s,half⟩
  rcases s with ⟨w,bit⟩|flag
  · cases w <;> rfl
  · cases flag <;> rfl
end RiemannGaussian.SemiprimeD1StackPortOwnerRecipeClassify
