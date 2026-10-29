/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortOwnerRecipeCalls
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
namespace RiemannGaussian.SemiprimeD1StackPortOwnerRecipePrepare
open SemiprimeD1StackPortOwnerRecipe SemiprimeD1StackPortOwnerRecipeSpec SemiprimeD1StackPortOwnerRecipeCalls
open SemiprimeD1StackProcedureTrace (Runs one_base)
open SemiprimeD1StackUnaryDivmod (unary)
/-- Actual preparation-call bound at each fixed finite instruction location. -/
def stepTime (p:Counters) (pc:Fin 41) : ℕ :=
  match pc.val with
  | 0=>SemiprimeD1StackPortOwnerMaddBounds.budget (p.r) (p.t) (0)+1
  | 1=>5*(p.r*p.t)+4
  | 2=>1
  | 3=>5*(p.a)+4
  | 4=>100*(p.a+p.r+1)+1
  | 5=>5*(p.b)+4
  | 6=>100*(p.b+p.r+1)+1
  | 7=>5*(p.t)+4
  | 8=>5*(p.c)+4
  | 9=>5*(p.r)+4
  | 10=>5*(p.c)+4
  | 11=>SemiprimeD1StackPortOwnerMaddBounds.budget (p.t) (p.c) (p.b)+1
  | 12=>5*(p.a)+4
  | 13=>1
  | 14=>5*(p.b)+4
  | 15=>1
  | 16=>5*(p.digits)+4
  | 17=>1
  | 18=>5*(p.b)+4
  | 19=>1
  | 20=>SemiprimeD1StackPortOwnerMaddBounds.budget ((p.b/p.r)) ((p.r*p.t+1)) (p.c)+1
  | 21=>SemiprimeD1StackPortOwnerMaddBounds.budget ((p.c+p.t)) ((p.r*p.t+1)) (p.d)+1
  | 22=>SemiprimeD1StackPortOwnerMaddBounds.budget (p.b) ((p.r*p.t+1)) (p.d)+1
  | 23=>5*(p.r*p.t+1)+4
  | 24=>5*(p.d)+4
  | 25=>SemiprimeD1StackPortOwnerMaddBounds.budget ((p.c+p.r)) ((p.r*p.t+1)) (p.d)+1
  | 26=>SemiprimeD1StackPortOwnerMaddBounds.budget (p.a) ((p.r*p.t+1)) (p.d)+1
  | 27=>SemiprimeD1StackPortOwnerMaddBounds.budget ((p.a/p.r)) ((p.r*p.t+1)) (p.b)+1
  | 28=>SemiprimeD1StackPortOwnerMaddBounds.budget (2) ((p.r*p.t+1)) (p.b)+1
  | 29=>5*(p.r*p.t+1)+4
  | 30=>5*(p.b)+4
  | 31=>5*(p.a)+4
  | 32=>5*(2)+4
  | 33=>30*((p.a)+(2)+1)+11
  | 34=>5*(p.a)+4
  | 35=>5*(p.r*p.t)+4
  | 36=>30*((p.a)+(p.r*p.t)+1)+11
  | 37=>5*(p.b+1)+4
  | 38=>5*(p.digits-1)+4
  | 39=>30*((p.b+1)+(p.digits-1)+1)+11
  | 40=>5*(p.tag)+4
  | _=>0
/-- Physical predecessor deletes exactly one unary marker, including zero. -/
theorem unary_tail (n:ℕ) : (unary n).tail=unary (n-1) := by simp [unary]
/-- Concatenation with a physically pushed successor retains the actual scalar sum. -/
theorem unary_append_succ (a b:ℕ) : unary a++true::unary b=unary (a+(b+1)) := by
  rw [←SemiprimeD1StackUnaryDivmod.unary_succ,←SemiprimeD1StackUnaryDivmod.unary_add]
local macro "store_equal" : tactic => `(tactic|
  (funext k
   rcases k with k|k
   · cases k <;> first | rfl | simp [atStage,cached,words,arg,reg,aux,maddStack,maddOperands,divideStack,lessStack,
       copyOperands,Function.update,unary_tail,unary_append_succ,SemiprimeD1StackUnaryDivmod.unary_succ,←SemiprimeD1StackUnaryDivmod.unary_add]
   · rcases k with k|k
     · cases k <;> first | rfl | simp [atStage,cached,words,arg,reg,aux,maddStack,maddOperands,divideStack,lessStack,
         copyOperands,Function.update,unary_tail,unary_append_succ,SemiprimeD1StackUnaryDivmod.unary_succ,←SemiprimeD1StackUnaryDivmod.unary_add]
     · cases k <;> first | rfl | simp [atStage,cached,words,arg,reg,aux,maddStack,maddOperands,divideStack,lessStack,
         copyOperands,Function.update,unary_tail,unary_append_succ,SemiprimeD1StackUnaryDivmod.unary_succ,←SemiprimeD1StackUnaryDivmod.unary_add]))
/-- Actual physical trace of static preparation stage 0. -/
theorem prepareStage0 (p:Counters) :
    ∃time ≤ stepTime p 0,Runs program time (.local (.prepare 0)) (atStage p 0)
      (nextPrepare 0) (atStage p (0+1)) := by
  obtain ⟨time,ht,h⟩:=madd_call .rt (atStage p 0) (.local (.prepare 0)) (nextPrepare 0) (p.r) (p.t) (0)
    rfl rfl rfl rfl rfl rfl rfl rfl
  refine ⟨time,ht,?_⟩
  have he:Function.update (atStage p 0) (maddStack .rt (.inr .output))
      (unary (p.r*p.t+0))=atStage p (0+1):=by store_equal
  rw [he] at h
  exact h
/-- Actual physical trace of static preparation stage 1. -/
theorem prepareStage1 (p:Counters) :
    ∃time ≤ stepTime p 1,Runs program time (.local (.prepare 1)) (atStage p 1)
      (nextPrepare 1) (atStage p (1+1)) := by
  have h:=copy_call .rtWidth (atStage p 1) (.local (.prepare 1)) (nextPrepare 1) rfl rfl
  refine ⟨5*((atStage p 1) (copyOperands .rtWidth).1).length+4,?_,?_⟩
  · change 5*(unary (p.r*p.t)).length+4≤5*(p.r*p.t)+4
    simp [unary]
  · have he:Function.update (atStage p 1) (copyOperands .rtWidth).2
        ((atStage p 1) (copyOperands .rtWidth).1++(atStage p 1) (copyOperands .rtWidth).2)=atStage p (1+1):=by store_equal
    rw [he] at h
    exact h
/-- Actual physical trace of static preparation stage 2. -/
theorem prepareStage2 (p:Counters) :
    ∃time ≤ stepTime p 2,Runs program time (.local (.prepare 2)) (atStage p 2)
      (nextPrepare 2) (atStage p (2+1)) := by
  refine ⟨1,le_rfl,?_⟩
  apply one_base program (.local (.prepare 2)) (nextPrepare 2) (.push (reg .width) true (nextPrepare 2)) (atStage p 2) (atStage p (2+1)) rfl rfl
  change Function.update (atStage p 2) (reg .width) (true::(atStage p 2) (reg .width))=atStage p (2+1)
  store_equal
/-- Actual physical trace of static preparation stage 3. -/
theorem prepareStage3 (p:Counters) :
    ∃time ≤ stepTime p 3,Runs program time (.local (.prepare 3)) (atStage p 3)
      (nextPrepare 3) (atStage p (3+1)) := by
  have h:=copy_call .aDiv (atStage p 3) (.local (.prepare 3)) (nextPrepare 3) rfl rfl
  refine ⟨5*((atStage p 3) (copyOperands .aDiv).1).length+4,?_,?_⟩
  · change 5*(unary (p.a)).length+4≤5*(p.a)+4
    simp [unary]
  · have he:Function.update (atStage p 3) (copyOperands .aDiv).2
        ((atStage p 3) (copyOperands .aDiv).1++(atStage p 3) (copyOperands .aDiv).2)=atStage p (3+1):=by store_equal
    rw [he] at h
    exact h
/-- Actual physical trace of static preparation stage 4. -/
theorem prepareStage4 (p:Counters) :
    ∃time ≤ stepTime p 4,Runs program time (.local (.prepare 4)) (atStage p 4)
      (nextPrepare 4) (atStage p (4+1)) := by
  obtain ⟨time,ht,h⟩:=divide_call false (atStage p 4) (.local (.prepare 4)) (nextPrepare 4) (p.a) p.r
    rfl rfl rfl rfl rfl rfl rfl
  refine ⟨time,ht,?_⟩
  have he:Function.update (Function.update (Function.update (atStage p 4) (divideStack false .input) [])
      (divideStack false .quotient) (unary (p.a/p.r)))
      (divideStack false .remainder) (unary (p.a%p.r))=atStage p (4+1):=by store_equal
  rw [he] at h
  exact h
/-- Actual physical trace of static preparation stage 5. -/
theorem prepareStage5 (p:Counters) :
    ∃time ≤ stepTime p 5,Runs program time (.local (.prepare 5)) (atStage p 5)
      (nextPrepare 5) (atStage p (5+1)) := by
  have h:=copy_call .bDiv (atStage p 5) (.local (.prepare 5)) (nextPrepare 5) rfl rfl
  refine ⟨5*((atStage p 5) (copyOperands .bDiv).1).length+4,?_,?_⟩
  · change 5*(unary (p.b)).length+4≤5*(p.b)+4
    simp [unary]
  · have he:Function.update (atStage p 5) (copyOperands .bDiv).2
        ((atStage p 5) (copyOperands .bDiv).1++(atStage p 5) (copyOperands .bDiv).2)=atStage p (5+1):=by store_equal
    rw [he] at h
    exact h
/-- Actual physical trace of static preparation stage 6. -/
theorem prepareStage6 (p:Counters) :
    ∃time ≤ stepTime p 6,Runs program time (.local (.prepare 6)) (atStage p 6)
      (nextPrepare 6) (atStage p (6+1)) := by
  obtain ⟨time,ht,h⟩:=divide_call true (atStage p 6) (.local (.prepare 6)) (nextPrepare 6) (p.b) p.r
    rfl rfl rfl rfl rfl rfl rfl
  refine ⟨time,ht,?_⟩
  have he:Function.update (Function.update (Function.update (atStage p 6) (divideStack true .input) [])
      (divideStack true .quotient) (unary (p.b/p.r)))
      (divideStack true .remainder) (unary (p.b%p.r))=atStage p (6+1):=by store_equal
  rw [he] at h
  exact h
/-- Actual physical trace of static preparation stage 7. -/
theorem prepareStage7 (p:Counters) :
    ∃time ≤ stepTime p 7,Runs program time (.local (.prepare 7)) (atStage p 7)
      (nextPrepare 7) (atStage p (7+1)) := by
  have h:=copy_call .tTc (atStage p 7) (.local (.prepare 7)) (nextPrepare 7) rfl rfl
  refine ⟨5*((atStage p 7) (copyOperands .tTc).1).length+4,?_,?_⟩
  · change 5*(unary (p.t)).length+4≤5*(p.t)+4
    simp [unary]
  · have he:Function.update (atStage p 7) (copyOperands .tTc).2
        ((atStage p 7) (copyOperands .tTc).1++(atStage p 7) (copyOperands .tTc).2)=atStage p (7+1):=by store_equal
    rw [he] at h
    exact h
/-- Actual physical trace of static preparation stage 8. -/
theorem prepareStage8 (p:Counters) :
    ∃time ≤ stepTime p 8,Runs program time (.local (.prepare 8)) (atStage p 8)
      (nextPrepare 8) (atStage p (8+1)) := by
  have h:=copy_call .cTc (atStage p 8) (.local (.prepare 8)) (nextPrepare 8) rfl rfl
  refine ⟨5*((atStage p 8) (copyOperands .cTc).1).length+4,?_,?_⟩
  · change 5*(unary (p.c)).length+4≤5*(p.c)+4
    simp [unary]
  · have he:Function.update (atStage p 8) (copyOperands .cTc).2
        ((atStage p 8) (copyOperands .cTc).1++(atStage p 8) (copyOperands .cTc).2)=atStage p (8+1):=by store_equal
    rw [he] at h
    exact h
/-- Actual physical trace of static preparation stage 9. -/
theorem prepareStage9 (p:Counters) :
    ∃time ≤ stepTime p 9,Runs program time (.local (.prepare 9)) (atStage p 9)
      (nextPrepare 9) (atStage p (9+1)) := by
  have h:=copy_call .rRc (atStage p 9) (.local (.prepare 9)) (nextPrepare 9) rfl rfl
  refine ⟨5*((atStage p 9) (copyOperands .rRc).1).length+4,?_,?_⟩
  · change 5*(unary (p.r)).length+4≤5*(p.r)+4
    simp [unary]
  · have he:Function.update (atStage p 9) (copyOperands .rRc).2
        ((atStage p 9) (copyOperands .rRc).1++(atStage p 9) (copyOperands .rRc).2)=atStage p (9+1):=by store_equal
    rw [he] at h
    exact h
/-- Actual physical trace of static preparation stage 10. -/
theorem prepareStage10 (p:Counters) :
    ∃time ≤ stepTime p 10,Runs program time (.local (.prepare 10)) (atStage p 10)
      (nextPrepare 10) (atStage p (10+1)) := by
  have h:=copy_call .cRc (atStage p 10) (.local (.prepare 10)) (nextPrepare 10) rfl rfl
  refine ⟨5*((atStage p 10) (copyOperands .cRc).1).length+4,?_,?_⟩
  · change 5*(unary (p.c)).length+4≤5*(p.c)+4
    simp [unary]
  · have he:Function.update (atStage p 10) (copyOperands .cRc).2
        ((atStage p 10) (copyOperands .cRc).1++(atStage p 10) (copyOperands .cRc).2)=atStage p (10+1):=by store_equal
    rw [he] at h
    exact h
/-- Actual physical trace of static preparation stage 11. -/
theorem prepareStage11 (p:Counters) :
    ∃time ≤ stepTime p 11,Runs program time (.local (.prepare 11)) (atStage p 11)
      (nextPrepare 11) (atStage p (11+1)) := by
  obtain ⟨time,ht,h⟩:=madd_call .pbc (atStage p 11) (.local (.prepare 11)) (nextPrepare 11) (p.t) (p.c) (p.b)
    rfl rfl rfl rfl rfl rfl rfl rfl
  refine ⟨time,ht,?_⟩
  have he:Function.update (atStage p 11) (maddStack .pbc (.inr .output))
      (unary (p.t*p.c+p.b))=atStage p (11+1):=by store_equal
  rw [he] at h
  exact h
/-- Actual physical trace of static preparation stage 12. -/
theorem prepareStage12 (p:Counters) :
    ∃time ≤ stepTime p 12,Runs program time (.local (.prepare 12)) (atStage p 12)
      (nextPrepare 12) (atStage p (12+1)) := by
  have h:=copy_call .aMinus (atStage p 12) (.local (.prepare 12)) (nextPrepare 12) rfl rfl
  refine ⟨5*((atStage p 12) (copyOperands .aMinus).1).length+4,?_,?_⟩
  · change 5*(unary (p.a)).length+4≤5*(p.a)+4
    simp [unary]
  · have he:Function.update (atStage p 12) (copyOperands .aMinus).2
        ((atStage p 12) (copyOperands .aMinus).1++(atStage p 12) (copyOperands .aMinus).2)=atStage p (12+1):=by store_equal
    rw [he] at h
    exact h
/-- Actual physical trace of static preparation stage 13. -/
theorem prepareStage13 (p:Counters) :
    ∃time ≤ stepTime p 13,Runs program time (.local (.prepare 13)) (atStage p 13)
      (nextPrepare 13) (atStage p (13+1)) := by
  refine ⟨1,le_rfl,?_⟩
  apply one_base program (.local (.prepare 13)) (nextPrepare 13) (.pop (reg .aminus) (nextPrepare 13) (nextPrepare 13) (nextPrepare 13)) (atStage p 13) (atStage p (13+1)) rfl
  · change some (SemiprimeD1StackBytecode.choose (nextPrepare 13) (nextPrepare 13) (nextPrepare 13) ((atStage p 13) (reg .aminus)).head?)=some (nextPrepare 13)
    cases hh:((atStage p 13) (reg .aminus)).head? with
    | none=>rfl
    | some b=>cases b <;> rfl
  · change Function.update (atStage p 13) (reg .aminus) ((atStage p 13) (reg .aminus)).tail=atStage p (13+1)
    store_equal
/-- Actual physical trace of static preparation stage 14. -/
theorem prepareStage14 (p:Counters) :
    ∃time ≤ stepTime p 14,Runs program time (.local (.prepare 14)) (atStage p 14)
      (nextPrepare 14) (atStage p (14+1)) := by
  have h:=copy_call .bMinus (atStage p 14) (.local (.prepare 14)) (nextPrepare 14) rfl rfl
  refine ⟨5*((atStage p 14) (copyOperands .bMinus).1).length+4,?_,?_⟩
  · change 5*(unary (p.b)).length+4≤5*(p.b)+4
    simp [unary]
  · have he:Function.update (atStage p 14) (copyOperands .bMinus).2
        ((atStage p 14) (copyOperands .bMinus).1++(atStage p 14) (copyOperands .bMinus).2)=atStage p (14+1):=by store_equal
    rw [he] at h
    exact h
/-- Actual physical trace of static preparation stage 15. -/
theorem prepareStage15 (p:Counters) :
    ∃time ≤ stepTime p 15,Runs program time (.local (.prepare 15)) (atStage p 15)
      (nextPrepare 15) (atStage p (15+1)) := by
  refine ⟨1,le_rfl,?_⟩
  apply one_base program (.local (.prepare 15)) (nextPrepare 15) (.pop (reg .bminus) (nextPrepare 15) (nextPrepare 15) (nextPrepare 15)) (atStage p 15) (atStage p (15+1)) rfl
  · change some (SemiprimeD1StackBytecode.choose (nextPrepare 15) (nextPrepare 15) (nextPrepare 15) ((atStage p 15) (reg .bminus)).head?)=some (nextPrepare 15)
    cases hh:((atStage p 15) (reg .bminus)).head? with
    | none=>rfl
    | some b=>cases b <;> rfl
  · change Function.update (atStage p 15) (reg .bminus) ((atStage p 15) (reg .bminus)).tail=atStage p (15+1)
    store_equal
/-- Actual physical trace of static preparation stage 16. -/
theorem prepareStage16 (p:Counters) :
    ∃time ≤ stepTime p 16,Runs program time (.local (.prepare 16)) (atStage p 16)
      (nextPrepare 16) (atStage p (16+1)) := by
  have h:=copy_call .digitsMinus (atStage p 16) (.local (.prepare 16)) (nextPrepare 16) rfl rfl
  refine ⟨5*((atStage p 16) (copyOperands .digitsMinus).1).length+4,?_,?_⟩
  · change 5*(unary (p.digits)).length+4≤5*(p.digits)+4
    simp [unary]
  · have he:Function.update (atStage p 16) (copyOperands .digitsMinus).2
        ((atStage p 16) (copyOperands .digitsMinus).1++(atStage p 16) (copyOperands .digitsMinus).2)=atStage p (16+1):=by store_equal
    rw [he] at h
    exact h
/-- Actual physical trace of static preparation stage 17. -/
theorem prepareStage17 (p:Counters) :
    ∃time ≤ stepTime p 17,Runs program time (.local (.prepare 17)) (atStage p 17)
      (nextPrepare 17) (atStage p (17+1)) := by
  refine ⟨1,le_rfl,?_⟩
  apply one_base program (.local (.prepare 17)) (nextPrepare 17) (.pop (reg .dminus) (nextPrepare 17) (nextPrepare 17) (nextPrepare 17)) (atStage p 17) (atStage p (17+1)) rfl
  · change some (SemiprimeD1StackBytecode.choose (nextPrepare 17) (nextPrepare 17) (nextPrepare 17) ((atStage p 17) (reg .dminus)).head?)=some (nextPrepare 17)
    cases hh:((atStage p 17) (reg .dminus)).head? with
    | none=>rfl
    | some b=>cases b <;> rfl
  · change Function.update (atStage p 17) (reg .dminus) ((atStage p 17) (reg .dminus)).tail=atStage p (17+1)
    store_equal
/-- Actual physical trace of static preparation stage 18. -/
theorem prepareStage18 (p:Counters) :
    ∃time ≤ stepTime p 18,Runs program time (.local (.prepare 18)) (atStage p 18)
      (nextPrepare 18) (atStage p (18+1)) := by
  have h:=copy_call .bPlus (atStage p 18) (.local (.prepare 18)) (nextPrepare 18) rfl rfl
  refine ⟨5*((atStage p 18) (copyOperands .bPlus).1).length+4,?_,?_⟩
  · change 5*(unary (p.b)).length+4≤5*(p.b)+4
    simp [unary]
  · have he:Function.update (atStage p 18) (copyOperands .bPlus).2
        ((atStage p 18) (copyOperands .bPlus).1++(atStage p 18) (copyOperands .bPlus).2)=atStage p (18+1):=by store_equal
    rw [he] at h
    exact h
/-- Actual physical trace of static preparation stage 19. -/
theorem prepareStage19 (p:Counters) :
    ∃time ≤ stepTime p 19,Runs program time (.local (.prepare 19)) (atStage p 19)
      (nextPrepare 19) (atStage p (19+1)) := by
  refine ⟨1,le_rfl,?_⟩
  apply one_base program (.local (.prepare 19)) (nextPrepare 19) (.push (reg .bplus) true (nextPrepare 19)) (atStage p 19) (atStage p (19+1)) rfl rfl
  change Function.update (atStage p 19) (reg .bplus) (true::(atStage p 19) (reg .bplus))=atStage p (19+1)
  store_equal
/-- Actual physical trace of static preparation stage 20. -/
theorem prepareStage20 (p:Counters) :
    ∃time ≤ stepTime p 20,Runs program time (.local (.prepare 20)) (atStage p 20)
      (nextPrepare 20) (atStage p (20+1)) := by
  obtain ⟨time,ht,h⟩:=madd_call .slot10 (atStage p 20) (.local (.prepare 20)) (nextPrepare 20) ((p.b/p.r)) ((p.r*p.t+1)) (p.c)
    rfl rfl rfl rfl rfl rfl rfl rfl
  refine ⟨time,ht,?_⟩
  have he:Function.update (atStage p 20) (maddStack .slot10 (.inr .output))
      (unary ((p.b/p.r)*(p.r*p.t+1)+p.c))=atStage p (20+1):=by store_equal
  rw [he] at h
  exact h
/-- Actual physical trace of static preparation stage 21. -/
theorem prepareStage21 (p:Counters) :
    ∃time ≤ stepTime p 21,Runs program time (.local (.prepare 21)) (atStage p 21)
      (nextPrepare 21) (atStage p (21+1)) := by
  obtain ⟨time,ht,h⟩:=madd_call .slot11 (atStage p 21) (.local (.prepare 21)) (nextPrepare 21) ((p.c+p.t)) ((p.r*p.t+1)) (p.d)
    rfl rfl rfl rfl rfl rfl rfl rfl
  refine ⟨time,ht,?_⟩
  have he:Function.update (atStage p 21) (maddStack .slot11 (.inr .output))
      (unary ((p.c+p.t)*(p.r*p.t+1)+p.d))=atStage p (21+1):=by store_equal
  rw [he] at h
  exact h
/-- Actual physical trace of static preparation stage 22. -/
theorem prepareStage22 (p:Counters) :
    ∃time ≤ stepTime p 22,Runs program time (.local (.prepare 22)) (atStage p 22)
      (nextPrepare 22) (atStage p (22+1)) := by
  obtain ⟨time,ht,h⟩:=madd_call .slot12 (atStage p 22) (.local (.prepare 22)) (nextPrepare 22) (p.b) ((p.r*p.t+1)) (p.d)
    rfl rfl rfl rfl rfl rfl rfl rfl
  refine ⟨time,ht,?_⟩
  have he:Function.update (atStage p 22) (maddStack .slot12 (.inr .output))
      (unary (p.b*(p.r*p.t+1)+p.d))=atStage p (22+1):=by store_equal
  rw [he] at h
  exact h
/-- Actual physical trace of static preparation stage 23. -/
theorem prepareStage23 (p:Counters) :
    ∃time ≤ stepTime p 23,Runs program time (.local (.prepare 23)) (atStage p 23)
      (nextPrepare 23) (atStage p (23+1)) := by
  have h:=copy_call .widthWd (atStage p 23) (.local (.prepare 23)) (nextPrepare 23) rfl rfl
  refine ⟨5*((atStage p 23) (copyOperands .widthWd).1).length+4,?_,?_⟩
  · change 5*(unary (p.r*p.t+1)).length+4≤5*(p.r*p.t+1)+4
    simp [unary]
  · have he:Function.update (atStage p 23) (copyOperands .widthWd).2
        ((atStage p 23) (copyOperands .widthWd).1++(atStage p 23) (copyOperands .widthWd).2)=atStage p (23+1):=by store_equal
    rw [he] at h
    exact h
/-- Actual physical trace of static preparation stage 24. -/
theorem prepareStage24 (p:Counters) :
    ∃time ≤ stepTime p 24,Runs program time (.local (.prepare 24)) (atStage p 24)
      (nextPrepare 24) (atStage p (24+1)) := by
  have h:=copy_call .dWd (atStage p 24) (.local (.prepare 24)) (nextPrepare 24) rfl rfl
  refine ⟨5*((atStage p 24) (copyOperands .dWd).1).length+4,?_,?_⟩
  · change 5*(unary (p.d)).length+4≤5*(p.d)+4
    simp [unary]
  · have he:Function.update (atStage p 24) (copyOperands .dWd).2
        ((atStage p 24) (copyOperands .dWd).1++(atStage p 24) (copyOperands .dWd).2)=atStage p (24+1):=by store_equal
    rw [he] at h
    exact h
/-- Actual physical trace of static preparation stage 25. -/
theorem prepareStage25 (p:Counters) :
    ∃time ≤ stepTime p 25,Runs program time (.local (.prepare 25)) (atStage p 25)
      (nextPrepare 25) (atStage p (25+1)) := by
  obtain ⟨time,ht,h⟩:=madd_call .slot13f (atStage p 25) (.local (.prepare 25)) (nextPrepare 25) ((p.c+p.r)) ((p.r*p.t+1)) (p.d)
    rfl rfl rfl rfl rfl rfl rfl rfl
  refine ⟨time,ht,?_⟩
  have he:Function.update (atStage p 25) (maddStack .slot13f (.inr .output))
      (unary ((p.c+p.r)*(p.r*p.t+1)+p.d))=atStage p (25+1):=by store_equal
  rw [he] at h
  exact h
/-- Actual physical trace of static preparation stage 26. -/
theorem prepareStage26 (p:Counters) :
    ∃time ≤ stepTime p 26,Runs program time (.local (.prepare 26)) (atStage p 26)
      (nextPrepare 26) (atStage p (26+1)) := by
  obtain ⟨time,ht,h⟩:=madd_call .slot13t (atStage p 26) (.local (.prepare 26)) (nextPrepare 26) (p.a) ((p.r*p.t+1)) (p.d)
    rfl rfl rfl rfl rfl rfl rfl rfl
  refine ⟨time,ht,?_⟩
  have he:Function.update (atStage p 26) (maddStack .slot13t (.inr .output))
      (unary (p.a*(p.r*p.t+1)+p.d))=atStage p (26+1):=by store_equal
  rw [he] at h
  exact h
/-- Actual physical trace of static preparation stage 27. -/
theorem prepareStage27 (p:Counters) :
    ∃time ≤ stepTime p 27,Runs program time (.local (.prepare 27)) (atStage p 27)
      (nextPrepare 27) (atStage p (27+1)) := by
  obtain ⟨time,ht,h⟩:=madd_call .slot14t (atStage p 27) (.local (.prepare 27)) (nextPrepare 27) ((p.a/p.r)) ((p.r*p.t+1)) (p.b)
    rfl rfl rfl rfl rfl rfl rfl rfl
  refine ⟨time,ht,?_⟩
  have he:Function.update (atStage p 27) (maddStack .slot14t (.inr .output))
      (unary ((p.a/p.r)*(p.r*p.t+1)+p.b))=atStage p (27+1):=by store_equal
  rw [he] at h
  exact h
/-- Actual physical trace of static preparation stage 28. -/
theorem prepareStage28 (p:Counters) :
    ∃time ≤ stepTime p 28,Runs program time (.local (.prepare 28)) (atStage p 28)
      (nextPrepare 28) (atStage p (28+1)) := by
  obtain ⟨time,ht,h⟩:=madd_call .slot14f (atStage p 28) (.local (.prepare 28)) (nextPrepare 28) (2) ((p.r*p.t+1)) (p.b)
    rfl rfl rfl rfl rfl rfl rfl rfl
  refine ⟨time,ht,?_⟩
  have he:Function.update (atStage p 28) (maddStack .slot14f (.inr .output))
      (unary (2*(p.r*p.t+1)+p.b))=atStage p (28+1):=by store_equal
  rw [he] at h
  exact h
/-- Actual physical trace of static preparation stage 29. -/
theorem prepareStage29 (p:Counters) :
    ∃time ≤ stepTime p 29,Runs program time (.local (.prepare 29)) (atStage p 29)
      (nextPrepare 29) (atStage p (29+1)) := by
  have h:=copy_call .widthWb (atStage p 29) (.local (.prepare 29)) (nextPrepare 29) rfl rfl
  refine ⟨5*((atStage p 29) (copyOperands .widthWb).1).length+4,?_,?_⟩
  · change 5*(unary (p.r*p.t+1)).length+4≤5*(p.r*p.t+1)+4
    simp [unary]
  · have he:Function.update (atStage p 29) (copyOperands .widthWb).2
        ((atStage p 29) (copyOperands .widthWb).1++(atStage p 29) (copyOperands .widthWb).2)=atStage p (29+1):=by store_equal
    rw [he] at h
    exact h
/-- Actual physical trace of static preparation stage 30. -/
theorem prepareStage30 (p:Counters) :
    ∃time ≤ stepTime p 30,Runs program time (.local (.prepare 30)) (atStage p 30)
      (nextPrepare 30) (atStage p (30+1)) := by
  have h:=copy_call .bWb (atStage p 30) (.local (.prepare 30)) (nextPrepare 30) rfl rfl
  refine ⟨5*((atStage p 30) (copyOperands .bWb).1).length+4,?_,?_⟩
  · change 5*(unary (p.b)).length+4≤5*(p.b)+4
    simp [unary]
  · have he:Function.update (atStage p 30) (copyOperands .bWb).2
        ((atStage p 30) (copyOperands .bWb).1++(atStage p 30) (copyOperands .bWb).2)=atStage p (30+1):=by store_equal
    rw [he] at h
    exact h
/-- Actual physical trace of static preparation stage 31. -/
theorem prepareStage31 (p:Counters) :
    ∃time ≤ stepTime p 31,Runs program time (.local (.prepare 31)) (atStage p 31)
      (nextPrepare 31) (atStage p (31+1)) := by
  have h:=copy_call .aTest (atStage p 31) (.local (.prepare 31)) (nextPrepare 31) rfl rfl
  refine ⟨5*((atStage p 31) (copyOperands .aTest).1).length+4,?_,?_⟩
  · change 5*(unary (p.a)).length+4≤5*(p.a)+4
    simp [unary]
  · have he:Function.update (atStage p 31) (copyOperands .aTest).2
        ((atStage p 31) (copyOperands .aTest).1++(atStage p 31) (copyOperands .aTest).2)=atStage p (31+1):=by store_equal
    rw [he] at h
    exact h
/-- Actual physical trace of static preparation stage 32. -/
theorem prepareStage32 (p:Counters) :
    ∃time ≤ stepTime p 32,Runs program time (.local (.prepare 32)) (atStage p 32)
      (nextPrepare 32) (atStage p (32+1)) := by
  have h:=copy_call .twoLimit (atStage p 32) (.local (.prepare 32)) (nextPrepare 32) rfl rfl
  refine ⟨5*((atStage p 32) (copyOperands .twoLimit).1).length+4,?_,?_⟩
  · change 5*(unary (2)).length+4≤5*(2)+4
    simp [unary]
  · have he:Function.update (atStage p 32) (copyOperands .twoLimit).2
        ((atStage p 32) (copyOperands .twoLimit).1++(atStage p 32) (copyOperands .twoLimit).2)=atStage p (32+1):=by store_equal
    rw [he] at h
    exact h
/-- Actual physical trace of static preparation stage 33. -/
theorem prepareStage33 (p:Counters) :
    ∃time ≤ stepTime p 33,Runs program time (.local (.prepare 33)) (atStage p 33)
      (nextPrepare 33) (atStage p (33+1)) := by
  obtain ⟨time,ht,h⟩:=less_call .smallA (atStage p 33) (.local (.prepare 33)) (nextPrepare 33) (p.a) (2)
    rfl rfl rfl rfl rfl
  refine ⟨time,ht,?_⟩
  have he:Function.update (Function.update (Function.update (atStage p 33) (lessStack .smallA .left) [])
      (lessStack .smallA .limit) []) (lessStack .smallA .valid) [decide ((p.a)<(2))]=atStage p (33+1):=by store_equal
  rw [he] at h
  exact h
/-- Actual physical trace of static preparation stage 34. -/
theorem prepareStage34 (p:Counters) :
    ∃time ≤ stepTime p 34,Runs program time (.local (.prepare 34)) (atStage p 34)
      (nextPrepare 34) (atStage p (34+1)) := by
  have h:=copy_call .aTest (atStage p 34) (.local (.prepare 34)) (nextPrepare 34) rfl rfl
  refine ⟨5*((atStage p 34) (copyOperands .aTest).1).length+4,?_,?_⟩
  · change 5*(unary (p.a)).length+4≤5*(p.a)+4
    simp [unary]
  · have he:Function.update (atStage p 34) (copyOperands .aTest).2
        ((atStage p 34) (copyOperands .aTest).1++(atStage p 34) (copyOperands .aTest).2)=atStage p (34+1):=by store_equal
    rw [he] at h
    exact h
/-- Actual physical trace of static preparation stage 35. -/
theorem prepareStage35 (p:Counters) :
    ∃time ≤ stepTime p 35,Runs program time (.local (.prepare 35)) (atStage p 35)
      (nextPrepare 35) (atStage p (35+1)) := by
  have h:=copy_call .rtLimit (atStage p 35) (.local (.prepare 35)) (nextPrepare 35) rfl rfl
  refine ⟨5*((atStage p 35) (copyOperands .rtLimit).1).length+4,?_,?_⟩
  · change 5*(unary (p.r*p.t)).length+4≤5*(p.r*p.t)+4
    simp [unary]
  · have he:Function.update (atStage p 35) (copyOperands .rtLimit).2
        ((atStage p 35) (copyOperands .rtLimit).1++(atStage p 35) (copyOperands .rtLimit).2)=atStage p (35+1):=by store_equal
    rw [he] at h
    exact h
/-- Actual physical trace of static preparation stage 36. -/
theorem prepareStage36 (p:Counters) :
    ∃time ≤ stepTime p 36,Runs program time (.local (.prepare 36)) (atStage p 36)
      (nextPrepare 36) (atStage p (36+1)) := by
  obtain ⟨time,ht,h⟩:=less_call .art (atStage p 36) (.local (.prepare 36)) (nextPrepare 36) (p.a) (p.r*p.t)
    rfl rfl rfl rfl rfl
  refine ⟨time,ht,?_⟩
  have he:Function.update (Function.update (Function.update (atStage p 36) (lessStack .art .left) [])
      (lessStack .art .limit) []) (lessStack .art .valid) [decide ((p.a)<(p.r*p.t))]=atStage p (36+1):=by store_equal
  rw [he] at h
  exact h
/-- Actual physical trace of static preparation stage 37. -/
theorem prepareStage37 (p:Counters) :
    ∃time ≤ stepTime p 37,Runs program time (.local (.prepare 37)) (atStage p 37)
      (nextPrepare 37) (atStage p (37+1)) := by
  have h:=copy_call .nextTest (atStage p 37) (.local (.prepare 37)) (nextPrepare 37) rfl rfl
  refine ⟨5*((atStage p 37) (copyOperands .nextTest).1).length+4,?_,?_⟩
  · change 5*(unary (p.b+1)).length+4≤5*(p.b+1)+4
    simp [unary]
  · have he:Function.update (atStage p 37) (copyOperands .nextTest).2
        ((atStage p 37) (copyOperands .nextTest).1++(atStage p 37) (copyOperands .nextTest).2)=atStage p (37+1):=by store_equal
    rw [he] at h
    exact h
/-- Actual physical trace of static preparation stage 38. -/
theorem prepareStage38 (p:Counters) :
    ∃time ≤ stepTime p 38,Runs program time (.local (.prepare 38)) (atStage p 38)
      (nextPrepare 38) (atStage p (38+1)) := by
  have h:=copy_call .digitsLimit (atStage p 38) (.local (.prepare 38)) (nextPrepare 38) rfl rfl
  refine ⟨5*((atStage p 38) (copyOperands .digitsLimit).1).length+4,?_,?_⟩
  · change 5*(unary (p.digits-1)).length+4≤5*(p.digits-1)+4
    simp [unary]
  · have he:Function.update (atStage p 38) (copyOperands .digitsLimit).2
        ((atStage p 38) (copyOperands .digitsLimit).1++(atStage p 38) (copyOperands .digitsLimit).2)=atStage p (38+1):=by store_equal
    rw [he] at h
    exact h
/-- Actual physical trace of static preparation stage 39. -/
theorem prepareStage39 (p:Counters) :
    ∃time ≤ stepTime p 39,Runs program time (.local (.prepare 39)) (atStage p 39)
      (nextPrepare 39) (atStage p (39+1)) := by
  obtain ⟨time,ht,h⟩:=less_call .next (atStage p 39) (.local (.prepare 39)) (nextPrepare 39) (p.b+1) (p.digits-1)
    rfl rfl rfl rfl rfl
  refine ⟨time,ht,?_⟩
  have he:Function.update (Function.update (Function.update (atStage p 39) (lessStack .next .left) [])
      (lessStack .next .limit) []) (lessStack .next .valid) [decide ((p.b+1)<(p.digits-1))]=atStage p (39+1):=by store_equal
  rw [he] at h
  exact h
/-- Actual physical trace of static preparation stage 40. -/
theorem prepareStage40 (p:Counters) :
    ∃time ≤ stepTime p 40,Runs program time (.local (.prepare 40)) (atStage p 40)
      (nextPrepare 40) (atStage p (40+1)) := by
  have h:=copy_call .tag (atStage p 40) (.local (.prepare 40)) (nextPrepare 40) rfl rfl
  refine ⟨5*((atStage p 40) (copyOperands .tag).1).length+4,?_,?_⟩
  · change 5*(unary (p.tag)).length+4≤5*(p.tag)+4
    simp [unary]
  · have he:Function.update (atStage p 40) (copyOperands .tag).2
        ((atStage p 40) (copyOperands .tag).1++(atStage p 40) (copyOperands .tag).2)=atStage p (40+1):=by store_equal
    rw [he] at h
    exact h
/-- Every finite preparation location executes the actual included primitive. -/
theorem prepare_step (p:Counters) (pc:Fin 41) :
    ∃time ≤ stepTime p pc,Runs program time (.local (.prepare pc)) (atStage p pc.val)
      (nextPrepare pc) (atStage p (pc.val+1)) := by
  fin_cases pc
  · exact prepareStage0 p
  · exact prepareStage1 p
  · exact prepareStage2 p
  · exact prepareStage3 p
  · exact prepareStage4 p
  · exact prepareStage5 p
  · exact prepareStage6 p
  · exact prepareStage7 p
  · exact prepareStage8 p
  · exact prepareStage9 p
  · exact prepareStage10 p
  · exact prepareStage11 p
  · exact prepareStage12 p
  · exact prepareStage13 p
  · exact prepareStage14 p
  · exact prepareStage15 p
  · exact prepareStage16 p
  · exact prepareStage17 p
  · exact prepareStage18 p
  · exact prepareStage19 p
  · exact prepareStage20 p
  · exact prepareStage21 p
  · exact prepareStage22 p
  · exact prepareStage23 p
  · exact prepareStage24 p
  · exact prepareStage25 p
  · exact prepareStage26 p
  · exact prepareStage27 p
  · exact prepareStage28 p
  · exact prepareStage29 p
  · exact prepareStage30 p
  · exact prepareStage31 p
  · exact prepareStage32 p
  · exact prepareStage33 p
  · exact prepareStage34 p
  · exact prepareStage35 p
  · exact prepareStage36 p
  · exact prepareStage37 p
  · exact prepareStage38 p
  · exact prepareStage39 p
  · exact prepareStage40 p
end RiemannGaussian.SemiprimeD1StackPortOwnerRecipePrepare
