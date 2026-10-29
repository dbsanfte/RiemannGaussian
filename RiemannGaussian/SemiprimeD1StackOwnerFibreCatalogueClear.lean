/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerFibreCatalogueView
import RiemannGaussian.SemiprimeD1StackPhysicalLoops
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackOwnerFibreCatalogueClear
open SemiprimeD1StackOwnerFibreCatalogue SemiprimeD1StackOwnerFibreCatalogueSource
open SemiprimeD1StackOwnerFibreCatalogueView
open SemiprimeD1StackProcedureTrace (Runs runs_trans)
/-- Fixed inverse to the actual fourteen-role filter cleanup order. -/
def rank :V.Stack→Fin 14
  | .inl .left=>0 | .inl .right=>1 | .inl .scratch=>2 | .inl .output=>3
  | .inr .query=>4 | .inr .reader=>5 | .inr .fieldScratch=>6 | .inr .valid=>7
  | .inr .copyScratch=>8 | .inr .payload=>9 | .inr .output=>10
  | .inr .frameBuffer=>11 | .inr .frameScratch=>12 | .inr .reversed=>13
/-- Every real filter role is visited exactly once by actual source cleanup. -/
theorem role_rank (k:V.Stack) :fibreRole (rank k)=k:=by rcases k with k|k <;> cases k <;> decide
/-- The proof-side rank agrees with every actual static drain call. -/
theorem rank_role (i:Fin 14) :rank (fibreRole i)=i:=by fin_cases i <;> decide
/-- Actual filter store after n physically drained payload roles. -/
def cleared (f:V.Stack→List Bool) (n:Nat) (k:V.Stack) :List Bool:=if (rank k).val<n then [] else f k
/-- An actual payload drain advances exactly the ordered cleanup view. -/
theorem cleared_step (f:V.Stack→List Bool) (i:Fin 14) :
    Function.update (cleared f i.val) (fibreRole i) []=cleared f (i.val+1):=by
  funext k;by_cases hk:k=fibreRole i
  · subst k;simp only [Function.update_same,cleared,rank_role,Nat.lt_succ_self,ite_true]
  · have hn:(rank k).val≠i.val:=by
      intro h;have he:rank k=i:=Fin.ext h
      have hr:=role_rank k;rw [he] at hr
      exact hk hr.symm
    simp only [Function.update_of_ne hk,cleared]
    split <;> split <;> simp_all <;> omega
/-- All filter payloads have been physically erased at cleanup exit. -/
theorem cleared_end (f:V.Stack→List Bool) :cleared f 14=fun _=>[]:=by funext k;exact ite_eq_left (rank k).isLt
/-- Actual next drain label, or the original E-loop after role fourteen. -/
def next (i:Fin 14) :Label:=
  if h:i.val<13 then .local (.clearFibre ⟨i.val+1,by omega⟩) else .local .loop
/-- Every real filter word is popped cell by cell, including its actual EOF transition. -/
theorem role_clear (s:R.Stack→List Bool) (f:V.Stack→List Bool) (a:Aux→List Bool) (i:Fin 14) :
    Runs program ((f (fibreRole i)).length+1) (.local (.clearFibre i))
      (data s (cleared f i.val) a) (next i) (data s (cleared f (i.val+1)) a):=by
  let before:=data s (cleared f i.val) a
  have hv:before (fibreStack (fibreRole i))=f (fibreRole i):=by
    simp only [before,data_fibre,cleared,rank_role,Nat.lt_irrefl,ite_false]
  have hi:Function.update before (fibreStack (fibreRole i)) (f (fibreRole i))=before:=by
    rw [←hv];exact Function.update_eq_self _ _
  have h:=SemiprimeD1StackPhysicalLoops.drain program (.local (.clearFibre i)) (next i)
    (fibreStack (fibreRole i)) rfl before (f (fibreRole i))
  rw [hi] at h
  simpa only [before,update_fibre,cleared_step] using h
/-- Static real source position within the complete filter cleanup. -/
def pc (n:Nat) :Label:=if h:n<14 then .local (.clearFibre ⟨n,h⟩) else .local .loop
/-- Chronological sum of all actual discarded payload lengths and EOF pops. -/
def time (f:V.Stack→List Bool) :Nat→Nat
  | 0=>0
  | n+1=>time f n+(f (fibreRole ⟨n%14,Nat.mod_lt _ (by omega)⟩)).length+1
/-- One actual static drain advances the exact physical role inventory. -/
theorem step (s:R.Stack→List Bool) (f:V.Stack→List Bool) (a:Aux→List Bool) (n:Nat) (hn:n<14) :
    Runs program ((f (fibreRole ⟨n,hn⟩)).length+1) (pc n) (data s (cleared f n) a)
      (pc (n+1)) (data s (cleared f (n+1)) a):=by
  have h:=role_clear s f a ⟨n,hn⟩
  have hp:next ⟨n,hn⟩=pc (n+1):=by
    unfold next pc
    by_cases h:n<13
    · simp only [h,show n+1<14 by omega,dite_eq_left]
    · have he:n=13:=by omega
      subst n;rfl
  rw [hp] at h
  simpa only [pc,dite_eq_left hn] using h
/-- Exact source trace through the first n physically erased filter roles. -/
theorem clear_prefix (s:R.Stack→List Bool) (f:V.Stack→List Bool) (a:Aux→List Bool) (n:Nat) (hn:n≤14) :
    Runs program (time f n) (pc 0) (data s (cleared f 0) a) (pc n) (data s (cleared f n) a):=by
  induction n with
  | zero=>exact SemiprimeD1StackProcedureTrace.runs_refl program _ _
  | succ n ih=>
    have hlt:n<14:=by omega
    have hm:n%14=n:=Nat.mod_eq_of_lt hlt
    have h:=runs_trans program _ _ _ _ _ _ _ _ (ih (by omega)) (step s f a n hlt)
    simpa only [time,hm,Nat.add_assoc] using h
/-- COMPLETE physical cleanup leaves the next owner iteration with fresh filter work, preserving E/IDs/history. -/
theorem clear_run (s:R.Stack→List Bool) (f:V.Stack→List Bool) (a:Aux→List Bool) :
    Runs program (time f 14) (.local (.clearFibre 0)) (data s f a) (.local .loop) (data s (fun _=>[]) a):=by
  have h:=clear_prefix s f a 14 (by omega)
  have hz:cleared f 0=f:=by funext k;exact ite_eq_right (Nat.not_lt_zero _)
  have hp0:pc 0=.local (.clearFibre 0):=by simp [pc]
  have hp14:pc 14=.local .loop:=by simp [pc]
  simpa only [hz,hp0,hp14,cleared_end] using h
end RiemannGaussian.SemiprimeD1StackOwnerFibreCatalogueClear
