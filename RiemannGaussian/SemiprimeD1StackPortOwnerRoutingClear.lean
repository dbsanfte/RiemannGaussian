/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortOwnerRoutingEmit
import RiemannGaussian.SemiprimeD1StackPhysicalLoops
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPortOwnerRoutingClear
open SemiprimeD1StackPortOwnerRouting SemiprimeD1StackPortOwnerRoutingAcquisition
open SemiprimeD1StackPortOwnerRoutingView
open SemiprimeD1StackProcedureTrace (Runs runs_trans)
/-- Fixed mathematical inverse of the real eleven-role lookup cleanup order. -/
def lookupRank : Lookup.Stack→Fin 11
  | .inl .left=>0 | .inl .right=>1 | .inl .scratch=>2 | .inl .output=>3
  | .inr .query=>4 | .inr .reader=>5 | .inr .fieldScratch=>6 | .inr .valid=>7
  | .inr .copyScratch=>8 | .inr .discard=>9 | .inr .output=>10
/-- Every real lookup role, including its unread map suffix, is physically erased once. -/
theorem lookupRole_rank (k:Lookup.Stack) : lookupRole (lookupRank k)=k := by
  rcases k with k|k <;> cases k <;> decide
/-- Proof-side ordered inventory of ALL eleven lookup and nine parsed payloads. -/
abbrev Bank := Fin 20→List Bool
/-- Static union of the actual eleven lookup and nine cache cleanup roles. -/
def clearStack (i:Fin 20) : Stack :=
  if h:i.val<11 then lookupStack (lookupRole ⟨i.val,h⟩) else cache ⟨i.val-11,by omega⟩
/-- Actual source position throughout the two consecutive physical cleanup inventories. -/
def pc (n:Nat) : Label :=
  if h:n<11 then .local (.clearLookup ⟨n,h⟩)
  else if h:n<20 then .local (.clearCache ⟨n-11,by omega⟩) else .local .parse
/-- Every actual cleanup label pops exactly its real role and moves only on EOF. -/
theorem clear_instruction (i:Fin 20) :
    program (pc i.val)=.base (.pop (clearStack i) (pc (i.val+1)) (pc i.val) (pc i.val)) := by
  fin_cases i <;> rfl
/-- Exact retained real lookup and cache payloads, solely a mathematical store view. -/
def bank (l:Lookup.Stack→List Bool) (w:Fin 9→List Bool) : Bank :=
  fun i=>if h:i.val<11 then l (lookupRole ⟨i.val,h⟩) else w ⟨i.val-11,by omega⟩
/-- Literal physical store reconstructed from all twenty actually reached cleanup words. -/
def store (m:Map.Stack→List Bool) (s:Scope.Stack→List Bool) (b:Bank) (a:Aux→List Bool) : Stack→List Bool :=
  data m s (fun k=>b ⟨(lookupRank k).val,by omega⟩) (fun i=>b ⟨i.val+11,by omega⟩) a
/-- All actual lookup/cache data are retained in the cleanup view. -/
theorem store_bank (m:Map.Stack→List Bool) (s:Scope.Stack→List Bool) (l:Lookup.Stack→List Bool)
    (w:Fin 9→List Bool) (a:Aux→List Bool) : store m s (bank l w) a=data m s l w a := by
  unfold store
  congr 1
  · funext k;rcases k with k|k <;> cases k <;> rfl
/-- Actual physical role projection at each drain boundary. -/
theorem store_source (m:Map.Stack→List Bool) (s:Scope.Stack→List Bool) (b:Bank) (a:Aux→List Bool) (i:Fin 20) :
    store m s b a (clearStack i)=b i := by fin_cases i <;> rfl
/-- A real payload pop updates only its actual cleanup word, retaining both original sources and collector. -/
theorem store_update (m:Map.Stack→List Bool) (s:Scope.Stack→List Bool) (b:Bank) (a:Aux→List Bool)
    (i:Fin 20) (word:List Bool) :
    Function.update (store m s b a) (clearStack i) word=store m s (Function.update b i word) a := by
  funext k;rcases k with k|k
  · have hn:(mapStack k)≠clearStack i:=by fin_cases i <;> intro h <;> cases h
    exact Function.update_of_ne hn _ _
  · rcases k with k|k
    · have hn:(scopeStack k)≠clearStack i:=by fin_cases i <;> intro h <;> cases h
      exact Function.update_of_ne hn _ _
    · rcases k with k|k
      · rcases k with k|k
        · fin_cases i <;> cases k <;> rfl
        · fin_cases i <;> cases k <;> rfl
      · rcases k with k|k
        · fin_cases i <;> fin_cases k <;> rfl
        · have hn:(aux k)≠clearStack i:=by fin_cases i <;> intro h <;> cases h
          exact Function.update_of_ne hn _ _
/-- Mathematical state after the first n physically drained words. -/
def cleared (b:Bank) (n:Nat) (i:Fin 20) : List Bool :=if i.val<n then [] else b i
/-- One actual drain advances the exact twenty-word store view. -/
theorem cleared_step (b:Bank) (i:Fin 20) :
    Function.update (cleared b i.val) i []=cleared b (i.val+1) := by
  funext j;fin_cases i <;> fin_cases j <;> rfl
/-- Every actual payload has been physically erased at cleanup exit. -/
theorem cleared_end (b:Bank) :cleared b 20=fun _=>[]:=by funext i;exact ite_eq_left i.isLt
/-- Actual physical drain time, including all unread-map/query/owner bytes and all EOF pops. -/
def time (b:Bank) : Nat→Nat
  | 0=>0
  | n+1=>time b n+(b ⟨n%20,Nat.mod_lt _ (by omega)⟩).length+1
/-- Each of the real twenty word-drain loops executes all its actual payload pops. -/
theorem clear_step (m:Map.Stack→List Bool) (s:Scope.Stack→List Bool) (b:Bank) (a:Aux→List Bool) (i:Fin 20) :
    Runs program ((b i).length+1) (pc i.val) (store m s (cleared b i.val) a)
      (pc (i.val+1)) (store m s (cleared b (i.val+1)) a) := by
  let before:=store m s (cleared b i.val) a
  have hv:before (clearStack i)=b i:=by simp only [before,store_source,cleared,Nat.lt_irrefl,ite_false]
  have hi:Function.update before (clearStack i) (b i)=before:=by rw [←hv];exact Function.update_eq_self _ _
  have h:=SemiprimeD1StackPhysicalLoops.drain program (pc i.val) (pc (i.val+1)) (clearStack i)
    (clear_instruction i) before (b i)
  rw [hi] at h
  simpa only [before,store_update,cleared_step] using h
/-- Exact SAME-source cleanup of the first n actual lookup/cache payloads. -/
theorem clear_prefix (m:Map.Stack→List Bool) (s:Scope.Stack→List Bool) (b:Bank) (a:Aux→List Bool)
    (n:Nat) (hn:n≤20) :
    Runs program (time b n) (pc 0) (store m s (cleared b 0) a)
      (pc n) (store m s (cleared b n) a) := by
  induction n with
  | zero=>exact SemiprimeD1StackProcedureTrace.runs_refl program _ _
  | succ n ih=>
    have hlt:n<20:=by omega
    have hm:n%20=n:=Nat.mod_eq_of_lt hlt
    have h:=runs_trans program _ _ _ _ _ _ _ _ (ih (by omega)) (clear_step m s b a ⟨n,hlt⟩)
    simpa only [time,hm,Nat.add_assoc] using h
/-- COMPLETE real erasure of ALL eleven lookup roles and ALL nine original parsed fields.
The unread map suffix, retained compact query and actual owner-ID payload are all charged. -/
theorem clear_run (m:Map.Stack→List Bool) (s:Scope.Stack→List Bool) (l:Lookup.Stack→List Bool)
    (w:Fin 9→List Bool) (a:Aux→List Bool) :
    Runs program (time (bank l w) 20) (.local (.clearLookup 0)) (data m s l w a)
      (.local .parse) (data m s (fun _=>[]) (fun _=>[]) a) := by
  have h:=clear_prefix m s (bank l w) a 20 (by omega)
  have hz:cleared (bank l w) 0=bank l w:=by funext i;exact ite_eq_right (Nat.not_lt_zero _)
  have hp0:pc 0=.local (.clearLookup 0):=by simp [pc]
  have hp20:pc 20=.local .parse:=by simp [pc]
  rw [hz,hp0,hp20,cleared_end,store_bank] at h
  simpa only [store] using h
end RiemannGaussian.SemiprimeD1StackPortOwnerRoutingClear
