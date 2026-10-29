/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerCatalogueClear
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackOwnerCatalogueCacheClear
open SemiprimeD1StackOwnerCatalogue SemiprimeD1StackOwnerCatalogueSource
open SemiprimeD1StackOwnerCatalogueFields SemiprimeD1StackOwnerCatalogueParse
open SemiprimeD1StackProcedureTrace (Runs runs_trans)
/-- Actual seven parsed payloads plus the two built keys retained for physical cleanup. -/
abbrev Packet := Fin 9→List Bool
/-- Literal physical store after arithmetic cleanup, retaining both actual tape suffixes. -/
def packet (s:S.Stack→List Bool) (p:Packet) (edges ids collector:List Bool) : Stack→List Bool :=
  data s (fun _=>[]) (fun i=>p ⟨i.val,by omega⟩) (fun k=>match k with
    | .readerEdges=>edges | .readerIds=>ids | .reversed=>collector
    | .record=>p 7 | .equalityKey=>p 8 | _=>[])
/-- The cleanup instruction reads the actual corresponding payload byte stack. -/
theorem packet_source (s:S.Stack→List Bool) (p:Packet) (edges ids collector:List Bool) (part:Fin 9) :
    packet s p edges ids collector (clearSource part)=p part := by
  fin_cases part <;> rfl
/-- Updating a real cleanup role preserves the source banks, both readers and the collector. -/
theorem packet_update (s:S.Stack→List Bool) (p:Packet) (edges ids collector:List Bool)
    (part:Fin 9) (word:List Bool) :
    Function.update (packet s p edges ids collector) (clearSource part) word=
      packet s (Function.update p part word) edges ids collector := by
  funext k
  rcases k with k|k
  · have hn:(Sum.inl k:Stack)≠clearSource part:=by
      fin_cases part <;> intro h <;> cases h
    exact Function.update_of_ne hn _ _
  · rcases k with k|k
    · have hn:(work k)≠clearSource part:=by
        fin_cases part <;> intro h <;> cases h
      exact Function.update_of_ne hn _ _
    · rcases k with k|k
      · fin_cases part <;> fin_cases k <;> simp [packet,clearSource,data,cache,aux,Function.update_apply]
      · fin_cases part <;> cases k <;> simp [packet,clearSource,data,cache,aux,Function.update_apply]
/-- Mathematical view of the payloads after n actual drains. -/
def cleared (p:Packet) (n:Nat) (i:Fin 9) : List Bool := if i.val<n then [] else p i
/-- The actual next role erasure advances the exact payload view. -/
theorem cleared_step (p:Packet) (part:Fin 9) :
    Function.update (cleared p part.val) part []=cleared p (part.val+1) := by
  funext i;fin_cases part <;> fin_cases i <;> rfl
/-- All nine actual payloads have been physically removed at cleanup exit. -/
theorem cleared_end (p:Packet) : cleared p 9=fun _=>[] := by
  funext i;exact ite_eq_left i.isLt
/-- The static next position after one real cache drain. -/
def next (part:Fin 9) : Label :=
  if h:part.val<8 then .local (.clearCache ⟨part.val+1,by omega⟩) else .local .parse
/-- Every bit in a payload is actually popped, plus its EOF transition. -/
theorem cache_call (s:S.Stack→List Bool) (p:Packet) (edges ids collector:List Bool) (part:Fin 9) :
    Runs program ((p part).length+1) (.local (.clearCache part))
      (packet s (cleared p part.val) edges ids collector) (next part)
      (packet s (cleared p (part.val+1)) edges ids collector) := by
  let before:=packet s (cleared p part.val) edges ids collector
  have hv:before (clearSource part)=p part:=by
    simp only [before,packet_source,cleared,Nat.lt_irrefl,ite_false]
  have hi:Function.update before (clearSource part) (p part)=before:=by
    rw [←hv];exact Function.update_eq_self _ _
  have h:=SemiprimeD1StackPhysicalLoops.drain program (.local (.clearCache part)) (next part)
    (clearSource part) rfl before (p part)
  rw [hi] at h
  simpa only [before,packet_update,cleared_step] using h
/-- Static position in the complete nine-payload cleanup. -/
def cachePC (n:Nat) : Label :=
  if h:n<9 then .local (.clearCache ⟨n,h⟩) else .local .parse
/-- Chronological sum of actual payload pops and their EOF pops. -/
def cacheTime (p:Packet) : Nat→Nat
  | 0=>0
  | n+1=>cacheTime p n+(p ⟨n%9,Nat.mod_lt _ (by omega)⟩).length+1
/-- One real cache drain advances the physically cleaned row view. -/
theorem cache_step (s:S.Stack→List Bool) (p:Packet) (edges ids collector:List Bool)
    (n:Nat) (hn:n<9) :
    Runs program ((p ⟨n,hn⟩).length+1) (cachePC n)
      (packet s (cleared p n) edges ids collector) (cachePC (n+1))
      (packet s (cleared p (n+1)) edges ids collector) := by
  have h:=cache_call s p edges ids collector ⟨n,hn⟩
  have hp:next ⟨n,hn⟩=cachePC (n+1):=by
    unfold next cachePC
    by_cases hn':n<8
    · simp only [hn',show n+1<9 by omega,dite_eq_left]
    · have he:n=8:=by omega
      subst n;rfl
  rw [hp] at h
  simpa only [cachePC,dite_eq_left hn] using h
/-- Exact trace of the first n real payload-drain loops. -/
theorem cache_prefix (s:S.Stack→List Bool) (p:Packet) (edges ids collector:List Bool)
    (n:Nat) (hn:n≤9) :
    Runs program (cacheTime p n) (cachePC 0) (packet s (cleared p 0) edges ids collector)
      (cachePC n) (packet s (cleared p n) edges ids collector) := by
  induction n with
  | zero=>exact SemiprimeD1StackProcedureTrace.runs_refl program _ _
  | succ n ih=>
    have hlt:n<9:=by omega
    have hm:n%9=n:=Nat.mod_eq_of_lt hlt
    have h:=runs_trans program _ _ _ _ _ _ _ _ (ih (by omega)) (cache_step s p edges ids collector n hlt)
    simpa only [cacheTime,hm,Nat.add_assoc] using h
/-- Every row cache is erased by the actual source; readers and collector survive for the next edge. -/
theorem cache_run (s:S.Stack→List Bool) (p:Packet) (edges ids collector:List Bool) :
    Runs program (cacheTime p 9) (.local (.clearCache 0)) (packet s p edges ids collector)
      (.local .parse) (data s (fun _=>[]) (fun _=>[]) (rowAux edges ids collector)) := by
  have h:=cache_prefix s p edges ids collector 9 (by omega)
  have hz:cleared p 0=p:=by funext k;exact ite_eq_right (Nat.not_lt_zero _)
  have hp0:cachePC 0=.local (.clearCache 0):=by simp [cachePC]
  have hp9:cachePC 9=.local .parse:=by simp [cachePC]
  have he:packet s (fun _=>[]) edges ids collector=
      data s (fun _=>[]) (fun _=>[]) (rowAux edges ids collector):=by
    funext k;rcases k with k|k
    · rfl
    · rcases k with k|k
      · rfl
      · rcases k with k|k
        · rfl
        · cases k <;> rfl
  simpa only [hz,hp0,hp9,cleared_end,he] using h
end RiemannGaussian.SemiprimeD1StackOwnerCatalogueCacheClear
