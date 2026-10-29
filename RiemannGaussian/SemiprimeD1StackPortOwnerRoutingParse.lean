/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortOwnerRoutingView
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPortOwnerRoutingParse
open SemiprimeD1StackPortOwnerRouting SemiprimeD1StackPortOwnerRoutingAcquisition
open SemiprimeD1StackPortOwnerRoutingView
open SemiprimeD1StackProcedureTrace (Runs included_call runs_trans one_base)
open SemiprimeD1StackPortOwnerRecipeCalls (update_rel)
open SemiprimeSourceHistogramKeyBits (frame)
namespace Rel
export SemiprimeD1StackMultiplierLink (DataRel)
end Rel
/-- All actual field readers use four distinct real Boolean roles. -/
theorem field_injective (part:Fin 9) : Function.Injective (fieldStack part) := by fin_cases part <;> decide
/-- Actual framed field parser, including its real positive-validity byte. -/
theorem field_call (part:Fin 9) (store:Stack→List Bool) (word tail:List Bool)
    (hi:store (aux .reader)=frame word tail) (ho:store (cache part)=[])
    (hs:store (aux .fieldScratch)=[]) (hv:store (aux .valid)=[]) :
    Runs program (8*word.length+7) (.local (.field part)) store (.local (.valid part))
      (Function.update (Function.update (Function.update store (aux .reader) tail) (cache part) word) (aux .valid) [true]) := by
  let before:=SemiprimeD1TensorTapeFieldBytecode.initial (frame word tail) []
  let after:SemiprimeD1StackBytecode.State F.Stack F.Label:=
    ⟨none,none,Sum.elim (SemiprimeD1TensorTapeFieldMachine.contents tail [] word) (fun _=>[true])⟩
  have hin:Rel.DataRel (fieldStack part) store before.store store:=by
    constructor
    · intro k;rcases k with k|k
      · cases k <;> simp [fieldStack,before,SemiprimeD1TensorTapeFieldBytecode.initial,
          SemiprimeD1TensorTapeFieldMachine.contents,hi,ho,hs]
      · cases k;exact hv
    · intro k _;rfl
  apply included_call program (fieldStack part) (Label.field part) (field_injective part)
    F.code (F.active .tagPop (none,false)) (fun _=>rfl) (.local (.field part)) (.local (.valid part))
    rfl (8*word.length+6) before after
  · rfl
  · rfl
  · exact SemiprimeD1TensorTapeFieldBytecode.framed_run word tail []
  · exact hin
  · have h0:=update_rel (fieldStack part) (field_injective part) store before.store store hin (.inl .input) tail
    have h1:=update_rel (fieldStack part) (field_injective part) store _ _ h0 (.inl .output) word
    have h2:=update_rel (fieldStack part) (field_injective part) store _ _ h1 (.inr ()) [true]
    have he:Function.update (Function.update (Function.update before.store (.inl .input) tail)
        (.inl .output) word) (.inr ()) [true]=after.store:=by
      funext k;rcases k with k|k <;> cases k <;> rfl
    simpa only [he,fieldStack] using h2
/-- Static actual continuation after validating one of the nine original fields. -/
def next (part:Fin 9) : Label :=
  if h:part.val<8 then .local (.field ⟨part.val+1,by omega⟩) else .local .sentinel
/-- One actual parse plus positive-validity pop, preserving all other physical banks. -/
theorem read_field (m:Map.Stack→List Bool) (s:Scope.Stack→List Bool) (l:Lookup.Stack→List Bool)
    (f:Fin 9→List Bool) (a:Aux→List Bool) (part:Fin 9) (word tail:List Bool)
    (hi:a .reader=frame word tail) (ho:f part=[]) (hs:a .fieldScratch=[]) (hv:a .valid=[]) :
    Runs program (8*word.length+8) (.local (.field part)) (data m s l f a) (next part)
      (data m s l (Function.update f part word) (Function.update a .reader tail)) := by
  let a':=Function.update a .reader tail
  let f':=Function.update f part word
  have hv':a' .valid=[]:=by simpa only [a',Function.update_of_ne (by decide : Aux.valid≠.reader)] using hv
  have hf:=field_call part (data m s l f a) word tail hi ho hs hv
  have he:Function.update (Function.update (Function.update (data m s l f a) (aux .reader) tail)
      (cache part) word) (aux .valid) [true]=data m s l f' (Function.update a' .valid [true]):=by
    simp only [update_aux,update_cache,a',f']
  rw [he] at hf
  have hp:Runs program 1 (.local (.valid part)) (data m s l f' (Function.update a' .valid [true]))
      (next part) (data m s l f' a'):=by
    apply one_base program _ _ (.pop (aux .valid) (.local .abort) (.local .abort) (next part)) _ _ rfl
    · simp only [SemiprimeD1StackBytecode.execute,data_aux,Function.update_same,
        SemiprimeD1StackBytecode.choose,List.head?_cons]
    · simp only [SemiprimeD1StackBytecode.execute,data_aux,Function.update_same,update_aux,Function.update_idem,List.tail_cons]
      rw [←hv',Function.update_eq_self]
  simpa only [show 8*word.length+8=(8*word.length+7)+1 by omega,a',f'] using
    runs_trans program _ _ _ _ _ _ _ _ hf hp
/-- Exact parsed prefix cache; unread fields are physically empty. -/
def parsed (w:Fin 9→List Bool) (n:Nat) (i:Fin 9) : List Bool :=if i.val<n then w i else []
/-- One actual cache write advances the exact parsed prefix. -/
theorem parsed_step (w:Fin 9→List Bool) (n:Nat) (hn:n<9) :
    Function.update (parsed w n) ⟨n,hn⟩ (w ⟨n,hn⟩)=parsed w (n+1) := by
  funext i;by_cases h:i=⟨n,hn⟩
  · subst i;simp [parsed]
  · have hi:i.val≠n:=by intro he;apply h;exact Fin.ext he
    simp only [Function.update_of_ne h,parsed]
    split <;> split <;> simp_all <;> omega
/-- Exact static field position, with sentinel acquisition only after ALL nine field payloads. -/
def pc (n:Nat) : Label :=if h:n<9 then .local (.field ⟨n,h⟩) else .local .sentinel
/-- Chronological sum of actual field-parser and validity-pop costs. -/
def time (w:Fin 9→List Bool) : Nat→Nat
  | 0=>0
  | n+1=>time w n+(8*(w ⟨n%9,Nat.mod_lt _ (by omega)⟩).length+8)
/-- Actual parser-boundary reader and collector after n physically consumed fields. -/
def boundaryAux (w:Fin 9→List Bool) (n:Nat) (tail raw:List Bool) : Aux→List Bool :=
  rowAux (SemiprimeD1FactorScopePairEncoding.suffix w n tail) raw
/-- One actual framed field read advances the exact nine-field suffix and cache prefix. -/
theorem field_step (m:Map.Stack→List Bool) (s:Scope.Stack→List Bool) (l:Lookup.Stack→List Bool)
    (w:Fin 9→List Bool) (n:Nat) (hn:n<9) (tail raw:List Bool) :
    Runs program (8*(w ⟨n,hn⟩).length+8) (pc n)
      (data m s l (parsed w n) (boundaryAux w n tail raw)) (pc (n+1))
      (data m s l (parsed w (n+1)) (boundaryAux w (n+1) tail raw)) := by
  let part:Fin 9:=⟨n,hn⟩
  have h:=read_field m s l (parsed w n) (boundaryAux w n tail raw) part (w part)
    (SemiprimeD1FactorScopePairEncoding.suffix w (n+1) tail)
    (SemiprimeD1FactorScopePairEncoding.suffix_step w part tail) (by simp [parsed,part]) rfl rfl
  have ha:Function.update (boundaryAux w n tail raw) .reader
      (SemiprimeD1FactorScopePairEncoding.suffix w (n+1) tail)=boundaryAux w (n+1) tail raw:=by
    funext k;cases k <;> simp [boundaryAux,rowAux]
  have hp:next part=pc (n+1):=by
    unfold next pc
    by_cases h:n<8
    · simp only [part,h,show n+1<9 by omega,dite_eq_left]
    · have he:n=8:=by omega
      subst n;rfl
  rw [ha,parsed_step w n hn,hp] at h
  simpa only [pc,dite_eq_left hn,part] using h
/-- Exact trace of the first n actual original scoped fields. -/
theorem field_prefix (m:Map.Stack→List Bool) (s:Scope.Stack→List Bool) (l:Lookup.Stack→List Bool)
    (w:Fin 9→List Bool) (n:Nat) (hn:n≤9) (tail raw:List Bool) :
    Runs program (time w n) (pc 0) (data m s l (parsed w 0) (boundaryAux w 0 tail raw))
      (pc n) (data m s l (parsed w n) (boundaryAux w n tail raw)) := by
  induction n with
  | zero=>exact SemiprimeD1StackProcedureTrace.runs_refl program _ _
  | succ n ih=>
    have hlt:n<9:=by omega
    have hm:n%9=n:=Nat.mod_eq_of_lt hlt
    have h:=runs_trans program _ _ _ _ _ _ _ _ (ih (by omega)) (field_step m s l w n hlt tail raw)
    simpa only [time,hm] using h
/-- EOF peek accepts a genuine empty first field; only an empty whole tape ends routing. -/
theorem peek_run (m:Map.Stack→List Bool) (s:Scope.Stack→List Bool) (l:Lookup.Stack→List Bool)
    (w:Fin 9→List Bool) (tail raw:List Bool) :
    Runs program 1 (.local .parse) (data m s l (parsed w 0) (boundaryAux w 0 tail raw))
      (pc 0) (data m s l (parsed w 0) (boundaryAux w 0 tail raw)) := by
  apply one_base program _ _ (.peek (aux .reader) (.local .finalTag) (.local (.field 0)) (.local (.field 0))) _ _ rfl
  · change some (SemiprimeD1StackBytecode.choose _ _ _
      (SemiprimeD1FactorScopePairEncoding.suffix w 0 tail).head?)=_
    rw [show SemiprimeD1FactorScopePairEncoding.suffix w 0 tail=
      frame (w 0) (SemiprimeD1FactorScopePairEncoding.suffix w 1 tail) from
      SemiprimeD1FactorScopePairEncoding.suffix_step w 0 tail]
    cases w 0 <;> simp only [frame,List.head?_cons,SemiprimeD1StackBytecode.choose,pc,
      show (0:Nat)<9 by omega,dite_eq_left,show (⟨0,by omega⟩:Fin 9)=0 by decide]
  · rfl
/-- ALL nine unchanged original physical payloads are read by the SAME routing source. -/
theorem parse_run (m:Map.Stack→List Bool) (s:Scope.Stack→List Bool) (l:Lookup.Stack→List Bool)
    (w:Fin 9→List Bool) (tail raw:List Bool) :
    Runs program (1+time w 9) (.local .parse)
      (data m s l (fun _=>[]) (rowAux (SemiprimeD1FactorScopePairEncoding.record w tail) raw))
      (.local .sentinel) (data m s l w (rowAux tail raw)) := by
  have h:=runs_trans program _ _ _ _ _ _ _ _ (peek_run m s l w tail raw) (field_prefix m s l w 9 (by omega) tail raw)
  have hz:parsed w 0=fun _=>[]:=by funext i;exact ite_eq_right (Nat.not_lt_zero _)
  have hall:parsed w 9=w:=by funext i;exact ite_eq_left i.isLt
  have hp:pc 9=.local .sentinel:=by simp [pc]
  simpa only [hz,hall,hp,boundaryAux,SemiprimeD1FactorScopePairEncoding.record,SemiprimeD1FactorScopePairEncoding.suffix_end] using h
end RiemannGaussian.SemiprimeD1StackPortOwnerRoutingParse
