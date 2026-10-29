/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryPrimitives
/-! # Actual framed-field source calls at all21 fixed factory sites -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryFields
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackChildGroupFactoryWiringFacts
open SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
/-- Each real Field call preserves every other115-role word and pays its own physical call/return. -/
theorem field_call (site:Fin 21) (pc next:Label)
    (hc:program pc=.call (.field site (F.active .tagPop (none,false))) next) (before:Stack→List Bool) (word tail:List Bool)
    (hi:before (fieldStack site (.inl .input))=frame word tail)
    (ho:before (fieldStack site (.inl .output))=[]) (hs:before (field (.inl .scratch))=[]) (hv:before (field (.inr ()))=[]):
    Runs program (8*word.length+7) pc before next
      (Function.update (Function.update (Function.update before (fieldStack site (.inl .input)) tail)
        (fieldStack site (.inl .output)) word) (field (.inr ())) [true]):=by
  let start:=SemiprimeD1TensorTapeFieldBytecode.initial (frame word tail) []
  let stop:SemiprimeD1StackBytecode.State F.Stack F.Label:=
    ⟨none,none,Sum.elim (SemiprimeD1TensorTapeFieldMachine.contents tail [] word) (fun _=>[true])⟩
  have hin:Link.DataRel (fieldStack site) before start.store before:=by
    constructor
    · intro k;rcases k with k|k
      · cases k with
        | input=>exact hi
        | scratch=>exact hs
        | output=>exact ho
      · cases k;exact hv
    · intro k _;rfl
  have h0:=Link.data_update (fieldStack site) (field_injective site) before start.store before hin (.inl .input) tail
  have h1:=Link.data_update (fieldStack site) (field_injective site) before _ _ h0 (.inl .output) word
  have h2:=Link.data_update (fieldStack site) (field_injective site) before _ _ h1 (.inr ()) [true]
  have he:Function.update (Function.update (Function.update start.store (.inl .input) tail) (.inl .output) word) (.inr ()) [true]=stop.store:=by
    funext k;rcases k with k|k <;> cases k <;> rfl
  rw [he] at h2
  exact included_call program (fieldStack site) (Label.field site) (field_injective site) F.code
    (F.active .tagPop (none,false)) (fun _=>rfl) pc next
    hc (8*word.length+6) start stop _ _ rfl rfl
    (SemiprimeD1TensorTapeFieldBytecode.framed_run word tail []) hin h2
/-- The caller physically consumes the real parser flag before using the field. -/
theorem field_read (site:Fin 21) (pc parsed next empty low:Label)
    (hc:program pc=.call (.field site (F.active .tagPop (none,false))) parsed)
    (hp:program parsed=.base (.pop (field (.inr ())) empty low next))
    (before:Stack→List Bool) (word tail:List Bool)
    (hi:before (fieldStack site (.inl .input))=frame word tail)
    (ho:before (fieldStack site (.inl .output))=[])
    (hs:before (field (.inl .scratch))=[]) (hv:before (field (.inr ()))=[]):
    Runs program (8*word.length+8) pc before next
      (Function.update (Function.update before (fieldStack site (.inl .input)) tail)
        (fieldStack site (.inl .output)) word):=by
  have h0:=field_call site pc parsed hc before word tail hi ho hs hv
  let v:=Function.update (Function.update (Function.update before (fieldStack site (.inl .input)) tail)
    (fieldStack site (.inl .output)) word) (field (.inr ())) [true]
  have h1:=pop_run parsed empty low next (field (.inr ())) v [true] hp (Function.update_self _ _ _)
  simp only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] at h1
  have he:Function.update v (field (.inr ())) []=
      Function.update (Function.update before (fieldStack site (.inl .input)) tail)
        (fieldStack site (.inl .output)) word:=by
    dsimp [v]
    have hoNe:fieldStack site (.inl .output)≠field (.inr ()) := (field_disjoint site).2.2.2.2
    have hiNe:fieldStack site (.inl .input)≠field (.inr ()) := (field_disjoint site).2.2.2.1
    rw [Function.update_idem,Function.update_comm hoNe,Function.update_comm hiNe]
    have hz:Function.update before (field (.inr ())) []=before:=by
      rw [←hv];exact Function.update_eq_self _ _
    rw [hz]
  rw [he] at h1
  have h:=join h0 h1
  simpa only [Nat.add_assoc] using h
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryFields
