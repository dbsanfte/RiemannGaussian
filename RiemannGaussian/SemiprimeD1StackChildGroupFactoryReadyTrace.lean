/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryReady
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryExecution
/-! # Direct same-clock retained-bank execution, without a synthetic caller
The ready source replaces the core final halt by a real return. Its actual
balanced source stop proves that return reads EOF, hence genuinely halts.
All inner real returns and all258 allocated words are retained in the relation.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryReadyTrace
namespace C
export SemiprimeD1StackCalls (State Instruction execute step run)
end C
namespace Link
export SemiprimeD1StackMultiplierLink (DataRel data_update)
end Link
namespace V
export SemiprimeD1StackValidationLink (instruction halted_run)
end V
/-- Identical actual labels/flags/returns and complete included-plus-foreign data. -/
def Rel {A K L:Type} (stack:A→K) (aux:K→List Bool) (source:C.State A L) (target:C.State K L):Prop:=
  Link.DataRel stack aux source.data target.data ∧ target.pc=source.pc ∧ target.flag=source.flag ∧
    target.returned=source.returned ∧ target.frames=source.frames
/-- One actual instruction preserves the full relation; final return requires actual empty frames. -/
theorem execute_rel {A K L:Type} [DecidableEq A] [DecidableEq K]
    (stack:A→K) (hinj:Function.Injective stack) (aux:K→List Bool)
    (op:C.Instruction A L) (source:C.State A L) (target:C.State K L)
    (hh:op=.base .halt→source.frames=[]) (h:Rel stack aux source target):
    Rel stack aux (C.execute op source) (C.execute (V.instruction stack id op) target):=by
  rcases h with ⟨hd,hpc,hflag,hreturned,hframes⟩
  cases op with
  | base op=>
    cases op with
    | push j b next=>
      refine ⟨?_,rfl,hflag,hreturned,hframes⟩
      simpa only [V.instruction,SemiprimeD1StackMultiplierLink.instruction,C.execute,hd.1 j] using
        Link.data_update stack hinj aux source.data target.data hd j (b::source.data j)
    | pop j empty low high=>
      refine ⟨?_,?_,?_,hreturned,hframes⟩
      · simpa only [V.instruction,SemiprimeD1StackMultiplierLink.instruction,C.execute,hd.1 j] using
          Link.data_update stack hinj aux source.data target.data hd j (source.data j).tail
      · simp only [V.instruction,SemiprimeD1StackMultiplierLink.instruction,C.execute,hd.1 j,id_eq]
      · simp only [V.instruction,SemiprimeD1StackMultiplierLink.instruction,C.execute,hd.1 j]
    | peek j empty low high=>
      refine ⟨hd,?_,?_,hreturned,hframes⟩
      · simp only [V.instruction,SemiprimeD1StackMultiplierLink.instruction,C.execute,hd.1 j,id_eq]
      · simp only [V.instruction,SemiprimeD1StackMultiplierLink.instruction,C.execute,hd.1 j]
    | jump next=>exact ⟨hd,rfl,hflag,hreturned,hframes⟩
    | halt=>
      have hs:=hh rfl
      have ht:target.frames=[]:=hframes.trans hs
      simpa only [Rel,V.instruction,SemiprimeD1StackMultiplierLink.instruction,C.execute,hs,ht,and_self,and_true] using
        (show Link.DataRel stack aux source.data target.data from hd)
  | call callee next=>
    exact ⟨hd,rfl,rfl,rfl,congrArg (List.cons next) hframes⟩
  | ret=>
    cases hs:source.frames with
    | nil=>simpa only [Rel,V.instruction,C.execute,hs,hframes,hs,and_self,and_true] using hd
    | cons next frames=>
      simp only [V.instruction,C.execute,hframes,hs]
      exact ⟨hd,rfl,hflag,rfl,rfl⟩
/-- Exact direct transport of any successful balanced trace, with no added outer call or elapsed step. -/
theorem run_rel {A K L:Type} [DecidableEq A] [DecidableEq K]
    (stack:A→K) (hinj:Function.Injective stack) (aux:K→List Bool)
    (component:L→C.Instruction A L) (program:L→C.Instruction K L)
    (hcode:∀pc,program pc=V.instruction stack id (component pc))
    (fuel:Nat) (source out:C.State A L) (target:C.State K L)
    (h:Rel stack aux source target) (hr:C.run component fuel source=some out) (hout:out.frames=[]):
    ∃finish,C.run program fuel target=some finish ∧ Rel stack aux out finish:=by
  induction fuel generalizing source target with
  | zero=>change some source=some out at hr;cases hr;exact ⟨target,rfl,h⟩
  | succ fuel ih=>
    rw [show fuel+1=1+fuel by omega,SemiprimeD1StackReturnLink.run_add] at hr
    change (C.step component source).bind (C.run component fuel)=some out at hr
    cases hp:source.pc with
    | none=>simp [C.step,hp] at hr
    | some pc=>
      have hs:C.step component source=some (C.execute (component pc) source):=by simp [C.step,hp]
      rw [hs,Option.bind_some] at hr
      have hh:component pc=.base .halt→source.frames=[]:=by
        intro hop
        have he:=V.halted_run component fuel (C.execute (component pc) source) out (by simp [hop,C.execute]) hr
        have hf:=congrArg (fun st:C.State A L=>st.frames) he
        simpa only [hop,C.execute] using hf.trans hout
      have ht:C.step program target=some (C.execute (V.instruction stack id (component pc)) target):=by
        simp only [C.step,h.2.1,hp,Option.map_some,hcode]
      obtain ⟨finish,hfinish,hrel⟩:=ih (C.execute (component pc) source)
        (C.execute (V.instruction stack id (component pc)) target)
        (execute_rel stack hinj aux _ source target hh h) hr
      refine ⟨finish,?_,hrel⟩
      rw [show fuel+1=1+fuel by omega,SemiprimeD1StackReturnLink.run_add]
      change (C.step program target).bind (C.run program fuel)=some finish
      rw [ht,Option.bind_some,hfinish]
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryReadyTrace
