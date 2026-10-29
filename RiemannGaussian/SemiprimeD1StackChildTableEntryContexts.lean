/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackProcedureCallsTrace
import RiemannGaussian.SemiprimeD1StackChildTableEntryView
import RiemannGaussian.SemiprimeD1StackChildTableEntryPrimitives
/-! # Real acquisition of both retained original context banks -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildTableEntryContexts
open SemiprimeD1StackChildTableEntry SemiprimeD1StackChildTableEntryEncoding
open SemiprimeD1StackChildTableEntryView SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeD1StackUnaryDivmod (unary)
namespace Link
export SemiprimeD1StackMultiplierLink (DataRel)
end Link
local notation "ctl"=>Label.local
/-- Complete actual old context acquisition preserves every other physical field and all genuine outer returns. -/
theorem old_call (axes:List Nat) (hp:∀q∈axes,0<q) (p:List Bool)
    (child:J.Stack→List Bool) (g:G.Stack→List Bool) (t:T.Stack→List Bool) (r:R.Stack→List Bool) (a:Aux→List Bool):
    ∃q ≤ SemiprimeD1StackJetContextCorrectness.budget axes p+1,Runs program q (ctl .start)
      (bank (J.initial (vectorBits (axes.map unary)) p).data child g t r a) (ctl .childContext) (bank (Context.finalData axes p) child g t r a):=by
  let start:=J.initial (vectorBits (axes.map unary)) p
  let stop:C.State J.Stack J.Label:=⟨none,none,none,Context.finalData axes p,[]⟩
  have hin:Link.DataRel (context false) (bank (J.initial (vectorBits (axes.map unary)) p).data child g t r a) start.data (bank (J.initial (vectorBits (axes.map unary)) p).data child g t r a):=by
    constructor
    · intro k;rfl
    · intro k _;rfl
  have hout:Link.DataRel (context false) (bank (J.initial (vectorBits (axes.map unary)) p).data child g t r a) stop.data (bank (Context.finalData axes p) child g t r a):=by
    constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k|k|k|k|k
      · exact False.elim (hk k rfl)
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
  obtain ⟨q,hq,hr⟩:=SemiprimeD1StackJetContextCorrectness.source_run axes hp p
  refine ⟨q+1,by omega,?_⟩
  exact SemiprimeD1StackProcedureCallsTrace.included_call program (context false) (Label.context false)
    (context_injective false) J.program .start (fun _=>rfl) (ctl .start) (ctl .childContext) rfl
    q start stop _ _ rfl rfl rfl rfl hr hin hout
/-- Complete actual child context acquisition preserves every other physical field and all genuine outer returns. -/
theorem child_call (axes:List Nat) (hp:∀q∈axes,0<q) (p:List Bool)
    (old:J.Stack→List Bool) (g:G.Stack→List Bool) (t:T.Stack→List Bool) (r:R.Stack→List Bool) (a:Aux→List Bool):
    ∃q ≤ SemiprimeD1StackJetContextCorrectness.budget axes p+1,Runs program q (ctl .childContext)
      (bank old (J.initial (vectorBits (axes.map unary)) p).data g t r a) (ctl .ready) (bank old (Context.finalData axes p) g t r a):=by
  let start:=J.initial (vectorBits (axes.map unary)) p
  let stop:C.State J.Stack J.Label:=⟨none,none,none,Context.finalData axes p,[]⟩
  have hin:Link.DataRel (context true) (bank old (J.initial (vectorBits (axes.map unary)) p).data g t r a) start.data (bank old (J.initial (vectorBits (axes.map unary)) p).data g t r a):=by
    constructor
    · intro k;rfl
    · intro k _;rfl
  have hout:Link.DataRel (context true) (bank old (J.initial (vectorBits (axes.map unary)) p).data g t r a) stop.data (bank old (Context.finalData axes p) g t r a):=by
    constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k|k|k|k|k
      · rfl
      · exact False.elim (hk k rfl)
      · rfl
      · rfl
      · rfl
      · rfl
  obtain ⟨q,hq,hr⟩:=SemiprimeD1StackJetContextCorrectness.source_run axes hp p
  refine ⟨q+1,by omega,?_⟩
  exact SemiprimeD1StackProcedureCallsTrace.included_call program (context true) (Label.context true)
    (context_injective true) J.program .start (fun _=>rfl) (ctl .childContext) (ctl .ready) rfl
    q start stop _ _ rfl rfl rfl rfl hr hin hout
end RiemannGaussian.SemiprimeD1StackChildTableEntryContexts
