/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceSelectedKeysEncoding
import RiemannGaussian.SemiprimeD1StackSourceSelectedKeysPrimitives
/-! # Exact39-role physical boundary stores throughout selected-key acquisition -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceSelectedKeysView
open SemiprimeD1StackSourceSelectedKeys SemiprimeD1StackSourceSelectedKeysEncoding
namespace Env
export SemiprimeD1StackSourceEnvironmentView (view)
export SemiprimeD1StackSourceEnvironmentEncoding (dictionary variableKey)
end Env
/-- All39 actual words, including retained arbitrary caller inputs, saved query and every parser/frame/log word. -/
def view (i:Inputs) (q present returned reader own fac ownID key valid buffer hist out:List Bool) :Stack→List Bool :=
  Sum.elim (Env.view (Env.dictionary i.ids) (Env.variableKey i.ids.length) i.chosen q i.pfx [] [] present [] returned)
    (fun k=>match k with
      | .source=>tape i | .savedQuery=>i.query | .reader=>reader | .ownerKey=>own | .factorKey=>fac
      | .ownerID=>ownID | .key=>key | .valid=>valid | .frameBuffer=>buffer | .history=>hist | .output=>out | _=>[])
/-- One physical q write retains every other39-role word. -/
theorem update_q (i:Inputs) (q present returned reader own fac ownID key valid buffer hist out word:List Bool) :
    Function.update (view i q present returned reader own fac ownID key valid buffer hist out) (query) word=view i word present returned reader own fac ownID key valid buffer hist out :=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- One physical present write retains every other39-role word. -/
theorem update_present (i:Inputs) (q present returned reader own fac ownID key valid buffer hist out word:List Bool) :
    Function.update (view i q present returned reader own fac ownID key valid buffer hist out) (found) word=view i q word returned reader own fac ownID key valid buffer hist out :=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- One physical returned write retains every other39-role word. -/
theorem update_returned (i:Inputs) (q present returned reader own fac ownID key valid buffer hist out word:List Bool) :
    Function.update (view i q present returned reader own fac ownID key valid buffer hist out) (idOutput) word=view i q present word reader own fac ownID key valid buffer hist out :=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- One physical reader write retains every other39-role word. -/
theorem update_reader (i:Inputs) (q present returned reader own fac ownID key valid buffer hist out word:List Bool) :
    Function.update (view i q present returned reader own fac ownID key valid buffer hist out) (aux .reader) word=view i q present returned word own fac ownID key valid buffer hist out :=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- One physical own write retains every other39-role word. -/
theorem update_own (i:Inputs) (q present returned reader own fac ownID key valid buffer hist out word:List Bool) :
    Function.update (view i q present returned reader own fac ownID key valid buffer hist out) (aux .ownerKey) word=view i q present returned reader word fac ownID key valid buffer hist out :=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- One physical fac write retains every other39-role word. -/
theorem update_fac (i:Inputs) (q present returned reader own fac ownID key valid buffer hist out word:List Bool) :
    Function.update (view i q present returned reader own fac ownID key valid buffer hist out) (aux .factorKey) word=view i q present returned reader own word ownID key valid buffer hist out :=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- One physical ownID write retains every other39-role word. -/
theorem update_ownID (i:Inputs) (q present returned reader own fac ownID key valid buffer hist out word:List Bool) :
    Function.update (view i q present returned reader own fac ownID key valid buffer hist out) (aux .ownerID) word=view i q present returned reader own fac word key valid buffer hist out :=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- One physical key write retains every other39-role word. -/
theorem update_key (i:Inputs) (q present returned reader own fac ownID key valid buffer hist out word:List Bool) :
    Function.update (view i q present returned reader own fac ownID key valid buffer hist out) (aux .key) word=view i q present returned reader own fac ownID word valid buffer hist out :=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- One physical valid write retains every other39-role word. -/
theorem update_valid (i:Inputs) (q present returned reader own fac ownID key valid buffer hist out word:List Bool) :
    Function.update (view i q present returned reader own fac ownID key valid buffer hist out) (aux .valid) word=view i q present returned reader own fac ownID key word buffer hist out :=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- One physical buffer write retains every other39-role word. -/
theorem update_buffer (i:Inputs) (q present returned reader own fac ownID key valid buffer hist out word:List Bool) :
    Function.update (view i q present returned reader own fac ownID key valid buffer hist out) (aux .frameBuffer) word=view i q present returned reader own fac ownID key valid word hist out :=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- One physical hist write retains every other39-role word. -/
theorem update_hist (i:Inputs) (q present returned reader own fac ownID key valid buffer hist out word:List Bool) :
    Function.update (view i q present returned reader own fac ownID key valid buffer hist out) (aux .history) word=view i q present returned reader own fac ownID key valid buffer word out :=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- One physical out write retains every other39-role word. -/
theorem update_out (i:Inputs) (q present returned reader own fac ownID key valid buffer hist out word:List Bool) :
    Function.update (view i q present returned reader own fac ownID key valid buffer hist out) (aux .output) word=view i q present returned reader own fac ownID key valid buffer hist word :=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- A real lookup sees precisely its acquired complete cache and current actual query, with fresh20work words. -/
theorem environment_projection (i:Inputs) (q reader own fac ownID key valid buffer hist out:List Bool)
    (k:SemiprimeD1StackSourceEnvironment.Stack) :
    view i q [] [] reader own fac ownID key valid buffer hist out (environmentStack k)=
      (SemiprimeD1StackSourceEnvironmentExecution.lookupReady i.ids i.chosen q i.pfx).data k :=rfl
end RiemannGaussian.SemiprimeD1StackSourceSelectedKeysView
