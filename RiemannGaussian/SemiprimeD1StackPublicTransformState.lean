/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicTransformPrimitives
/-! # Fixed-role physical payload views for whole transform proofs
Parts/functions here are proof images of the fixed204 physical stacks. NONE
is an executing argument, a control register, word getter, evaluator or oracle.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackPublicTransformState
open SemiprimeD1StackPublicTransform SemiprimeD1StackProcedureTrace
/-- Proof image of the fixed physical component stores, not machine control. -/
structure Parts where
  /-- Original root acquisition's actual fixed-role data. -/
  root : R.Stack→List Bool := fun _=>[]
  /-- Actual dot component's fixed-role data. -/
  dot : D.Stack→List Bool := fun _=>[]
  /-- Actual modular multiplier's fixed-role data. -/
  multiplication : M.Stack→List Bool := fun _=>[]
  /-- Actual first n-word acquisition's fixed-role data. -/
  inputVector : W.Stack→List Bool := fun _=>[]
  /-- Actual second n-word acquisition's fixed-role data. -/
  outputVector : W.Stack→List Bool := fun _=>[]
  /-- Actual canonicality checker's fixed-role data. -/
  checker : V.Stack→List Bool := fun _=>[]
  /-- Actual output-vector reader's fixed-role data. -/
  reader : J.Stack→List Bool := fun _=>[]
  /-- Actual streaming numeric comparator's fixed-role data. -/
  equality : SemiprimeD1StackAdder.Stack→List Bool := fun _=>[]
  /-- Seven actual original/control/cache/work stores. -/
  auxiliary : Aux→List Bool := fun _=>[]
/-- Exact fixed-role physical store projection. -/
def data (p : Parts) : Stack→List Bool
  | .roots k=>p.root k | .dot k=>p.dot k | .multiply k=>p.multiplication k
  | .inputVector k=>p.inputVector k | .outputVector k=>p.outputVector k
  | .guard k=>p.checker k | .read k=>p.reader k | .equal k=>p.equality k | .aux k=>p.auxiliary k
/-- Proof view of one ACTUAL literal physical write. -/
def set (p : Parts) (role : Stack) (word : List Bool) : Parts := match role with
  | .roots k=>{p with root:=Function.update p.root k word}
  | .dot k=>{p with dot:=Function.update p.dot k word}
  | .multiply k=>{p with multiplication:=Function.update p.multiplication k word}
  | .inputVector k=>{p with inputVector:=Function.update p.inputVector k word}
  | .outputVector k=>{p with outputVector:=Function.update p.outputVector k word}
  | .guard k=>{p with checker:=Function.update p.checker k word}
  | .read k=>{p with reader:=Function.update p.reader k word}
  | .equal k=>{p with equality:=Function.update p.equality k word}
  | .aux k=>{p with auxiliary:=Function.update p.auxiliary k word}
/-- Proof-view write equals the machine's actual physical stack update. -/
theorem data_set (p : Parts) (role : Stack) (word : List Bool) :
    data (set p role word)=Function.update (data p) role word := by
  funext q
  cases role <;> cases q <;> first | rfl | (rename_i i j;by_cases h : i=j <;> simp_all [data,set,Function.update])
/-- Exact same role read after an actual write. -/
theorem data_set_same (p : Parts) (role : Stack) (word : List Bool) : data (set p role word) role=word := by
  rw [data_set,Function.update_same]
/-- Physically copied payload view; the execution theorem uses literal Copy. -/
def copied (p : Parts) (kind : CopyKind) : Parts := set p (copyDestination kind) (data p (copySource kind))
/-- Exact actual copy transition on the fixed-role proof image. -/
theorem copy_run (kind : CopyKind) (pc next : Label) (hc : program pc=.call (.copy kind 0) next)
    (p : Parts) (hd : data p (copyDestination kind)=[]) (hs : data p (.aux .scratch)=[]) :
    Runs program (5*(data p (copySource kind)).length+4) pc (data p) next (data (copied p kind)) := by
  rw [copied,data_set]
  exact SemiprimeD1StackPublicTransformPrimitives.copy_call kind pc next hc (data p) hd hs
/-- Original machine input as a fixed-role proof image. -/
def initialParts (bits raw : List Bool) (second inverse : Bool) : Parts :=
  {root:=R.input bits,auxiliary:=fun k=>match k with
    | .raw=>raw | .second=>[second] | .inverse=>[inverse] | _=>[]}
/-- No initial metadata/source/word/vector/count/answer appears in this image. -/
theorem initial_data (bits raw : List Bool) (second inverse : Bool) :
    data (initialParts bits raw second inverse)=(initial bits raw second inverse).data := by
  funext k;cases k <;> first | rfl | (rename_i k;cases k <;> rfl)
/-- Reached actual state after original N-only root acquisition executes ONCE. -/
def acquiredParts (bits raw : List Bool) (second inverse : Bool) : Parts :=
  {initialParts bits raw second inverse with root:=(SemiprimeD1StackRootSourceExecution.done bits).data}
/-- Root acquisition is a REAL included closed procedure, retaining raw/flags. -/
theorem roots_call (bits raw : List Bool) (second inverse : Bool) (hb : bits≠[]) :
    ∃t≤SemiprimeD1StackRootSourceBounds.timeBound bits+1,
      Runs program t .start (data (initialParts bits raw second inverse)) .selectSecond
        (data (acquiredParts bits raw second inverse)) := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackRootSourceBounds.source_run_bounded bits hb
  refine ⟨t+1,Nat.add_le_add_right ht 1,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program Stack.roots Label.roots
    (by intro i j h;exact Stack.roots.inj h) R.program .start (fun _=>rfl) .start .selectSecond rfl t
    (R.initial bits) (SemiprimeD1StackRootSourceExecution.done bits) _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk;cases k <;> first | rfl | exact (hk _ rfl).elim
end RiemannGaussian.SemiprimeD1StackPublicTransformState
