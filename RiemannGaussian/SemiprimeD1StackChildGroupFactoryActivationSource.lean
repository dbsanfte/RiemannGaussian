/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryActivationLoop
/-! # Real thirteen-input entry through complete all-vertex activation
The two actual marker words acquire the iteration count. Source words, fields
and Valid witnesses are proof indices only, never additional physical inputs.
This prefix stops at the literal endpoint-source acquisition continuation.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryActivationSource
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackChildGroupFactoryActivation SemiprimeD1StackChildGroupFactoryActivationView
open SemiprimeD1StackChildGroupFactoryActivationLoop SemiprimeD1StackProcedureTrace
/-- Actual stopped activation bank before the program begins occurrence acquisition. -/
def result (i:Inputs) (coordinate:Nat) (rows:List Row):Stack→List Bool:=
  let out:=finish i coordinate [] [] [false] rows
  Function.update (data i [] [] [] out.map) (aux .activation) out.history.reverse
/-- Literal setup, all real rows, final reversal, and binary-key erasure. -/
def timeBound (i:Inputs) (coordinate:Nat) (environment catalogue:List (List Bool×List Bool)) (rows:List Row):Nat:=
  let out:=finish i coordinate [] [] [false] rows
  (5*i.owners.length+4)+(5*i.factors.length+4)+1+
    SemiprimeD1StackChildGroupFactoryActivationLoop.timeBound i coordinate environment catalogue [] rows+
    (2*out.history.length+3)+(out.key.length+1)
/-- Every original non-input workspace word is actually empty at entry. -/
theorem data_zero (i:Inputs):data i [] [] [] []=input i:=by
  funext k
  rcases k with k|k|k|k|k|k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · cases k <;> rfl
/-- Literal physical map-word write at a loop boundary. -/
theorem data_write_map (i:Inputs) (todo key hist map next:List Bool):
    Function.update (data i todo key hist map) (aux .activationMap) next=data i todo key hist next:=by
  funext k
  rcases k with k|k|k|k|k|k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · cases k <;> rfl
/-- Literal physical log-word write at a loop boundary. -/
theorem data_write_history (i:Inputs) (todo key hist map next:List Bool):
    Function.update (data i todo key hist map) (aux .activationHistory) next=data i todo key next map:=by
  funext k
  rcases k with k|k|k|k|k|k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · cases k <;> rfl
/-- Literal physical binary-key write at a loop boundary. -/
theorem data_write_key (i:Inputs) (todo key hist map next:List Bool):
    Function.update (data i todo key hist map) (aux .vertexKey) next=data i todo next hist map:=by
  funext k
  rcases k with k|k|k|k|k|k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · cases k <;> rfl
/-- From ONLY actual thirteen source words to all-vertex activation, with its own physical clock. -/
theorem source_trace (i:Inputs) (coordinate:Nat) (environment catalogue:List (List Bool×List Bool))
    (he:i.environment=SemiprimeD1StackOwnerLookup.records environment [])
    (hk:i.catalogue=SemiprimeD1StackOwnerLookup.records catalogue [])
    (hi:i.colourIndex=List.replicate coordinate true) (rows:List Row)
    (hlen:rows.length=i.owners.length+i.factors.length) (hv:Valid environment catalogue [] rows):
    ∃t≤timeBound i coordinate environment catalogue rows,
      Runs program t entry (input i) (.local 2 18) (result i coordinate rows):=by
  have h0:=copy_call 0 entry (.local 0 1) rfl (input i) i.owners [] rfl rfl rfl
  change Runs program (5*i.owners.length+4) entry (input i) (.local 0 1)
    (Function.update (input i) (aux .vertexTodo) (i.owners++[])) at h0
  simp only [List.append_nil] at h0
  rw [←data_zero i,data_write_todo] at h0
  have h1:=copy_call 1 (.local 0 1) (.local 0 2) rfl (data i i.owners [] [] [])
    i.factors i.owners rfl rfl rfl
  change Runs program (5*i.factors.length+4) (.local 0 1) (data i i.owners [] [] []) (.local 0 2)
    (Function.update (data i i.owners [] [] []) (aux .vertexTodo) (i.factors++i.owners)) at h1
  rw [data_write_todo] at h1
  have h2:=push_run (.local 0 2) (.local 0 3) (aux .activationMap) false
    (data i (i.factors++i.owners) [] [] []) rfl
  change Runs program 1 (.local 0 2) (data i (i.factors++i.owners) [] [] []) (.local 0 3)
    (Function.update (data i (i.factors++i.owners) [] [] []) (aux .activationMap) [false]) at h2
  rw [data_write_map] at h2
  obtain ⟨a,ha,h3⟩:=SemiprimeD1StackChildGroupFactoryActivationLoop.source_trace i coordinate environment catalogue
    he hk hi rows (i.factors++i.owners) [] [] [false] (by rw [List.length_append,hlen];omega) hv
  let out:=finish i coordinate [] [] [false] rows
  have h4:=reverse_call 0 (.local 2 16) (.local 2 17) rfl
    (data i [] out.key out.history out.map) out.history [] rfl rfl
  change Runs program (2*out.history.length+3) (.local 2 16) (data i [] out.key out.history out.map)
    (.local 2 17) (Function.update (Function.update (data i [] out.key out.history out.map)
      (aux .activationHistory) []) (aux .activation) (out.history.reverse++[])) at h4
  simp only [List.append_nil,data_write_history] at h4
  have h5:=drain_loop (.local 2 17) (.local 2 18) (aux .vertexKey) rfl
    (Function.update (data i [] out.key [] out.map) (aux .activation) out.history.reverse) out.key rfl
  have heq:Function.update (Function.update (data i [] out.key [] out.map)
      (aux .activation) out.history.reverse) (aux .vertexKey) []=result i coordinate rows:=by
    rw [Function.update_comm (by decide:aux .activation≠aux .vertexKey),data_write_key]
    rfl
  rw [heq] at h5
  refine ⟨(5*i.owners.length+4)+((5*i.factors.length+4)+(1+(a+((2*out.history.length+3)+(out.key.length+1))))),?_,?_⟩
  · dsimp only [timeBound,out]
    omega
  · have h:=join h0 (join h1 (join h2 (join h3 (join h4 h5))))
    simpa only [data_zero] using h
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryActivationSource
