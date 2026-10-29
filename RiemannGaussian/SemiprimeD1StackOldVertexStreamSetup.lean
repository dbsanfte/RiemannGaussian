/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOldVertexStreamView
/-! # All four physical stream copies before the first vertex read -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackOldVertexStreamSetup
open SemiprimeD1StackOldVertexStream SemiprimeD1StackOldVertexStreamRoles
open SemiprimeD1StackOldVertexStreamView SemiprimeD1StackProcedureTrace
namespace Q
export SemiprimeD1StackOldVertexStreamPrimitives (copy_call join)
end Q
/-- Actual four reached readers; no parsed table, scope, order or activity singleton is supplied. -/
def loaded (i : Inputs) : Words:={empty with records:=i.records,activation:=i.activation,scopes:=i.scopes,orders:=i.orders}
/-- Total physical input bytes copied; all four immutable original words survive. -/
def streamBytes (i : Inputs) : ℕ:=i.records.length+i.activation.length+i.scopes.length+i.orders.length
/-- SAME actual source pays all four preserving copies once, with every restoration loop and call/return. -/
theorem source_run (i : Inputs) : Runs program (5*streamBytes i+16) (.local .start) (inputData i)
    (.local .recordTag) (data i (loaded i)):=by
  let w0:=empty
  let w1:={w0 with records:=i.records}
  let w2:={w1 with activation:=i.activation}
  let w3:={w2 with scopes:=i.scopes}
  let w4:={w3 with orders:=i.orders}
  have h0 : Runs program (5*i.records.length+4) (.local .start) (data i w0)
      (.local .copyActivation) (data i w1):=by
    have h:=Q.copy_call .records (.local .start) (.local .copyActivation) rfl (data i w0) i.records [] rfl rfl rfl
    change Runs program _ _ _ _ (Function.update (data i w0) (aux .recordsReader) (i.records++[])) at h
    simpa only [List.append_nil,update_records] using h
  have h1 : Runs program (5*i.activation.length+4) (.local .copyActivation) (data i w1)
      (.local .copyScopes) (data i w2):=by
    have h:=Q.copy_call .activation (.local .copyActivation) (.local .copyScopes) rfl (data i w1) i.activation [] rfl rfl rfl
    change Runs program _ _ _ _ (Function.update (data i w1) (aux .activationReader) (i.activation++[])) at h
    simpa only [List.append_nil,update_activation] using h
  have h2 : Runs program (5*i.scopes.length+4) (.local .copyScopes) (data i w2)
      (.local .copyOrders) (data i w3):=by
    have h:=Q.copy_call .scopes (.local .copyScopes) (.local .copyOrders) rfl (data i w2) i.scopes [] rfl rfl rfl
    change Runs program _ _ _ _ (Function.update (data i w2) (aux .scopesReader) (i.scopes++[])) at h
    simpa only [List.append_nil,update_scopes] using h
  have h3 : Runs program (5*i.orders.length+4) (.local .copyOrders) (data i w3)
      (.local .recordTag) (data i w4):=by
    have h:=Q.copy_call .orders (.local .copyOrders) (.local .recordTag) rfl (data i w3) i.orders [] rfl rfl rfl
    change Runs program _ _ _ _ (Function.update (data i w3) (aux .ordersReader) (i.orders++[])) at h
    simpa only [List.append_nil,update_orders] using h
  have h:=Q.join (Q.join (Q.join h0 h1) h2) h3
  rw [initial_data]
  have hc : 5*streamBytes i+16=(5*i.records.length+4+(5*i.activation.length+4)+(5*i.scopes.length+4))+(5*i.orders.length+4):=by
    unfold streamBytes
    omega
  rw [hc]
  exact h
end RiemannGaussian.SemiprimeD1StackOldVertexStreamSetup
