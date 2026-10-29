/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackProductTable
/-! # Concrete product-table tape specification and static cleanup inventory
The native definitions here specify the output of the fixed physical program;
none is an initialized table, assignment producer, predicate or arity supplier.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackProductTableSpec
open SemiprimeD1StackProductTable
attribute [local instance] Fintype.decidableForallFintype
namespace TT
export SemiprimeD1TensorTables (Table build lookup)
end TT
/-- Actual original acquired M width determines the three-word product arity. -/
def arity (bits : List Bool) : ℕ :=3*(SemiprimeD1StackPublicProductExecution.cached bits).length
/-- The actual computed product checker Boolean, used only as a specification. -/
def answer (bits raw : List Bool) : Bool :=
  SemiprimeD1StackProductCheckExecution.answer raw (SemiprimeD1StackPublicProductExecution.cached bits)
/-- Literal root-context coefficient vector of the computed Boolean. -/
def leafWords (bits raw : List Bool) : List (List Bool) :=[if answer bits raw then [true] else []]
/-- False-first full tree over the original prefix order. This is a proof-side
output specification, not a callback or native table in executing control. -/
def tree (bits front : List Bool) : (n : ℕ)→TT.Table n
  | 0=>.leaf (leafWords bits front)
  | n+1=>.fork (tree bits (front++[false]) n) (tree bits (front++[true]) n)
/-- Exact original-N output tape sought by the closed physical acquirer. -/
def outputTape (bits : List Bool) : List Bool :=SemiprimeD1TensorTapeCodec.tape (tree bits [] (arity bits))
/-- Static role cleanup visits no checker role twice. -/
theorem checkerRoles_nodup : checkerRoles.Nodup := by decide
/-- Static cleanup covers EVERY role, including dormant private shadows. -/
theorem checkerRoles_complete : ∀k : P.Stack,k∈checkerRoles := by
  have h : checkerRoles.toFinset=(Finset.univ : Finset P.Stack) := by decide
  intro k
  have hk : k∈checkerRoles.toFinset := by rw [h];exact Finset.mem_univ k
  exact List.mem_toFinset.mp hk
/-- Every static role lookup is genuinely inside the closed finite table. -/
theorem clearRole_eq (pos : Fin 76) :
    clearRole pos=.inl (checkerRoles[pos.val]'(by rw [checkerRoles_length];exact pos.isLt)) := by
  rw [clearRole,List.getElem?_eq_getElem (by rw [checkerRoles_length];exact pos.isLt),Option.getD_some]
/-- Cleanup's literal role table reaches every actual checker register. -/
theorem clearRole_complete (k : P.Stack) : ∃pos : Fin 76,clearRole pos=.inl k := by
  obtain ⟨j,hj,h⟩:=List.mem_iff_getElem.mp (checkerRoles_complete k)
  have hlt : j<76 := by simpa only [checkerRoles_length] using hj
  refine ⟨⟨j,hlt⟩,?_⟩
  rw [clearRole_eq,h]
/-- Literal zero leaf code equals the frozen tree/vector framing. -/
theorem zero_code : List.ofFn zeroBits=SemiprimeD1TensorTapeCodec.tape (SemiprimeD1TensorTables.Table.leaf [[]]) := by decide
/-- Literal accepted leaf code preserves the original compact one word. -/
theorem one_code : List.ofFn oneBits=SemiprimeD1TensorTapeCodec.tape (SemiprimeD1TensorTables.Table.leaf [[true]]) := by decide
end RiemannGaussian.SemiprimeD1StackProductTableSpec
