/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackVertexProduct
/-! # Declarative register invariants for the actual vertex-product program
These finite functions describe physical configurations in proofs. They are not
arguments to the executed program, coefficient getters or result suppliers.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 65536
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000
namespace RiemannGaussian.SemiprimeD1StackVertexProductState
open SemiprimeD1StackVertexProduct

/-- The thirteen registers that can be live between actual included calls. -/
inductive Slot where
  | axes | precision | vertices | assignment | rank | width | left | product | result | reader | ports | table | valid
  deriving DecidableEq,Repr
instance : Fintype Slot := Fintype.ofList
  [.axes,.precision,.vertices,.assignment,.rank,.width,.left,.product,.result,.reader,.ports,.table,.valid]
  (by intro k; cases k <;> simp)

/-- Exact literal physical addresses of the between-call invariant. -/
def address : Slot → Stack
  | .axes => axes
  | .precision => aux .precisionBits
  | .vertices => aux .verticesCache
  | .assignment => aux .assignment
  | .rank => rank
  | .width => width
  | .left => left
  | .product => product
  | .result => result
  | .reader => aux .verticesReader
  | .ports => aux .ports
  | .table => aux .table
  | .valid => aux .fieldValid

/-- All live slots have genuinely distinct physical registers. -/
theorem address_injective : Function.Injective address := by decide

/-- Proof-side finite word-register values, equivalent to a thirteen-field tuple. -/
abbrev Values := Slot → List Bool

/-- Declarative physical configuration, all unnamed callee workspace empty. -/
def data (v : Values) (k : Stack) : List Bool :=
  if k=address .axes then v .axes else
  if k=address .precision then v .precision else
  if k=address .vertices then v .vertices else
  if k=address .assignment then v .assignment else
  if k=address .rank then v .rank else
  if k=address .width then v .width else
  if k=address .left then v .left else
  if k=address .product then v .product else
  if k=address .result then v .result else
  if k=address .reader then v .reader else
  if k=address .ports then v .ports else
  if k=address .table then v .table else
  if k=address .valid then v .valid else []

/-- Every named physical register has its declared contents. -/
theorem data_get (v : Values) (s : Slot) : data v (address s)=v s := by
  cases s <;> simp [data,address_injective.eq_iff]

/-- No hidden work data is present in the between-call invariant. -/
theorem data_other (v : Values) (k : Stack) (hk : ∀s,k ≠ address s) : data v k=[] := by
  simp [data,hk]

/-- Exact physical stack replacement agrees with the finite register invariant. -/
theorem data_update (v : Values) (s : Slot) (word : List Bool) :
    data (Function.update v s word)=Function.update (data v) (address s) word := by
  funext k
  by_cases hex : ∃t,k=address t
  · obtain ⟨t,rfl⟩:=hex
    rw [data_get]
    by_cases he : t=s
    · subst t
      simp
    · have hn : address t ≠ address s := fun hh=>he (address_injective hh)
      simp only [Function.update_of_ne he,Function.update_of_ne hn,data_get]
  · have hk : ∀s,k ≠ address s := by simpa only [not_exists] using hex
    rw [data_other _ _ hk,Function.update_of_ne (hk s),data_other _ _ hk]

/-- Finite original headers, acquired context and between-call buffers. -/
def values (axes precision vertices assignment rank width left product result reader ports table valid : List Bool) : Values
  | .axes => axes
  | .precision => precision
  | .vertices => vertices
  | .assignment => assignment
  | .rank => rank
  | .width => width
  | .left => left
  | .product => product
  | .result => result
  | .reader => reader
  | .ports => ports
  | .table => table
  | .valid => valid

/-- The actual entry exactly has the four original inputs and no acquired answers. -/
theorem initial_data (axes precision vertices assignment : List Bool) :
    (initial axes precision vertices assignment).data=
      data (values axes precision vertices assignment [] [] [] [] [] [] [] [] []) := by
  funext k
  by_cases hex : ∃s,k=address s
  · obtain ⟨s,rfl⟩:=hex
    rw [data_get]
    cases s <;> rfl
  · have hk : ∀s,k ≠ address s := by simpa only [not_exists] using hex
    rw [data_other _ _ hk]
    have ha : k ≠ SemiprimeD1StackVertexProduct.axes := hk .axes
    have hp : k ≠ aux .precisionBits := hk .precision
    have hv : k ≠ aux .verticesCache := hk .vertices
    have hb : k ≠ aux .assignment := hk .assignment
    simp only [initial,inputData,Function.update_of_ne hb,Function.update_of_ne hv,
      Function.update_of_ne hp,Function.update_of_ne ha]

end RiemannGaussian.SemiprimeD1StackVertexProductState
