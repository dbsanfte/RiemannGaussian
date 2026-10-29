/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackWeightedModeCataloguePrimitives
/-! # Paid actual packet/tile product and physical WIDTH predecessor
Packet and tile counts are explicit acquired metadata inputs. The original
packet constructor is not supplied or claimed by this internal source.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackWeightedModeCatalogueAcquisition
open SemiprimeD1StackWeightedModeCatalogue SemiprimeD1StackWeightedModeCatalogueView
open SemiprimeD1StackWeightedModeCataloguePrimitives
open SemiprimeD1StackWeightedModeView (unary unary_length)
open SemiprimeD1StackProcedureTrace
local notation "ctl" => (Sum.inl :Control→Label)
/-- Only the actual three metadata operands are initially present. -/
def original (p t width:Nat):Words:=
  {enumData:=W.input [] (unary width),productData:=M.data (unary p) (unary t) [] [] [] [] []}
/-- The literal initialized physical store equals the word view, including every zero work word. -/
theorem initial_store (p t width:Nat):input (unary p) (unary t) (unary width)=store (original p t width):=by
  funext k
  rcases k with k|k
  · cases k <;> rfl
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
/-- A real nested source call computes the product; no slot count is an input. -/
theorem product_call (p t width:Nat):
    ∃time ≤5*p+5*(p*(2*t+3)+1)+11,Runs program time (ctl .start)
      (store (original p t width)) (ctl .copyWidth)
      (store {original p t width with productData:=M.data (unary p) (unary t) [] [] [] [] (unary (p*t))}):=by
  obtain ⟨time,ht,hr⟩:=SemiprimeD1StackPortOwnerMaddExecution.source_run p t 0
  refine ⟨time+1,by omega,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program multiply multiplyLabel multiply_injective
    M.program (.inl .start) (fun _=>rfl) (ctl .start) (ctl .copyWidth) rfl time
    (SemiprimeD1StackPortOwnerMaddExecution.initial p t 0)
    (SemiprimeD1StackPortOwnerMaddExecution.done p t 0) _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k;rcases k with k|k <;> cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;rcases k with k|k <;> cases k <;> rfl
    · intro k hk
      rcases k with k|k
      · rfl
      · rcases k with k|k
        · exact False.elim (hk k rfl)
        · cases k <;> rfl
/-- The two source copies and real budget pop enter the actual order loop. -/
theorem setup_run (p t width:Nat):
    ∃time ≤5*p+5*(p*(2*t+3)+1)+5*width+17,Runs program time (ctl .start)
      (input (unary p) (unary t) (unary width)) (ctl .orderCheck)
      (store (scanning p t width (width-1) 0 0 0 [] [])):=by
  obtain ⟨u,hu,h0⟩:=product_call p t width
  let a:Words:={original p t width with productData:=M.data (unary p) (unary t) [] [] [] [] (unary (p*t))}
  let b:Words:={a with orders:=unary width}
  let c:Words:={b with orders:=unary (width-1)}
  have h1:=copy_call false .copyWidth .precisionPred rfl (store a) (unary width) [] rfl rfl rfl
  rw [List.append_nil,store_write,unary_length] at h1
  change Runs program (5*width+4) _ _ _ (store b) at h1
  have h2:=pop_run .precisionPred .weightSeed .weightSeed .weightSeed (aux .orders) (store b) (unary width) rfl rfl
  have hchoose:SemiprimeD1StackBytecode.choose (ctl .weightSeed) (ctl .weightSeed) (ctl .weightSeed)
      (unary width).head?=ctl .weightSeed:=by cases (unary width).head? with
    | none=>rfl
    | some b=>cases b <;> rfl
  rw [hchoose,SemiprimeD1StackWeightedModeExecution.unary_tail,store_write] at h2
  change Runs program 1 _ _ _ (store c) at h2
  have h3:=push_run .weightSeed .orderCheck (aux .weight) true (store c) rfl
  rw [store_write] at h3
  change Runs program 1 _ _ _ (store (scanning p t width (width-1) 0 0 0 [] [])) at h3
  have h:=join h0 (join h1 (join h2 h3))
  rw [initial_store]
  refine ⟨u+((5*width+4)+(1+1)),by omega,h⟩
end RiemannGaussian.SemiprimeD1StackWeightedModeCatalogueAcquisition
