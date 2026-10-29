/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackVertexArityStatic
import RiemannGaussian.SemiprimeD1StackVertexArityArithmetic
import RiemannGaussian.SemiprimeD1StackVertexArityDecode

/-! # Every actual original arity recipe, with uniform quadratic execution bound -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option synthInstance.maxSize 8192
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackVertexArityRecipes
open SemiprimeD1StackVertexArity SemiprimeD1StackVertexArityView
open SemiprimeD1StackVertexArityStatic SemiprimeD1StackVertexArityArithmetic SemiprimeD1StackVertexArityDecode
open SemiprimeD1StackProcedureFragments (Runs)
open SemiprimeD1StackUnaryDivmod (unary)

/-- Mathematical value of the actual static recipe; not an executable graph-arity supplier. -/
def value (code:Fin 18) (index radius first second digits:ℕ) : ℕ :=
  if code.val=0 then radius+(if index<digits then 1 else 0)
  else if code.val=1 then second*radius+second*radius
  else if code.val=2 then radius+radius
  else if code.val=3 then first*radius+first*radius
  else if code.val=4 then radius+(radius+radius)
  else if code.val=5 then radius
  else if code.val=6 then radius+(radius+radius)
  else if code.val=7 then radius
  else if code.val=8 then 3
  else if code.val=9 then 1 else 2
/-- Actual source-counter size parameter, kept separate from logical graph scope. -/
def dimensionSum (index radius first second digits:ℕ) : ℕ := index+radius+first+second+digits+1
/-- One fixed quadratic recipe envelope in actual unary metadata lengths. -/
def recipeBudget (index radius first second digits:ℕ) : ℕ := 100*(dimensionSum index radius first second digits)^2+100

/-- Pure scalar product substitution; no executable term is unfolded here. -/
theorem product_budget_le (axis radius S:ℕ) (ha:axis≤S) (hr:radius≤S) :
    productBudget axis radius≤100*S^2+100 := by
  have hm:(axis+axis)*(2*radius+3)≤(S+S)*(2*S+3):=Nat.mul_le_mul (by omega) (by omega)
  unfold productBudget
  nlinarith
/-- Pure scalar comparison/copy substitution. -/
theorem input_budget_le (index radius digits S:ℕ) (hi:index≤S) (hr:radius≤S) (hd:digits≤S) (hp:1≤S) :
    inputBudget index radius digits≤100*S^2+100 := by
  have hs:S≤S^2:=by nlinarith
  unfold inputBudget
  omega
/-- Three readonly-source copies dominate every radius-only recipe. -/
theorem radius_budget_le (radius S:ℕ) (hr:radius≤S) (hp:1≤S) : 15*radius+12≤100*S^2+100 := by
  have hs:S≤S^2:=by nlinarith
  omega
/-- All eighteen recipes execute actual instructions and return the original-value tally. -/
theorem recipe_run (code:Fin 18) (index radius first second digits:ℕ) :
    ∃time≤recipeBudget index radius first second digits,Runs program time (recipe code)
      (store (header code.val index radius first second digits) [] [] [] [] [] []) (.inl .halt)
      (store (header code.val index radius first second digits) (unary (value code index radius first second digits)) [] [] [] [] []) := by
  let S:=dimensionSum index radius first second digits
  have hi:index≤S:=by dsimp [S,dimensionSum];omega
  have hr:radius≤S:=by dsimp [S,dimensionSum];omega
  have hf:first≤S:=by dsimp [S,dimensionSum];omega
  have hs:second≤S:=by dsimp [S,dimensionSum];omega
  have hd:digits≤S:=by dsimp [S,dimensionSum];omega
  have hp:1≤S:=by dsimp [S,dimensionSum];omega
  have hbI:inputBudget index radius digits≤recipeBudget index radius first second digits:=input_budget_le _ _ _ S hi hr hd hp
  have hbF:productBudget first radius≤recipeBudget index radius first second digits:=product_budget_le _ _ S hf hr
  have hbS:productBudget second radius≤recipeBudget index radius first second digits:=product_budget_le _ _ S hs hr
  have hbR:15*radius+12≤recipeBudget index radius first second digits:=radius_budget_le _ S hr hp
  have hbL:3≤recipeBudget index radius first second digits:=by unfold recipeBudget;omega
  fin_cases code
  · obtain ⟨time,ht,he⟩:=input_run 0 index radius first second digits
    exact ⟨time,ht.trans hbI,he⟩
  · obtain ⟨time,ht,he⟩:=axis_run false 1 index radius first second digits
    exact ⟨time,ht.trans hbS,he⟩
  · exact ⟨10*radius+8,by omega,radius_two 2 index radius first second digits⟩
  · obtain ⟨time,ht,he⟩:=axis_run true 3 index radius first second digits
    exact ⟨time,ht.trans hbF,he⟩
  · exact ⟨15*radius+12,hbR,radius_three 4 index radius first second digits⟩
  · exact ⟨5*radius+4,by omega,radius_one 5 index radius first second digits⟩
  · exact ⟨15*radius+12,hbR,radius_three 6 index radius first second digits⟩
  · exact ⟨5*radius+4,by omega,radius_one 7 index radius first second digits⟩
  · exact ⟨3,hbL,literal_three _ []⟩
  · exact ⟨1,by omega,literal_one _ []⟩
  all_goals exact ⟨2,by omega,literal_two _ []⟩

/-- Whole actual copy/decode/recipe trace, before the caller's final halt instruction. -/
theorem ready (code:Fin 18) (index radius first second digits:ℕ) :
    ∃time≤recipeBudget index radius first second digits+107,Runs program time (.inl .main)
      (store (header code.val index radius first second digits) [] [] [] [] [] []) (.inl .halt)
      (store (header code.val index radius first second digits) (unary (value code index radius first second digits)) [] [] [] [] []) := by
  have h0:=tag_run code index radius first second digits
  obtain ⟨time,ht,h1⟩:=recipe_run code index radius first second digits
  refine ⟨(6*code.val+5)+time,?_,h0.trans h1⟩
  have hc:=code.isLt
  omega
end RiemannGaussian.SemiprimeD1StackVertexArityRecipes
