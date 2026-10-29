/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryNodeInventory
/-! # All140 retained fields and direct actual six-word weight input projection -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryNodeView
open SemiprimeD1StackRecoveryNode SemiprimeD1StackRecoveryNodeInventory
namespace A
export SemiprimeD1StackRecoveryAffine (Stack rational aux grid)
end A
namespace V
export SemiprimeD1StackRecoveryNodeInputsView (result old_retained)
end V
/-- The old entire140-word stopped bank is actually present; only freshoutput is EMPTY. -/
def empty (old:N.Stack→List Bool):Stack→List Bool:=bank old []
/-- Only the ONE new chronological whole-weight output is added. -/
def result (old:N.Stack→List Bool) (out:List Bool):Stack→List Bool:=Function.update (empty old) output out
/-- Every actual source/cache/shadow of Node140 is retained literally. -/
theorem old_retained (old:N.Stack→List Bool) (out:List Bool) (role:N.Stack):
    result old out (node role)=old role:=by
  rw [result,Function.update_of_ne (by simp [node,output])]
  rfl
/-- A retained Node inverse register is physically empty after the complete actual source. -/
theorem reg_empty (old:A.Stack→List Bool) (inv pow:List Bool) (cache:I.Reg×Bool):
    V.result old inv pow (N.inverseReg cache)=[]:=by
  change Function.update (SemiprimeD1StackRecoveryNodeInputsView.afterInverse old inv) (SemiprimeD1StackRecoveryNodeInputs.powersWork 7) pow (N.inverseReg cache)=[]
  rw [Function.update_of_ne (by simp [SemiprimeD1StackRecoveryNodeInputs.powersWork,SemiprimeD1StackRecoveryNodeInputs.inverseReg])]
  change Function.update (SemiprimeD1StackRecoveryNodeInputsView.empty old) (N.inverseWork 11) inv (N.inverseReg cache)=[]
  rw [Function.update_of_ne (by simp [SemiprimeD1StackRecoveryNodeInputs.inverseWork,SemiprimeD1StackRecoveryNodeInputs.inverseReg])]
  rfl
/-- All actual Node inverse-private words are empty except its complete retained output. -/
theorem work_word (old:A.Stack→List Bool) (inv pow:List Bool) (i:Fin 12):
    V.result old inv pow (N.inverseWork i)=if i=11 then inv else []:=by
  change Function.update (SemiprimeD1StackRecoveryNodeInputsView.afterInverse old inv) (SemiprimeD1StackRecoveryNodeInputs.powersWork 7) pow (N.inverseWork i)=_
  rw [Function.update_of_ne (by simp [SemiprimeD1StackRecoveryNodeInputs.powersWork,SemiprimeD1StackRecoveryNodeInputs.inverseWork])]
  change Function.update (SemiprimeD1StackRecoveryNodeInputsView.empty old) (N.inverseWork 11) inv (N.inverseWork i)=_
  by_cases hi:i=11
  · subst i;rw [Function.update_self,ite_eq_left rfl]
  · rw [Function.update_of_ne (by intro he;apply hi;exact Sum.inr.inj (Sum.inl.inj (Sum.inr.inj he))),ite_eq_right hi]
    rfl
/-- Exact acquired power-array word, with no private-power source getter. -/
theorem powers_word (old:A.Stack→List Bool) (inv pow:List Bool):
    V.result old inv pow N.powersOutput=pow:=by
  unfold V.result
  rw [Function.update_self]
/-- Complete actual weight input projection has no supplied inverse/powers/scalar/q answers. -/
theorem weight_initial (old:A.Stack→List Bool) (inv pow signed den q width:List Bool)
    (hr:∀role,old (A.rational role)=if role=SemiprimeD1StackRationalOperation.aux .template then width else [])
    (hss:old (A.grid (SemiprimeD1StackRecoveryGrid.reg .scalar false))=signed)
    (hsd:old (A.grid (SemiprimeD1StackRecoveryGrid.reg .scalar true))=den)
    (hq:old (A.aux .retainedQ)=q):
    SemiprimeD1StackMultiplierLink.DataRel weight (empty (V.result old inv pow))
      (W.input inv pow signed den q width) (empty (V.result old inv pow)):=by
  constructor
  · intro role
    rcases role with role|role
    · rcases role with role|role|role
      · change V.result old inv pow (N.inverse (.inl role))=_
        exact (V.old_retained old inv pow (A.rational role)).trans (hr role)
      · rcases role with ⟨r,b⟩
        change V.result old inv pow (N.inverseReg (r,b))=[]
        exact reg_empty old inv pow (r,b)
      · cases role
        · change V.result old inv pow (N.inverseWork 11)=inv
          exact work_word old inv pow 11
        · change V.result old inv pow (SemiprimeD1StackRecoveryNodeInputs.affine (A.aux .retainedQ))=q
          exact (V.old_retained old inv pow _).trans hq
        all_goals first
          | (change V.result old inv pow N.powersOutput=pow;exact powers_word old inv pow)
          | rfl
    · cases role
      · change V.result old inv pow (SemiprimeD1StackRecoveryNodeInputs.affine (A.grid (SemiprimeD1StackRecoveryGrid.reg .scalar false)))=signed
        exact (V.old_retained old inv pow _).trans hss
      · change V.result old inv pow (SemiprimeD1StackRecoveryNodeInputs.affine (A.grid (SemiprimeD1StackRecoveryGrid.reg .scalar true)))=den
        exact (V.old_retained old inv pow _).trans hsd
  · intro role _;rfl
/-- The real stopped weight source differs from its initial six-input bank ONLY at output. -/
theorem weight_result (inv pow:List SemiprimeRationalBits.RationalWord) (scalar:SemiprimeRationalBits.RationalWord) (q:ℕ) (width:List Bool):
    SemiprimeD1StackRecoveryWeightsExecution.result inv pow scalar q width=
      Function.update (W.input (SemiprimeD1StackNormalizedInverse.tape inv) (SemiprimeD1StackNormalizedInverse.tape pow)
        (SemiprimeD1StackNormalizedInverse.signed scalar) scalar.denominator (List.replicate q true) width)
        (W.aux .output) (SemiprimeD1StackNormalizedInverse.tape (SemiprimeD1StackRecoveryWeightsSpec.array width q scalar inv pow)):=by
  funext role
  rcases role with role|role
  · rcases role with role|role|role
    · simp [SemiprimeD1StackRecoveryWeightsExecution.result,SemiprimeD1StackRecoveryWeightsOuterView.outer,
        SemiprimeD1StackRecoveryWeightsView.bank,W.input,W.aux,SemiprimeD1StackRecoveryWeights.helper,
        SemiprimeD1StackNormalizedInverse.aux,SemiprimeD1StackNormalizedInverseView.store,SemiprimeD1StackNormalizedInverseView.emptyRational,SemiprimeD1StackNormalizedInverse.bank]
    · rfl
    · cases role <;> rfl
  · cases role <;> rfl
end RiemannGaussian.SemiprimeD1StackRecoveryNodeView
