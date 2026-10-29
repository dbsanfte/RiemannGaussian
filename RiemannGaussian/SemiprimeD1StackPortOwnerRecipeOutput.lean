/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortOwnerRecipeDecision
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
namespace RiemannGaussian.SemiprimeD1StackPortOwnerRecipeOutput
open SemiprimeD1StackPortOwnerRecipe SemiprimeD1StackPortOwnerRecipeSpec
open SemiprimeD1StackPortOwnerRecipeEmit SemiprimeD1StackPortOwnerRecipeDecision
/-- The actual cached-field/sentinel emitter agrees with the complete literal arithmetic recipe. -/
theorem output_expected (p:Counters) (tag:Tag) (ht:p.tag=(tagCode tag).val) :
    suffix p (selected p tag) 6=expected p := by
  cases tag <;> cases hh:p.half
  all_goals simp only [selected,hh]
  all_goals try split_ifs
  all_goals simp_all [suffix,word,ready,prepared,atStage,cached,fields,words,arg,reg,
    Function.update,expected,tagCode,SemiprimeD1StackUnaryDivmod.unary,SemiprimeD1PortOwnerArithmeticSpec.routeKey,
    SemiprimeD1PortOwnerArithmeticSpec.route,SemiprimeD1EdgeCatalogueEncoding.fields,
    SemiprimeD1EdgeCatalogueEncoding.record,SemiprimeD1VertexCatalogueModes.code,
    Nat.add_comm,Nat.add_left_comm,Nat.mul_comm]
  all_goals split_ifs <;> first | omega | simp_all
end RiemannGaussian.SemiprimeD1StackPortOwnerRecipeOutput
