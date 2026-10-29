/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortOwnerRoutingExecution
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackOwnerFibreRetained
/-- EVERY actual original E-map source word survives the whole factor-major routing source. -/
theorem routing_map (bits:List Bool) (hN:0<SemiprimeBitArithmetic.bitValue bits)
    (k:SemiprimeD1StackOwnerCatalogue.Stack) :
    (SemiprimeD1StackPortOwnerRoutingExecution.done bits hN).data
      (SemiprimeD1StackPortOwnerRouting.mapStack k)=(SemiprimeD1StackOwnerCatalogueExecution.done bits).data k:=rfl
/-- EVERY actual original Root83 source word survives complete E-map construction. -/
theorem catalogue_root (bits:List Bool) (k:SemiprimeD1StackRootScopeBank.Stack) :
    (SemiprimeD1StackOwnerCatalogueExecution.done bits).data (SemiprimeD1StackOwnerCatalogue.source k)=
      SemiprimeD1StackRootScopeBankExecution.result bits k:=rfl
end RiemannGaussian.SemiprimeD1StackOwnerFibreRetained
