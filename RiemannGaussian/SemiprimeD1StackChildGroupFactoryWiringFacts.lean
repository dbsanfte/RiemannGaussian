/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryWiring
/-! # Physical disjointness at every actual fixed source call
All finite cases concern literal program wiring, never input metadata.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryWiringFacts
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
/-- Generic three-port physical disjointness before concrete source substitution. -/
theorem three_injective {K:Type} (x y z:K)
    (hxy:x≠y) (hxz:x≠z) (hyz:y≠z):
    Function.Injective (fun k:Fin 3=>if k=0 then x else if k=1 then y else z):=by
  intro a b h
  fin_cases a <;> fin_cases b <;> first | rfl | simp_all
/-- Each copy's source/destination/restoration scratch are actual distinct words. -/
theorem copy_disjoint (site:Fin 38):
    (copyPorts site).1≠(copyPorts site).2 ∧
      (copyPorts site).1≠aux .copyScratch ∧(copyPorts site).2≠aux .copyScratch:=by
  fin_cases site <;> decide
/-- Every real preserving copy has an injective inclusion. -/
theorem copy_injective (site:Fin 38):Function.Injective (copyStack site):=by
  exact three_injective _ _ _ (copy_disjoint site).1 (copy_disjoint site).2.1 (copy_disjoint site).2.2
/-- Every actual frame source/destination is disjoint from the restored scratch. -/
theorem frame_disjoint (site:Fin 25):
    (framePorts site).1≠(framePorts site).2 ∧
      (framePorts site).1≠aux .copyScratch ∧(framePorts site).2≠aux .copyScratch:=by
  fin_cases site <;> decide
/-- Every real field-frame has an injective inclusion. -/
theorem frame_injective (site:Fin 25):Function.Injective (frameStack site):=by
  exact three_injective _ _ _ (frame_disjoint site).1 (frame_disjoint site).2.1 (frame_disjoint site).2.2
/-- Every reversal consumes a physically distinct source. -/
theorem reverse_disjoint (site:Fin 16):(reversePorts site).1≠(reversePorts site).2:=by
  fin_cases site <;> decide
/-- Actual source/destination projections prove every reversal inclusion injective. -/
theorem reverse_injective (site:Fin 16):Function.Injective (reverseStack site):=by
  have hn:=reverse_disjoint site
  have hnr:=Ne.symm hn
  intro a b h
  fin_cases a <;> fin_cases b <;> first | rfl | simp_all [reverseStack]
/-- Parser input/output are disjoint from one another and from its private roles. -/
theorem field_disjoint (site:Fin 21):
    (fieldPorts site).1≠(fieldPorts site).2 ∧
    (fieldPorts site).1≠field (.inl .scratch) ∧(fieldPorts site).2≠field (.inl .scratch) ∧
    (fieldPorts site).1≠field (.inr ()) ∧(fieldPorts site).2≠field (.inr ()):=by
  fin_cases site <;> decide
/-- Every real four-role Field inclusion is injective, including both unused shadows. -/
theorem field_injective (site:Fin 21):Function.Injective (fieldStack site):=by
  obtain ⟨h0,h1,h2,h3,h4⟩:=field_disjoint site
  have h0r:=Ne.symm h0
  have h1r:=Ne.symm h1
  have h2r:=Ne.symm h2
  have h3r:=Ne.symm h3
  have h4r:=Ne.symm h4
  intro a b h
  rcases a with a|a <;> rcases b with b|b <;> cases a <;> cases b <;>
    first | rfl | simp_all [fieldStack,field]
/-- The complete11-role lookup image remains physically distinct. -/
theorem lookup_injective:Function.Injective lookup:=Sum.inl_injective
/-- The complete19-role reader image remains physically distinct. -/
theorem rows_injective:Function.Injective rows:=by intro a b h;exact Sum.inl_injective (Sum.inr_injective h)
/-- Actual full-adder and equality calls share only the same four distinct words. -/
theorem arithmetic_injective:Function.Injective arithmetic:=by
  intro a b h;exact Sum.inl_injective (Sum.inr_injective (Sum.inr_injective h))
/-- Every allocation of the real12-role ordinal converter remains distinct. -/
theorem ordinal_injective:Function.Injective ordinal:=by
  intro a b h;exact Sum.inl_injective (Sum.inr_injective (Sum.inr_injective (Sum.inr_injective (Sum.inr_injective h))))
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryWiringFacts
