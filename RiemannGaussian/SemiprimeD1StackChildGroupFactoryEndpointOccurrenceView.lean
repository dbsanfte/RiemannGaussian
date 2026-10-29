/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryEndpointOccurrence
/-! # Exact full-bank invariants of the actual complete incidence source -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryEndpointOccurrenceView
open SemiprimeD1StackChildGroupFactoryRoles
open SemiprimeD1StackChildGroupFactoryEndpointOccurrence
/-- Neither actual side call changes a role outside the two acquired log histories. -/
theorem factorBank_other (ownerFlag factorFlag:Bool) (before:Stack→List Bool) (f:Parse.Fields)
    (pairTail placementTail:List Bool) (k:Stack) (ho:k≠aux .oldHistory) (he:k≠aux .endpointHistory):
    factorBank ownerFlag factorFlag before f pairTail placementTail k=parsedBank before f pairTail placementTail k:=by
  calc
    _=ownerBank ownerFlag before f pairTail placementTail k:=
      SemiprimeD1StackChildGroupFactoryEndpointSide.result_other false factorFlag
        (ownerBank ownerFlag before f pairTail placementTail) f.factor f.packet f.slot f.edge k ho he
    _=parsedBank before f pairTail placementTail k:=
      SemiprimeD1StackChildGroupFactoryEndpointSide.result_other true ownerFlag
        (parsedBank before f pairTail placementTail) f.owner f.packet f.slot f.edge k ho he
/-- All non-field/non-history roles retain the actual paired parser's exact byte values. -/
theorem result_outside_fields (ownerFlag factorFlag:Bool) (before:Stack→List Bool) (f:Parse.Fields)
    (pairTail placementTail:List Bool) (k:Stack) (hf:∀j,Cleanup.role j≠k)
    (ho:k≠aux .oldHistory) (he:k≠aux .endpointHistory):
    result ownerFlag factorFlag before f pairTail placementTail k=parsedBank before f pairTail placementTail k:=by
  unfold result
  rw [SemiprimeD1StackChildGroupFactoryEndpointCleanup.result_other _ k hf]
  exact factorBank_other ownerFlag factorFlag before f pairTail placementTail k ho he
/-- Every foreign source/cache/private word outside readers and logs is retained literally. -/
theorem result_other (ownerFlag factorFlag:Bool) (before:Stack→List Bool) (f:Parse.Fields)
    (pairTail placementTail:List Bool) (k:Stack) (hf:∀j,Cleanup.role j≠k)
    (hpair:k≠aux .pairReader) (hplacement:k≠aux .placementReader)
    (ho:k≠aux .oldHistory) (he:k≠aux .endpointHistory):
    result ownerFlag factorFlag before f pairTail placementTail k=before k:=by
  rw [result_outside_fields ownerFlag factorFlag before f pairTail placementTail k hf ho he]
  have h0:=Ne.symm (hf 0)
  have h1:=Ne.symm (hf 1)
  have h2:=Ne.symm (hf 2)
  have h3:=Ne.symm (hf 3)
  have h4:=Ne.symm (hf 4)
  have h5:=Ne.symm (hf 5)
  have h6:=Ne.symm (hf 6)
  simp only [SemiprimeD1StackChildGroupFactoryEndpointCleanup.role] at h0 h1 h2 h3 h4 h5 h6
  simp only [parsedBank,Parse.result,Function.update_of_ne h6,Function.update_of_ne h5,
    Function.update_of_ne h4,Function.update_of_ne h3,Function.update_of_ne h2,Function.update_of_ne h1,
    Function.update_of_ne h0,Function.update_of_ne hplacement,Function.update_of_ne hpair]
/-- The actual pair reader advances by exactly the two actual fields. -/
theorem result_pair (ownerFlag factorFlag:Bool) (before:Stack→List Bool) (f:Parse.Fields)
    (pairTail placementTail:List Bool):
    result ownerFlag factorFlag before f pairTail placementTail (aux .pairReader)=pairTail:=by
  rw [result_outside_fields ownerFlag factorFlag before f pairTail placementTail (aux .pairReader)
    (by intro j;fin_cases j <;> decide) (by decide) (by decide)]
  rfl
/-- The actual placement reader advances by exactly one complete six-field record. -/
theorem result_placement (ownerFlag factorFlag:Bool) (before:Stack→List Bool) (f:Parse.Fields)
    (pairTail placementTail:List Bool):
    result ownerFlag factorFlag before f pairTail placementTail (aux .placementReader)=placementTail:=by
  rw [result_outside_fields ownerFlag factorFlag before f pairTail placementTail (aux .placementReader)
    (by intro j;fin_cases j <;> decide) (by decide) (by decide)]
  rfl
/-- Both real original tags are acquired unconditionally, owner BEFORE factor in the final forward stream. -/
theorem result_oldHistory (ownerFlag factorFlag:Bool) (before:Stack→List Bool) (f:Parse.Fields)
    (pairTail placementTail:List Bool):
    result ownerFlag factorFlag before f pairTail placementTail (aux .oldHistory)=
      (SemiprimeD1StackChildGroupFactoryEndpointOldLog.row false f.factor f.edge).reverse++
      (SemiprimeD1StackChildGroupFactoryEndpointOldLog.row true f.owner f.edge).reverse++before (aux .oldHistory):=by
  unfold result
  rw [SemiprimeD1StackChildGroupFactoryEndpointCleanup.result_other _ (aux .oldHistory)
    (by intro j;fin_cases j <;> decide)]
  cases ownerFlag <;> cases factorFlag <;> simp [factorBank,ownerBank,parsedBank,Side.result,Parse.result,aux,List.append_assoc]
/-- Exact selected-row bytes from the actual computed flags. -/
def selectedRow (owner flag:Bool) (f:Parse.Fields):List Bool:=
  if flag then (SemiprimeD1StackChildGroupFactoryEndpointEmit.row owner
    (if owner then f.owner else f.factor) f.packet f.slot f.edge).reverse else []
/-- Every actual selected row remains in the literal original owner-BEFORE-factor order. -/
theorem result_endpointHistory (ownerFlag factorFlag:Bool) (before:Stack→List Bool) (f:Parse.Fields)
    (pairTail placementTail:List Bool):
    result ownerFlag factorFlag before f pairTail placementTail (aux .endpointHistory)=
      selectedRow false factorFlag f++selectedRow true ownerFlag f++before (aux .endpointHistory):=by
  unfold result
  rw [SemiprimeD1StackChildGroupFactoryEndpointCleanup.result_other _ (aux .endpointHistory)
    (by intro j;fin_cases j <;> decide)]
  cases ownerFlag <;> cases factorFlag <;> simp [factorBank,ownerBank,parsedBank,Side.result,Parse.result,selectedRow,aux,List.append_assoc]
/-- All parser outputs/flags/scratch are clean before the next REAL paired source read. -/
theorem result_clean (ownerFlag factorFlag:Bool) (before:Stack→List Bool) (f:Parse.Fields)
    (pairTail placementTail:List Bool) (hc:∀k∈Parse.cleanRoles,before k=[]):
    ∀k∈Parse.cleanRoles,result ownerFlag factorFlag before f pairTail placementTail k=[]:=by
  intro k hk
  simp only [Parse.cleanRoles,List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact SemiprimeD1StackChildGroupFactoryEndpointCleanup.result_role _ 0
  · exact SemiprimeD1StackChildGroupFactoryEndpointCleanup.result_role _ 1
  · exact SemiprimeD1StackChildGroupFactoryEndpointCleanup.result_role _ 2
  · exact SemiprimeD1StackChildGroupFactoryEndpointCleanup.result_role _ 3
  · exact SemiprimeD1StackChildGroupFactoryEndpointCleanup.result_role _ 4
  · exact SemiprimeD1StackChildGroupFactoryEndpointCleanup.result_role _ 5
  · exact SemiprimeD1StackChildGroupFactoryEndpointCleanup.result_role _ 6
  all_goals
    rw [result_other ownerFlag factorFlag before f pairTail placementTail _
      (by intro j;fin_cases j <;> decide) (by decide) (by decide) (by decide) (by decide)]
    exact hc _ (by simp [Parse.cleanRoles])
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryEndpointOccurrenceView
