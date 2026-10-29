/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryActivationSource
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryActivationMeaning
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryActivationResults
/-! # Whole physical activation from the actual original selected-ID cache
Every original ID, including an isolated vertex, is visited in numeric order.
The prepared source inputs remain ONLY the thirteen real cache/header words.
The original-N/cache-to-caller join and the later topology loops are separate.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryActivationOriginal
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackChildGroupFactoryActivation SemiprimeD1StackChildGroupFactoryActivationView
open SemiprimeD1StackChildGroupFactoryActivationLoop SemiprimeD1StackChildGroupFactoryActivationMeaning
open SemiprimeD1StackChildGroupFactoryActivationResults SemiprimeD1StackProcedureTrace
namespace Source
export SemiprimeD1StackChildGroupFactoryActivationSource (result timeBound source_trace)
end Source
/-- The literal stopped output log equals the exact original all-ID native activation scan. -/
theorem output_original (i:Inputs) (a coordinate:Nat) (ids:List (List Bool))
    (hm:∀id∈ids,id∈(SemiprimeSourceCompactWordBank.acquire 64 a).ids):
    Source.result i coordinate (plan a ids [] ids.reverse) (aux .activation)=
      (SemiprimeD1ChildActivation.scan (SemiprimeSourceHistogramRows.acquire 64 a)
        a coordinate i.group ids.reverse).bits:=by
  change (finish i coordinate [] [] [false] (plan a ids [] ids.reverse)).history.reverse=_
  rw [finish_history]
  simp only [List.append_nil,List.reverse_reverse]
  rw [plan_flags,SemiprimeD1ChildActivation.scan_bits]
  apply List.map_congr_left
  intro id hid
  exact active_original i a coordinate id (hm id (List.mem_reverse.mp hid))
/-- All row-validity/classification obligations follow from the acquired original cache itself. -/
theorem source_original (i:Inputs) (a coordinate:Nat) (ids:List (List Bool))
    (hm:∀id∈ids,id∈(SemiprimeSourceCompactWordBank.acquire 64 a).ids)
    (he:i.environment=SemiprimeD1StackSourceEnvironmentEncoding.dictionary ids)
    (hc:i.catalogue=SemiprimeD1StackPacketRowsOriginal.catalogue a)
    (hi:i.colourIndex=List.replicate coordinate true)
    (hlen:ids.length=i.owners.length+i.factors.length):
    ∃t≤Source.timeBound i coordinate (Env.prefixRows ids) (Palette.originalEntries 64 a)
        (plan a ids [] ids.reverse),
      Runs program t entry (input i) (.local 2 18) (Source.result i coordinate (plan a ids [] ids.reverse)) ∧
      Source.result i coordinate (plan a ids [] ids.reverse) (aux .activation)=
        (SemiprimeD1ChildActivation.scan (SemiprimeSourceHistogramRows.acquire 64 a)
          a coordinate i.group ids.reverse).bits:=by
  have henv:i.environment=SemiprimeD1StackOwnerLookup.records (Env.prefixRows ids) []:=he
  have hcat:i.catalogue=SemiprimeD1StackOwnerLookup.records (Palette.originalEntries 64 a) []:=
    hc.trans (SemiprimeD1StackPacketRowsMeaning.catalogue_original a).symm
  obtain ⟨t,ht,hr⟩:=Source.source_trace i coordinate (Env.prefixRows ids) (Palette.originalEntries 64 a)
    henv hcat hi (plan a ids [] ids.reverse)
    (by simpa only [plan_length,List.length_reverse] using hlen) (plan_valid_all a ids hm)
  exact ⟨t,ht,hr,output_original i a coordinate ids hm⟩
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryActivationOriginal
