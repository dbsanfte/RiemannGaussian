/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryActivationLoop
/-! # Exact all-vertex activation log and generated-key invariants -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryActivationResults
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryActivationView
open SemiprimeD1StackChildGroupFactoryActivationLoop
/-- Exactly one actual Boolean log cell per real vertex, in reverse accumulation order. -/
theorem finish_history (i:Inputs) (coordinate:Nat) (rows:List Row) (key hist map:List Bool):
    (finish i coordinate key hist map rows).history=
      (rows.map (fun row=>active i coordinate row.colours)).reverse++hist:=by
  induction rows generalizing key hist map with
  | nil=>rfl
  | cons row rows ih=>
    simpa only [finish,List.map_cons,List.reverse_cons,List.append_assoc,List.singleton_append]
      using ih (advance key) (active i coordinate row.colours::hist)
        (true::SemiprimeSourceHistogramKeyBits.frame key
          (SemiprimeSourceHistogramKeyBits.frame [active i coordinate row.colours] map))
/-- Every original numeric vertex key is generated once, even when there are no occurrences. -/
theorem finish_key_value (i:Inputs) (coordinate:Nat) (rows:List Row) (key hist map:List Bool):
    SemiprimeBitArithmetic.bitValue (finish i coordinate key hist map rows).key=
      SemiprimeBitArithmetic.bitValue key+rows.length:=by
  induction rows generalizing key hist map with
  | nil=>simp only [finish,List.length_nil,Nat.add_zero]
  | cons row rows ih=>
    have h:=ih (advance key) (active i coordinate row.colours::hist)
      (true::SemiprimeSourceHistogramKeyBits.frame key
        (SemiprimeSourceHistogramKeyBits.frame [active i coordinate row.colours] map))
    simpa only [finish,advance_value,List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
/-- Only generated bounded metadata grows; neither original numeric N nor a coefficient becomes unary. -/
theorem finish_key_length (i:Inputs) (coordinate:Nat) (rows:List Row) (key hist map:List Bool):
    (finish i coordinate key hist map rows).key.length≤key.length+2*rows.length:=by
  induction rows generalizing key hist map with
  | nil=>simp only [finish,List.length_nil,Nat.mul_zero,Nat.add_zero,le_refl]
  | cons row rows ih=>
    have h:=ih (advance key) (active i coordinate row.colours::hist)
      (true::SemiprimeSourceHistogramKeyBits.frame key
        (SemiprimeSourceHistogramKeyBits.frame [active i coordinate row.colours] map))
    have hk:=advance_length key
    change (finish i coordinate (advance key) (active i coordinate row.colours::hist)
      (true::SemiprimeSourceHistogramKeyBits.frame key
        (SemiprimeSourceHistogramKeyBits.frame [active i coordinate row.colours] map)) rows).key.length≤_
    simp only [List.length_cons]
    omega
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryActivationResults
