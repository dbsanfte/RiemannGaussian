/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1FactorScopePairEncoding
/-! # Exact reached physical stores of the factor-scope projection -/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackFactorScopePairView
open SemiprimeD1StackFactorScopePairs SemiprimeD1FactorScopePairEncoding
/-- All retained source values, nine caches and every actual work register. -/
def data (base : S.Stack→List Bool) (reader : List Bool) (words : Record)
    (raw buffer out valid : List Bool) : Stack→List Bool
  | .inl k=>base k
  | .inr (.inl k)=>words k
  | .inr (.inr .reader)=>reader
  | .inr (.inr .reversed)=>raw
  | .inr (.inr .frameBuffer)=>buffer
  | .inr (.inr .output)=>out
  | .inr (.inr .valid)=>valid
  | _=>[]
/-- Clean loop stores have empty frame buffer, final output and validity cell. -/
def clean (base : S.Stack→List Bool) (reader : List Bool) (words : Record) (raw : List Bool) : Stack→List Bool :=
  data base reader words raw [] [] []
/-- The finite cache after exactly n physical field parses. -/
def parsed (n : Nat) (w : Record) : Record := fun k=>if k.val<n then w k else []
/-- Every actual fixed cache update advances its parser-prefix invariant. -/
theorem parsed_step (w : Record) (part : Fin 9) :
    Function.update (parsed part.val w) part (w part)=parsed (part.val+1) w := by
  funext k
  fin_cases part <;> fin_cases k <;> rfl
/-- All nine fields were actually parsed. -/
theorem parsed_end (w : Record) : parsed 9 w=w := by funext k;fin_cases k <;> rfl
/-- Physical cache updates touch precisely one finite slot. -/
theorem update_cache (base : S.Stack→List Bool) (reader : List Bool) (words : Record)
    (raw buffer out valid value : List Bool) (part : Fin 9) :
    Function.update (data base reader words raw buffer out valid) (cache part) value=
      data base reader (Function.update words part value) raw buffer out valid := by
  funext k
  by_cases hk:k=cache part
  · subst k
    rw [Function.update_self]
    change value=(Function.update words part value) part
    rw [Function.update_self]
  · rw [Function.update_of_ne hk]
    cases k with
    | inl k=>rfl
    | inr k=>cases k with
      | inl j=>
        have hj:j≠part:=by intro h;subst j;exact hk rfl
        change words j=(Function.update words part value) j
        rw [Function.update_of_ne hj]
      | inr j=>cases j <;> rfl
/-- A reader pop changes only the actual reader suffix. -/
theorem update_reader (base : S.Stack→List Bool) (reader next : List Bool) (words : Record)
    (raw buffer out valid : List Bool) :
    Function.update (data base reader words raw buffer out valid) (aux .reader) next=
      data base next words raw buffer out valid := by funext k;rcases k with k|k|k <;> first | rfl | cases k <;> rfl
/-- Parser validity has its own real Boolean cell. -/
theorem update_valid (base : S.Stack→List Bool) (reader : List Bool) (words : Record)
    (raw buffer out valid next : List Bool) :
    Function.update (data base reader words raw buffer out valid) (aux .valid) next=
      data base reader words raw buffer out next := by funext k;rcases k with k|k|k <;> first | rfl | cases k <;> rfl
/-- Reversed output bytes are actual allocated Boolean payload. -/
theorem update_raw (base : S.Stack→List Bool) (reader : List Bool) (words : Record)
    (raw buffer out valid next : List Bool) :
    Function.update (data base reader words raw buffer out valid) (aux .reversed) next=
      data base reader words next buffer out valid := by funext k;rcases k with k|k|k <;> first | rfl | cases k <;> rfl
/-- Every framed byte is physically materialized before reversal. -/
theorem update_buffer (base : S.Stack→List Bool) (reader : List Bool) (words : Record)
    (raw buffer out valid next : List Bool) :
    Function.update (data base reader words raw buffer out valid) (aux .frameBuffer) next=
      data base reader words raw next out valid := by funext k;rcases k with k|k|k <;> first | rfl | cases k <;> rfl
/-- Final output has its own actually written destination. -/
theorem update_output (base : S.Stack→List Bool) (reader : List Bool) (words : Record)
    (raw buffer out valid next : List Bool) :
    Function.update (data base reader words raw buffer out valid) (aux .output) next=
      data base reader words raw buffer next valid := by funext k;rcases k with k|k|k <;> first | rfl | cases k <;> rfl
end RiemannGaussian.SemiprimeD1StackFactorScopePairView
