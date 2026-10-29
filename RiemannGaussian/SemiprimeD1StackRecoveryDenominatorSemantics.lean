/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryDenominatorExecution
import RiemannGaussian.SemiprimeD1RecoveryIntegerBits
import RiemannGaussian.SemiprimeD1StackWordFitBounds
import RiemannGaussian.SemiprimeD1StackAssignmentOrder
/-! # Exact old common-denominator bytes on the original bounded domain
The source is a streaming left product with one physical final fit. The old
right-recursive clipped product has the same integer value under the original
width caps, and both nonempty outputs have the same exact physical width.
No native clock, numerator acquisition or child read is transported.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryDenominatorSemantics
open SemiprimeD1StackRecoveryDenominatorEncoding SemiprimeBitArithmetic
namespace X
export SemiprimeD1StackRecoveryDenominatorExecution (result output_result done source_run)
end X
namespace I
export SemiprimeD1RecoveryIntegerBits (Entry native denominator product product_length denominator_correct native_denominator_bound)
end I
/-- Proof-only entry projection; only its actual denominator field affects this stage. -/
def entries (rs:List Row):List I.Entry:=rs.map fun r=>⟨⟨(r 2).head?.getD false,r 3⟩,r 4,[]⟩
/-- The old mathematical integer denominator is exactly its original actual denominator product. -/
theorem native_product (es:List I.Entry):
    (SemiprimeD1RecoveryCanonicalRun.denominator (I.native es)).value=(es.map (fun e=>bitValue e.denominator)).prod:=by
  induction es with
  | nil=>rfl
  | cons e es ih=>
    simp only [I.native,List.map_cons,SemiprimeD1RecoveryCanonicalRun.denominator,List.prod_cons] at ⊢ ih
    rw [ih]
/-- Actual raw streaming accumulator represents the same full integer denominator product. -/
theorem raw_native (rs:List Row):
    bitValue (raw rs [true])=(SemiprimeD1RecoveryCanonicalRun.denominator (I.native (entries rs))).value:=by
  rw [raw_value,native_product]
  simp only [entries,List.map_map,Function.comp_def,show bitValue [true]=1 from rfl,Nat.mul_one]
/-- The original nonempty clipped recursive denominator occupies exactly the paid physical template width. -/
theorem old_length (r:Row) (rs:List Row) (widthTemplate:List Bool):
    (I.denominator widthTemplate (entries (r::rs))).bits.length=widthTemplate.length:=
  I.product_length _ _ _
/-- The actual full-product word fits from original per-row canonical height and actual template width. -/
theorem raw_fits (rs:List Row) (widthTemplate:List Bool) (A:Nat)
    (hd:∀r∈rs,bitValue (r 4) ≤2^A) (hw:A*rs.length+1 ≤widthTemplate.length):
    bitValue (raw rs [true]) < 2^widthTemplate.length:=by
  have h:∀e∈entries rs,bitValue e.denominator ≤2^A:=by
    intro e he
    obtain ⟨r,hr,rfl⟩:=List.mem_map.mp he
    exact hd r hr
  have hb:=I.native_denominator_bound (entries rs) A h
  rw [←raw_native] at hb
  simp only [entries,List.length_map] at hb
  exact hb.trans_lt (Nat.pow_lt_pow_right (by decide:1 <2) (by omega))
/-- Empty source rows return the original literal one even for an empty template. -/
theorem result_nil (widthTemplate:List Bool):X.result [] widthTemplate=(I.denominator widthTemplate []).bits:=rfl
/-- Exact old W-padded denominator bytes under the derived original fit domain. -/
theorem result_old (rs:List Row) (widthTemplate:List Bool) (A:Nat)
    (hd:∀r∈rs,bitValue (r 4) ≤2^A) (hw:A*rs.length+1 ≤widthTemplate.length):
    X.result rs widthTemplate=(I.denominator widthTemplate (entries rs)).bits:=by
  cases rs with
  | nil=>rfl
  | cons r rs=>
    have hfit:=raw_fits (r::rs) widthTemplate A hd hw
    have ho:∀e∈entries (r::rs),bitValue e.denominator ≤2^A:=by
      intro e he
      obtain ⟨r,hr,rfl⟩:=List.mem_map.mp he
      exact hd r hr
    have hold:=I.denominator_correct widthTemplate (entries (r::rs)) A ho (by simpa only [entries,List.length_map] using hw)
    apply SemiprimeD1StackAssignmentOrder.word_value_injective
    · exact (SemiprimeD1StackWordFitExecution.result_length _ _).trans (old_length r rs widthTemplate).symm
    · change bitValue (SemiprimeD1StackWordFitExecution.result (raw (r::rs) [true]) widthTemplate)=_
      rw [SemiprimeD1StackWordFitBounds.result_value _ _ hfit,raw_native,hold]
/-- Literal old denominator bytes depend only on actual denominator fields, never children or numerator signs. -/
def oldWords (widthTemplate:List Bool):List (List Bool) → List Bool
  | []=>[true]
  | d::ds=>(I.product widthTemplate d (oldWords widthTemplate ds)).bits
/-- Exact byte projection of the old source onto actual denominator words. -/
theorem denominator_words (widthTemplate:List Bool) (es:List I.Entry):
    (I.denominator widthTemplate es).bits=oldWords widthTemplate (es.map (fun e=>e.denominator)):=by
  induction es with
  | nil=>rfl
  | cons e es ih=>simp only [I.denominator,List.map_cons,oldWords,ih]
end RiemannGaussian.SemiprimeD1StackRecoveryDenominatorSemantics
