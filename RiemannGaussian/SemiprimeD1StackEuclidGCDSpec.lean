/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackEuclidGCD
import RiemannGaussian.SemiprimeD1StackSourceEnvironmentEncoding
/-! # Meaning of the actual byte-fuel Euclid loop
The recursive interpretation and natural fuel below are proof objects only.
The fixed source obtains every fuel marker by scanning its retained inputs.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackEuclidGCDSpec
open SemiprimeBitArithmetic (bitValue)
open SemiprimeSourceCompactBits (Compact)
open SemiprimeD1StackSourceEnvironmentEncoding (normalize normalize_value normalize_compact normalize_length)
/-- Proof interpretation of the actual public output and actual fuel-abort branch. -/
structure Outcome where
  /-- Compact actual result word. -/
  word:List Bool
  /-- True means the physical fuel-empty branch would be taken. -/
  exhausted:Bool
/-- Interpretation of literal positive divisions, physical Euclid swaps and trimming. -/
def iterate :Nat→List Bool→List Bool→Outcome
  | 0,x,_=>⟨normalize x,true⟩
  | n+1,x,y=>if y=[] then ⟨normalize x,false⟩ else
      iterate n y (normalize (SemiprimeBitDivision.divideLoop x y).remainder)
/-- Exactly two physically pushed markers per original input byte and one literal terminal marker. -/
def fuelLength (left right:List Bool) :Nat:=2*(left.length+right.length)+1
/-- Source output interpretation from the two actual original words. -/
def answer (left right:List Bool) :Outcome:=iterate (fuelLength left right) left (normalize right)
/-- Compact numeric zero is physically empty, including after an all-zero padded input. -/
theorem compact_zero (word:List Bool) (hc:Compact word) :bitValue word=0 ↔ word=[] :=by
  constructor
  · intro h
    exact SemiprimeSourceCompactWordIds.compact_value_injective word [] hc trivial h
  · intro h;rw [h];rfl
/-- A nonempty trimmed actual divisor is a genuinely positive numeric divisor. -/
theorem compact_positive (word:List Bool) (hc:Compact word) (hne:word≠[]) :0<bitValue word:=by
  have hz:bitValue word≠0:=fun h=>hne ((compact_zero word hc).mp h)
  omega
/-- Every returned interpretation is compact even for insufficient proof-side fuel. -/
theorem iterate_compact (n:Nat) (x y:List Bool) :Compact (iterate n x y).word:=by
  induction n generalizing x y with
  | zero=>exact normalize_compact x
  | succ n ih=>
    simp only [iterate]
    split
    · exact normalize_compact x
    · exact ih _ _
/-- Numeric words and exhaustion agree with the legacy finite-fuel Euclid semantics.
This is only a value/termination proof, never a transport of its report clock. -/
theorem legacy_correspond (n:Nat) (x y rawX rawY:List Bool) (hc:Compact y)
    (hx:bitValue x=bitValue rawX) (hy:bitValue y=bitValue rawY) :
    bitValue (iterate n x y).word=bitValue (SemiprimeBitGcd.gcdLoop rawX rawY (List.replicate n ())).bits ∧
    (iterate n x y).exhausted=(SemiprimeBitGcd.gcdLoop rawX rawY (List.replicate n ())).exhausted :=by
  induction n generalizing x y rawX rawY with
  | zero=>exact ⟨(normalize_value x).trans hx,rfl⟩
  | succ n ih=>
    by_cases hz:y=[]
    · have hv:bitValue rawY=0:=by rw [←hy,hz];rfl
      have hb:¬(SemiprimeBitDivision.nonzeroBits rawY).nonzero=true:=by
        intro h;have hp:=(SemiprimeBitDivision.nonzeroBits_correct rawY).mp h;omega
      simp only [iterate,hz,ite_true,List.replicate_succ,SemiprimeBitGcd.gcdLoop,ite_eq_right hb]
      exact ⟨(normalize_value x).trans hx,trivial⟩
    · have hp:=compact_positive y hc hz
      have hb:(SemiprimeBitDivision.nonzeroBits rawY).nonzero=true:=
        (SemiprimeBitDivision.nonzeroBits_correct rawY).mpr (by omega)
      have hr:bitValue (normalize (SemiprimeBitDivision.divideLoop x y).remainder)=
          bitValue (SemiprimeBitDivision.divideBits rawX rawY).remainder:=by
        rw [normalize_value,(SemiprimeD1StackDividerExecution.output_values x y hp).2,
          (SemiprimeBitDivision.divideBits_correct rawX rawY).2,hx,hy]
      simpa only [iterate,ite_eq_right hz,List.replicate_succ,SemiprimeBitGcd.gcdLoop,ite_eq_left hb] using
        ih y (normalize (SemiprimeBitDivision.divideLoop x y).remainder) rawY
          (SemiprimeBitDivision.divideBits rawX rawY).remainder (normalize_compact _) hy hr
/-- The physically acquired byte fuel suffices for every original binary word, including padded zero. -/
theorem answer_stopped (left right:List Bool) :(answer left right).exhausted=false:=by
  have h:=legacy_correspond (fuelLength left right) left (normalize right) left right
    (normalize_compact right) rfl (normalize_value right)
  have hs:=(SemiprimeBitGcd.gcdLoop_stops_pow right.length left right
    (List.replicate (fuelLength left right) ()) (SemiprimeBitArithmetic.bitValue_lt_width right)
    (by simp only [List.length_replicate,fuelLength];omega)).1
  exact h.2.trans hs
/-- The actual source's compact output represents the exact mathematical GCD. -/
theorem answer_value (left right:List Bool) :
    bitValue (answer left right).word=(bitValue left).gcd (bitValue right):=by
  have h:=legacy_correspond (fuelLength left right) left (normalize right) left right
    (normalize_compact right) rfl (normalize_value right)
  have hs:(SemiprimeBitGcd.gcdLoop left right (List.replicate (fuelLength left right) ())).exhausted=false:=
    h.2.symm.trans (answer_stopped left right)
  exact h.1.trans (SemiprimeBitGcd.gcdLoop_correct_of_stopped _ _ _ hs)
/-- Required byte ABI: exact compact normalization of the legacy GCD result, without its arbitrary input padding. -/
theorem answer_legacy_bits (left right:List Bool) :
    (answer left right).word=normalize (SemiprimeBitGcd.gcdBits left right).bits:=by
  apply SemiprimeSourceCompactWordIds.compact_value_injective _ _ (iterate_compact _ _ _) (normalize_compact _)
  change bitValue (answer left right).word=_
  rw [answer_value,normalize_value,(SemiprimeBitGcd.gcdBits_correct left right).1]
end RiemannGaussian.SemiprimeD1StackEuclidGCDSpec
