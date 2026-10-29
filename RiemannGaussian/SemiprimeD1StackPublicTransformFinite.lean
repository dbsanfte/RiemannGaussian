/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicTransformFiniteWords
import RiemannGaussian.SemiprimeD1StackPublicScaleFinite
/-! # Original first/second transform local-slot order -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackPublicTransformFinite
open SemiprimeD1StackPublicTransformMetadata SemiprimeD1StackPublicTransformFiniteWords
open SemiprimeBitArithmetic SemiprimeMacroParameters SemiprimeMacroGraph SemiprimeMacroEntryBitCheck
/-- Original public stage sizes equal the actual acquired marker counts. -/
theorem size_original (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits) (second : Bool) :
    size bits second=if second then (SemiprimePublicFactorCount.publicConfig (bitValue bits) hN).r
      else (SemiprimePublicFactorCount.publicConfig (bitValue bits) hN).t := by
  unfold size
  rw [SemiprimeD1BinaryDigitAcquisitionBounds.canonical_width bits hc]
  rfl
/-- Original acquired first-stage size. -/
theorem first_size (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits) :
    size bits false=secondAxis (bitLength (bitValue bits)) := size_original bits hc hN false
/-- Original physical word width. -/
theorem public_width (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits) :
    (cached bits).length=firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))+1 := by
  exact SemiprimeD1StackPublicScaleFinite.public_width bits hc hN
/-- Original first-stage assignment cast changes no physical byte. -/
def firstInput (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (tr : Transform) (j : Fin (firstAxis (bitLength (bitValue bits))))
    (input : Fin (arity (Vertex.first (t:=secondAxis (bitLength (bitValue bits))) (digits:=digitCount (bitLength (bitValue bits))) tr j))→Bool) :
    Fin (size bits false*(cached bits).length+size bits false*(cached bits).length)→Bool := fun b=>input ⟨b.val,by
      have hw:=public_width bits hc hN
      have hn:=first_size bits hc hN
      change b.val<(_+_)
      have hb:=b.isLt
      have he : size bits false*(cached bits).length+size bits false*(cached bits).length=
          secondAxis (bitLength (bitValue bits))*(firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))+1)+
          secondAxis (bitLength (bitValue bits))*(firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))+1) := by rw [hw,hn]
      exact Nat.lt_of_lt_of_eq hb he⟩
/-- The finite cast preserves the whole literal assignment stream. -/
theorem first_raw (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (tr : Transform) (j : Fin (firstAxis (bitLength (bitValue bits))))
    (input : Fin (arity (Vertex.first (t:=secondAxis (bitLength (bitValue bits))) (digits:=digitCount (bitLength (bitValue bits))) tr j))→Bool) :
    List.ofFn (firstInput bits hc hN tr j input)=List.ofFn input := by
  apply List.ext_getElem
  · rw [List.length_ofFn,List.length_ofFn]
    have hw:=public_width bits hc hN
    have hn:=first_size bits hc hN
    change _=secondAxis _*(_+1)+secondAxis _*(_+1)
    rw [hw,hn]
  · intro b hb hb';simp only [List.getElem_ofFn,firstInput]
/-- Both first-stage words agree with the actual original local-slot equivalence,
including all parallel word/bit coordinates and high zeros. -/
theorem first_words (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (tr : Transform) (j : Fin (firstAxis (bitLength (bitValue bits))))
    (input : Fin (arity (Vertex.first (t:=secondAxis (bitLength (bitValue bits))) (digits:=digitCount (bitLength (bitValue bits))) tr j))→Bool)
    (k : Fin (size bits false)) :
    halfWord (cached bits) (size bits false) (firstInput bits hc hN tr j input) false k=
      localWord (fun b=>input (localSlotFinEquiv (.first tr j) (.inl (⟨k.val,by
        exact Nat.lt_of_lt_of_eq k.isLt (first_size bits hc hN)⟩,b)))) ∧
    halfWord (cached bits) (size bits false) (firstInput bits hc hN tr j input) true k=
      localWord (fun b=>input (localSlotFinEquiv (.first tr j) (.inr (⟨k.val,by
        exact Nat.lt_of_lt_of_eq k.isLt (first_size bits hc hN)⟩,b)))) := by
  have hw:=public_width bits hc hN
  have hn:=first_size bits hc hN
  constructor
  · apply List.ext_getElem
    · simpa only [halfWord,localWord,SemiprimeMacroEntryBitPrimitives.portBits,List.length_ofFn] using hw
    · intro b hb hb'
      simp only [halfWord,localWord,SemiprimeMacroEntryBitPrimitives.portBits,List.getElem_ofFn,firstInput,Bool.false_eq_true,ite_false,Nat.zero_add]
      congr 1
      apply Fin.ext
      change k.val*(cached bits).length+b=b+(firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))+1)*k.val
      rw [hw,Nat.mul_comm k.val]
      omega
  · apply List.ext_getElem
    · simpa only [halfWord,localWord,SemiprimeMacroEntryBitPrimitives.portBits,List.length_ofFn] using hw
    · intro b hb hb'
      simp only [halfWord,localWord,SemiprimeMacroEntryBitPrimitives.portBits,List.getElem_ofFn,firstInput,ite_true]
      congr 1
      apply Fin.ext
      change size bits false*(cached bits).length+k.val*(cached bits).length+b=
        secondAxis (bitLength (bitValue bits))*(firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))+1)+(b+(firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))+1)*k.val)
      have hs:=congrArg₂ (fun x y : ℕ=>x*y) hn hw
      have hk:=congrArg (fun x : ℕ=>k.val*x) hw
      have hcomm:=Nat.mul_comm k.val (firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))+1)
      omega
/-- Original acquired second-stage size. -/
theorem second_size (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits) :
    size bits true=firstAxis (bitLength (bitValue bits)) := size_original bits hc hN true
/-- Original second-stage assignment cast changes no physical byte. -/
def secondInput (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (tr : Transform) (j : Fin (secondAxis (bitLength (bitValue bits))))
    (input : Fin (arity (Vertex.second (r:=firstAxis (bitLength (bitValue bits))) (digits:=digitCount (bitLength (bitValue bits))) tr j))→Bool) :
    Fin (size bits true*(cached bits).length+size bits true*(cached bits).length)→Bool := fun b=>input ⟨b.val,by
      have hw:=public_width bits hc hN
      have hn:=second_size bits hc hN
      change b.val<(_+_)
      have hb:=b.isLt
      have he : size bits true*(cached bits).length+size bits true*(cached bits).length=
          firstAxis (bitLength (bitValue bits))*(firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))+1)+
          firstAxis (bitLength (bitValue bits))*(firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))+1) := by rw [hw,hn]
      exact Nat.lt_of_lt_of_eq hb he⟩
/-- The finite cast preserves the whole literal assignment stream. -/
theorem second_raw (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (tr : Transform) (j : Fin (secondAxis (bitLength (bitValue bits))))
    (input : Fin (arity (Vertex.second (r:=firstAxis (bitLength (bitValue bits))) (digits:=digitCount (bitLength (bitValue bits))) tr j))→Bool) :
    List.ofFn (secondInput bits hc hN tr j input)=List.ofFn input := by
  apply List.ext_getElem
  · rw [List.length_ofFn,List.length_ofFn]
    have hw:=public_width bits hc hN
    have hn:=second_size bits hc hN
    change _=firstAxis _*(_+1)+firstAxis _*(_+1)
    rw [hw,hn]
  · intro b hb hb';simp only [List.getElem_ofFn,secondInput]
/-- Both second-stage words agree with the actual original local-slot equivalence,
including all parallel word/bit coordinates and high zeros. -/
theorem second_words (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (tr : Transform) (j : Fin (secondAxis (bitLength (bitValue bits))))
    (input : Fin (arity (Vertex.second (r:=firstAxis (bitLength (bitValue bits))) (digits:=digitCount (bitLength (bitValue bits))) tr j))→Bool)
    (k : Fin (size bits true)) :
    halfWord (cached bits) (size bits true) (secondInput bits hc hN tr j input) false k=
      localWord (fun b=>input (localSlotFinEquiv (.second tr j) (.inl (⟨k.val,by
        exact Nat.lt_of_lt_of_eq k.isLt (second_size bits hc hN)⟩,b)))) ∧
    halfWord (cached bits) (size bits true) (secondInput bits hc hN tr j input) true k=
      localWord (fun b=>input (localSlotFinEquiv (.second tr j) (.inr (⟨k.val,by
        exact Nat.lt_of_lt_of_eq k.isLt (second_size bits hc hN)⟩,b)))) := by
  have hw:=public_width bits hc hN
  have hn:=second_size bits hc hN
  constructor
  · apply List.ext_getElem
    · simpa only [halfWord,localWord,SemiprimeMacroEntryBitPrimitives.portBits,List.length_ofFn] using hw
    · intro b hb hb'
      simp only [halfWord,localWord,SemiprimeMacroEntryBitPrimitives.portBits,List.getElem_ofFn,secondInput,Bool.false_eq_true,ite_false,Nat.zero_add]
      congr 1
      apply Fin.ext
      change k.val*(cached bits).length+b=b+(firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))+1)*k.val
      rw [hw,Nat.mul_comm k.val]
      omega
  · apply List.ext_getElem
    · simpa only [halfWord,localWord,SemiprimeMacroEntryBitPrimitives.portBits,List.length_ofFn] using hw
    · intro b hb hb'
      simp only [halfWord,localWord,SemiprimeMacroEntryBitPrimitives.portBits,List.getElem_ofFn,secondInput,ite_true]
      congr 1
      apply Fin.ext
      change size bits true*(cached bits).length+k.val*(cached bits).length+b=
        firstAxis (bitLength (bitValue bits))*(firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))+1)+(b+(firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))+1)*k.val)
      have hs:=congrArg₂ (fun x y : ℕ=>x*y) hn hw
      have hk:=congrArg (fun x : ℕ=>k.val*x) hw
      have hcomm:=Nat.mul_comm k.val (firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))+1)
      omega
end RiemannGaussian.SemiprimeD1StackPublicTransformFinite
