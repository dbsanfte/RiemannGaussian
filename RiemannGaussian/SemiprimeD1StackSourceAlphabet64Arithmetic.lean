/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceAlphabet64Bounds
import RiemannGaussian.SemiprimeSourceHistogramHeadRefinement
/-! # Proof-only exact head-major radix64 packing of the actual fixed-width counter -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceAlphabet64Arithmetic
open SemiprimeD1StackSourceAlphabet64Encoding SemiprimeD1StackSourceAlphabet64Bounds
open SemiprimeBitArithmetic (bitValue bitNat)
namespace A
export SemiprimeD1StackAssignmentOrder (assignments assignments_values assignments_width word_value_injective zero_remaining)
end A
/-- General numeric concatenation identity for actual little-endian Boolean words. -/
theorem value_append (xs ys:List Bool) :bitValue (xs++ys)=bitValue xs+2^xs.length*bitValue ys :=by
  induction xs with
  | nil=>simp only [List.nil_append,bitValue,List.length_nil,pow_zero,Nat.one_mul,Nat.zero_add]
  | cons b xs ih=>simp only [List.cons_append,bitValue,ih,List.length_cons,pow_succ];ring
/-- Fixed-width all-false words represent zero, including empty width. -/
theorem zero_value (n:Nat) :bitValue (List.replicate n false)=0 :=by
  induction n with
  | zero=>rfl
  | succ n ih=>simp only [List.replicate_succ,bitValue,bitNat,Bool.false_eq_true,ite_false,ih,Nat.mul_zero,Nat.add_zero]
/-- Literal complete six-bit counter bank used only to identify each bounded colour in proofs. -/
def digit (c:Fin 64) :List Bool :=((A.assignments 64 (List.replicate 6 false))[c.val]?).getD []
/-- Each original finite colour has one exact six-bit physical representation. -/
theorem digit_length (c:Fin 64) :(digit c).length=6 :=by
  have hc:c.val<(A.assignments 64 (List.replicate 6 false)).length:=by
    rw [SemiprimeD1StackAssignmentOrder.assignments_length];exact c.isLt
  rw [digit,List.getElem?_eq_getElem hc,Option.getD_some]
  exact (A.assignments_width _ _ _ (List.getElem_mem hc)).trans List.length_replicate
/-- Counter order identifies exactly the native finite colour ordinal. -/
theorem digit_value (c:Fin 64) :bitValue (digit c)=c.val :=by
  have hv:=A.assignments_values 64 (List.replicate 6 false) (by rw [A.zero_remaining];decide)
  rw [zero_value,←List.range_eq_range'] at hv
  have hc:c.val<(A.assignments 64 (List.replicate 6 false)).length:=by
    rw [SemiprimeD1StackAssignmentOrder.assignments_length];exact c.isLt
  have h:=congrArg (fun xs:List Nat=>(xs[c.val]?).getD 0) hv
  simpa only [digit,List.getElem?_map,List.getElem?_eq_getElem hc,List.getElem?_range c.isLt,
    Option.map_some,Option.getD_some] using h
/-- Exact old canonical colour ABI, including the EMPTY colour-zero representation. -/
theorem digit_compact (c:Fin 64) :compact (digit c)=SemiprimeSourceHistogramHeadRefinement.numberKey c.val :=by
  apply SemiprimeSourceCompactWordIds.compact_value_injective _ _
    (SemiprimeSourceCompactBits.trim_compact _) (SemiprimeSourceHistogramHeadRefinement.numberKey_compact _)
  rw [SemiprimeSourceCompactBits.trim_value,digit_value,SemiprimeSourceHistogramHeadRefinement.numberKey_value]
/-- Pure head-major finite coordinate enumeration; this is never a runtime operand. -/
def digits :Nat→List (List (Fin 64))
  | 0=>[[]]
  | a+1=>(List.finRange 64).flatMap (fun c=>(digits a).map (c::.))
/-- Original physical little-endian packed counter layout: the last coordinate contributes low bits. -/
def pack :List (Fin 64)→List Bool
  | []=>[]
  | c::cs=>pack cs++digit c
/-- Proof-side head-major ordinal of one original colour tuple. -/
def rank :List (Fin 64)→Nat
  | []=>0
  | c::cs=>c.val*64^cs.length+rank cs
/-- Every proof tuple retains its exact coordinate count. -/
theorem digits_width (a:Nat) (cs:List (Fin 64)) (hc:cs∈digits a) :cs.length=a :=by
  induction a generalizing cs with
  | zero=>have he:cs=[]:=List.mem_singleton.mp hc;subst cs;rfl
  | succ a ih=>
    obtain ⟨c,hcMember,hmapped⟩:=List.mem_flatMap.mp hc
    obtain ⟨rest,hrest,he⟩:=List.mem_map.mp hmapped
    subst cs
    exact congrArg Nat.succ (ih rest hrest)
/-- Literal packed width is six actual bits per original coordinate. -/
theorem pack_length (cs:List (Fin 64)) :(pack cs).length=6*cs.length :=by
  induction cs with
  | nil=>rfl
  | cons c cs ih=>simp only [pack,List.length_append,ih,digit_length,List.length_cons];omega
/-- Packed counter value is its exact head-major finite tuple ordinal. -/
theorem pack_value (cs:List (Fin 64)) :bitValue (pack cs)=rank cs :=by
  induction cs with
  | nil=>rfl
  | cons c cs ih=>
    rw [pack,value_append,pack_length,cardinality,ih,digit_value]
    change _=c.val*64^cs.length+rank cs
    ring
/-- Finite ordinal values retain their exact original order. -/
theorem fin_values (n:Nat) :(List.finRange n).map Fin.val=List.range n :=by
  induction n with
  | zero=>rfl
  | succ n ih=>simp only [List.finRange_succ,List.map_cons,List.map_map,Fin.val_zero,Fin.val_succ,
      List.range_succ_eq_map,←ih,List.map_map,Function.comp_def,Nat.succ_eq_add_one]
/-- Head-major rectangle traversal is the contiguous original mixed-radix ordinal range. -/
theorem rectangle_values (heads tails:Nat) :
    (List.range heads).flatMap (fun h=>(List.range tails).map (fun t=>h*tails+t))=List.range (heads*tails) :=by
  induction heads with
  | zero=>simp only [List.range_zero,List.flatMap_nil,Nat.zero_mul]
  | succ heads ih=>
    rw [List.range_succ,List.flatMap_append,List.flatMap_singleton,ih,Nat.succ_mul,List.range_add]
/-- The original head-major tuple ranks enumerate EVERY counter ordinal in exactly ascending order. -/
theorem ranks_values (a:Nat) :(digits a).map rank=List.range (64^a) :=by
  induction a with
  | zero=>rfl
  | succ a ih=>
    simp only [digits,List.map_flatMap,List.map_map]
    have he:∀c:Fin 64,(digits a).map (fun cs=>rank (c::cs))=
        (List.range (64^a)).map (fun t=>c.val*64^a+t):=by
      intro c
      calc
        _=(digits a).map (fun cs=>c.val*64^a+rank cs):=by
          apply List.map_congr_left
          intro cs hc
          simp only [rank,digits_width a cs hc]
        _=((digits a).map rank).map (fun t=>c.val*64^a+t):=by rw [List.map_map];rfl
        _= _:=by rw [ih]
    change (List.finRange 64).flatMap (fun c=>(digits a).map (fun cs=>rank (c::cs)))=_
    simp_rw [he]
    rw [show (List.finRange 64).flatMap (fun c=>(List.range (64^a)).map (fun t=>c.val*64^a+t))=
      ((List.finRange 64).map Fin.val).flatMap (fun c=>(List.range (64^a)).map (fun t=>c*64^a+t)) by rw [List.flatMap_map]]
    rw [fin_values,rectangle_values,pow_succ,Nat.mul_comm]
/-- Physical complete counter values are the same original ascending ordinal range. -/
theorem words_values (a:Nat) :(words a).map bitValue=List.range (64^a) :=by
  rw [words,A.assignments_values _ _ (by rw [A.zero_remaining])]
  rw [zero_value,←List.range_eq_range',cardinality]
/-- Fixed-width lists are determined by their actual numeric sequences, without a permutation premise. -/
theorem fixed_lists_eq (xs ys:List (List Bool)) (width:Nat)
    (hx:∀x∈xs,x.length=width) (hy:∀y∈ys,y.length=width) (hv:xs.map bitValue=ys.map bitValue) :xs=ys :=by
  induction xs generalizing ys with
  | nil=>cases ys with | nil=>rfl | cons y ys=>cases hv
  | cons x xs ih=>
    cases ys with
    | nil=>cases hv
    | cons y ys=>
      have hh:=List.cons.inj hv
      have hxy:x=y:=A.word_value_injective x y
        ((hx x List.mem_cons_self).trans (hy y List.mem_cons_self).symm) hh.1
      have ht:=ih ys (fun z hz=>hx z (List.mem_cons_of_mem _ hz))
        (fun z hz=>hy z (List.mem_cons_of_mem _ hz)) hh.2
      rw [hxy,ht]
/-- The actual counter enumeration is LITERALLY the packed old head-major colour enumeration. -/
theorem packed_words (a:Nat) :(digits a).map pack=words a :=by
  apply fixed_lists_eq _ _ (6*a)
  · intro w hw
    obtain ⟨cs,hc,rfl⟩:=List.mem_map.mp hw
    rw [pack_length,digits_width a cs hc]
  · exact word_width a
  · rw [List.map_map]
    simp only [Function.comp_def,pack_value]
    rw [ranks_values,words_values]
/-- Every real six-bit parsed/normalized colour is exactly the old finite coordinate word. -/
theorem colours_pack (cs:List (Fin 64)) :
    colours cs.length (pack cs).reverse=cs.map (fun c=>compact (digit c)) :=by
  induction cs with
  | nil=>rfl
  | cons c cs ih=>
    have ht:((digit c).reverse++(pack cs).reverse).take 6=(digit c).reverse:=by
      simpa only [List.length_reverse,digit_length] using (List.take_left (l₁:=(digit c).reverse) (l₂:=(pack cs).reverse))
    have hd:((digit c).reverse++(pack cs).reverse).drop 6=(pack cs).reverse:=by
      simpa only [List.length_reverse,digit_length] using (List.drop_left (l₁:=(digit c).reverse) (l₂:=(pack cs).reverse))
    simp only [List.length_cons,pack,List.reverse_append,colours,ht,hd,List.reverse_reverse,List.map_cons,ih]
end RiemannGaussian.SemiprimeD1StackSourceAlphabet64Arithmetic
