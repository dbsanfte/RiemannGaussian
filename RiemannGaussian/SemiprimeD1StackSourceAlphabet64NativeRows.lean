/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceAlphabet64Arithmetic
/-! # Literal compact-colour row ABI agrees with the frozen original head-major native rows -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceAlphabet64NativeRows
open SemiprimeD1StackSourceAlphabet64Encoding SemiprimeD1StackSourceAlphabet64Arithmetic
open SemiprimeSourceHistogramKeyBits (frame)
open SemiprimeBitArithmetic (bitValue)
namespace Old
export SemiprimeSourceWordBankRows (colours prepend rowsWith rows prepend_value)
export SemiprimeSourceHistogramRows (layout)
export SemiprimeSourceHistogramHeadRefinement (numberKey numberKey_value numberKey_compact)
end Old
/-- Head-major complete actual row layouts from a finite compact-colour list; proof specification only. -/
def layouts (keys:List (List Bool)) :Nat→List (List Bool)
  | 0=>[[]]
  | a+1=>keys.flatMap (fun key=>(layouts keys a).map (frame key))
/-- Every original physical row constructor has exactly the declared compact-colour ABI. -/
theorem rowsWith_layouts (cs:List SemiprimeRationalBits.RationalWord) (a:Nat) :
    (Old.rowsWith cs a).value.map Old.layout=
      layouts (cs.map (fun c=>compact c.numerator.magnitude)) a :=by
  induction a with
  | zero=>rfl
  | succ a ih=>
    simp only [Old.rowsWith,SemiprimeMaterializedSourceUniversal.collect_value,
      SemiprimePaidFiniteEnumerationLists.product_value,List.map_map]
    change (cs.product (Old.rowsWith cs a).value).map (fun p=>Old.layout (Old.prepend p.1 p.2).value)=_
    simp only [List.product,List.map_flatMap,List.map_map,layouts,List.flatMap_map]
    congr 1
    funext c
    rw [←ih,List.map_map]
    apply List.map_congr_left
    intro tail _
    change Old.layout (Old.prepend c tail).value=frame (compact c.numerator.magnitude) (Old.layout tail)
    rw [Old.prepend_value]
    rfl
/-- Every original paid colour normalizes to the SAME canonical field word used by this source. -/
theorem colour_keys :
    (Old.colours 64).value.map (fun c=>compact c.numerator.magnitude)=
      (List.finRange 64).map (fun c=>Old.numberKey c.val) :=by
  simp only [Old.colours,SemiprimeMaterializedSourceUniversal.collect_value,
    SemiprimePaidFiniteEnumerationLists.fin_value,List.map_map]
  apply List.map_congr_left
  intro c _
  rfl
/-- Exact old head-major row layout list, with padding physically removed in both codecs. -/
theorem rows_layouts (a:Nat) :
    (Old.rows 64 a).value.map Old.layout=
      layouts ((List.finRange 64).map (fun c=>Old.numberKey c.val)) a :=by
  change (Old.rowsWith (Old.colours 64).value a).value.map Old.layout=_
  rw [rowsWith_layouts,colour_keys]
/-- Pure tuple enumeration and actual compact-field layout share literal order. -/
theorem layouts_digits (a:Nat) :
    layouts ((List.finRange 64).map (fun c=>Old.numberKey c.val)) a=
      (digits a).map (fun cs=>fields (cs.map (fun c=>Old.numberKey c.val))) :=by
  induction a with
  | zero=>rfl
  | succ a ih=>
    simp only [layouts,List.flatMap_map,ih,List.map_map,digits,List.map_flatMap]
    congr 1
/-- Actual parsed compact colours of every packed original tuple are byte-identical to the frozen native row ABI. -/
theorem row_pack (a:Nat) (cs:List (Fin 64)) (hc:cs∈digits a) :
    row a (pack cs)=fields (cs.map (fun c=>Old.numberKey c.val)) :=by
  have hlen:=digits_width a cs hc
  rw [←hlen,row,colours_pack]
  congr 1
  apply List.map_congr_left
  intro c _
  exact digit_compact c
/-- Canonical word lists with identical numeric values have no padding/zero ambiguity. -/
theorem compact_lists_eq (xs ys:List (List Bool))
    (hx:∀x∈xs,SemiprimeSourceCompactBits.Compact x)
    (hy:∀y∈ys,SemiprimeSourceCompactBits.Compact y) (hv:xs.map bitValue=ys.map bitValue) :xs=ys :=by
  induction xs generalizing ys with
  | nil=>cases ys with | nil=>rfl | cons y ys=>cases hv
  | cons x xs ih=>
    cases ys with
    | nil=>cases hv
    | cons y ys=>
      have hh:=List.cons.inj hv
      have hxy:x=y:=SemiprimeSourceCompactWordIds.compact_value_injective x y
        (hx x List.mem_cons_self) (hy y List.mem_cons_self) hh.1
      have ht:=ih ys (fun z hz=>hx z (List.mem_cons_of_mem _ hz))
        (fun z hz=>hy z (List.mem_cons_of_mem _ hz)) hh.2
      rw [hxy,ht]
/-- Actual trimmed counter IDs equal the frozen compact bank IDs literally, including sole compact zero[]. -/
theorem ids_actual (a:Nat) :
    (words a).map compact=(SemiprimeSourceCompactWordBank.acquire 64 a).ids :=by
  apply compact_lists_eq
  · intro x hx
    obtain ⟨w,_,rfl⟩:=List.mem_map.mp hx
    exact SemiprimeSourceCompactBits.trim_compact _
  · exact SemiprimeSourceCompactWordBank.ids_compact 64 a
  · rw [SemiprimeSourceCompactWordBank.ids_values,List.map_map]
    change (words a).map (fun w=>bitValue (compact w))=_
    simp only [compact,SemiprimeSourceCompactBits.trim_value]
    exact words_values a
/-- Zipping two actual original-order traversals pairs corresponding physical fields exactly. -/
theorem zip_maps {α β γ:Type} (xs:List α) (f:α→β) (g:α→γ) :
    (xs.map f).zip (xs.map g)=xs.map (fun x=>(f x,g x)) :=by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>simp only [List.map_cons,List.zip_cons_cons,ih]
/-- ENTIRE actual compact-ID/full-colour-row catalogue matches the frozen native rows
with the exact original candidate order, not only a numeric permutation. -/
theorem entries_original (a:Nat) :
    entries a=(SemiprimeSourceCompactWordBank.acquire 64 a).ids.zip
      ((Old.rows 64 a).value.map Old.layout) :=by
  rw [←ids_actual,rows_layouts,layouts_digits]
  simp only [entries,←packed_words,List.map_map]
  rw [zip_maps]
  apply List.map_congr_left
  intro cs hc
  change (compact (pack cs),row a (pack cs))=(compact (pack cs),fields (cs.map (fun c=>Old.numberKey c.val)))
  rw [row_pack a cs hc]
end RiemannGaussian.SemiprimeD1StackSourceAlphabet64NativeRows
