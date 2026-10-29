/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1VertexCatalogueModes
import RiemannGaussian.SemiprimeD1StackCartesian4Bounds
import RiemannGaussian.SemiprimeD1StackGraphIndicesBounds

/-! # Original vertex descriptor specification
These encodings specify the actual bytes to be emitted by the static physical
mode controller. No typed vertex or native Cartesian list is a machine input.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1VertexCatalogueEncoding
open SemiprimeD1VertexCatalogueModes
open SemiprimeD1StackCartesian4Body (record)
open SemiprimeD1StackCartesian4Execution
open SemiprimeMacroGraph

/-- Original three-transform constructor code in its exact original sum order. -/
def transformCode : Transform→ℕ
  | .inl side => side.val
  | .inr _ => 2
/-- Mathematical representation of one actual tagged four-coordinate record. -/
def encode (mode:Mode) (i0 i1 i2 i3:ℕ) (tail:List Bool) : List Bool :=
  record (List.replicate (code mode) true)
    ![List.replicate i0 true,List.replicate i1 true,List.replicate i2 true,List.replicate i3 true] tail

/-- Actual original arithmetic-vertex constructor/coordinate encoding. -/
def arithmetic {r t digits:ℕ} : Vertex r t digits→List Bool→List Bool
  | .input side i => encode .input side.val i.val 0 0
  | .first tr j => encode .first (transformCode tr) j.val 0 0
  | .scale tr j k => encode .scale (transformCode tr) j.val k.val 0
  | .second tr k => encode .second (transformCode tr) k.val 0 0
  | .product i => encode .product i.val 0 0 0
  | .carryInitial => encode .carryInitial 0 0 0 0
  | .carry i => encode .carry i.val 0 0 0
  | .carryTerminal => encode .carryTerminal 0 0 0 0
  | .orGate side i => encode .orGate side.val i.val 0 0
  | .inputCheck side => encode .inputCheck side.val 0 0 0
/-- Actual original word-signal equality-vertex descriptor, including its word-bit index. -/
def wordEquality {r t:ℕ} : WordSignal r t→Fin (r*t+1)→List Bool→List Bool
  | .input side i,bit => encode .wordInput side.val i.val bit.val 0
  | .first tr j k,bit => encode .wordFirst (transformCode tr) j.val k.val bit.val
  | .twiddle tr j k,bit => encode .wordTwiddle (transformCode tr) j.val k.val bit.val
  | .second tr k j,bit => encode .wordSecond (transformCode tr) k.val j.val bit.val
  | .product i,bit => encode .wordProduct i.val bit.val 0 0
  | .carry i,bit => encode .wordCarry i.val bit.val 0 0
/-- Actual source/OR flag equality-vertex descriptor. -/
def flagEquality {digits:ℕ} : FlagSignal digits→List Bool→List Bool
  | .digit side i => encode .flagDigit side.val i.val 0 0
  | .orOut side i => encode .flagOr side.val i.val 0 0
/-- Full original subdivided-vertex record format; both branches are retained. -/
def vertex {r t digits:ℕ} : SubdividedVertex r t digits→List Bool→List Bool
  | .inl v => arithmetic v
  | .inr (.inl (word,bit)) => wordEquality word bit
  | .inr (.inr flag) => flagEquality flag

/-- Exact output of the actual closed Cartesian engine for a fixed constructor mode. -/
def modeCatalogue (r t digits:ℕ) (mode:Mode) (tail:List Bool) : List Bool :=
  box0 (dims r t digits mode) (fun _=>[]) (List.replicate (code mode) true) tail
/-- All original constructor modes in their literal original order. -/
def catalogue (r t digits:ℕ) (tail:List Bool) : List Bool :=
  order.foldr (fun mode rest=>modeCatalogue r t digits mode rest) tail

/-- The original transform list codes are the literal ascending three-element range. -/
theorem transform_codes : SemiprimeMacroFiniteEnumerations.transforms.values.map transformCode=[0,1,2] := rfl

/-- Exact list-product traversal, including its actual left-before-right ordering. -/
theorem foldr_product {A B C:Type} (xs:List A) (ys:List B) (F:A×B→C→C) (tail:C) :
    (xs.product ys).foldr F tail=xs.foldr (fun x rest=>ys.foldr (fun y acc=>F (x,y) acc) rest) tail := by
  induction xs generalizing tail with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.product,List.flatMap_cons,List.foldr_append,List.foldr_map,List.foldr_cons]
    exact congrArg (fun rest=>ys.foldr (fun y acc=>F (x,y) acc) rest) (ih tail)

/-- The actual finite original index order is exactly the physical scalar range fold. -/
theorem rangeFold_fin (n:ℕ) (F:ℕ→List Bool→List Bool) (tail:List Bool) :
    SemiprimeD1StackCartesian4Loop.rangeFold n F tail=
      (SemiprimeFiniteEnumerations.fin n).values.foldr (fun i rest=>F i.val rest) tail := by
  rw [rangeFold_range,←SemiprimeD1StackGraphIndicesBounds.fin_values]
  simp only [List.foldr_map]

/-- The physical engine reads exactly the four chosen current indices in its emitted record. -/
theorem four_indices (tag output:List Bool) (i0 i1 i2 i3:ℕ) :
    record tag
      (Function.update (Function.update (Function.update (Function.update (fun _:Fin 4=>[])
        0 (List.replicate i0 true)) 1 (List.replicate i1 true)) 2 (List.replicate i2 true)) 3 (List.replicate i3 true)) output=
    record tag ![List.replicate i0 true,List.replicate i1 true,List.replicate i2 true,List.replicate i3 true] output := by
  simp [record,Function.update]
/-- Exact four-index product emitted by the real engine, expressed with original Fin lists. -/
theorem modeCatalogue_fin (r t digits:ℕ) (mode:Mode) (tail:List Bool) :
    modeCatalogue r t digits mode tail=
      (SemiprimeFiniteEnumerations.fin (dims r t digits mode 0)).values.foldr (fun i0 rest=>
      (SemiprimeFiniteEnumerations.fin (dims r t digits mode 1)).values.foldr (fun i1 rest=>
      (SemiprimeFiniteEnumerations.fin (dims r t digits mode 2)).values.foldr (fun i2 rest=>
      (SemiprimeFiniteEnumerations.fin (dims r t digits mode 3)).values.foldr (fun i3 rest=>
        encode mode i0.val i1.val i2.val i3.val rest) rest) rest) rest) tail := by
  unfold modeCatalogue box0 box1 box2 box3
  simp_rw [rangeFold_fin,four_indices]
  rfl

/-- All arithmetic AND equality descriptors are the exact original complete list fold. -/
theorem original_vertices (r t digits:ℕ) (tail:List Bool) :
    catalogue r t digits tail=(SemiprimeMacroFiniteEnumerations.subdividedVertices r t digits).values.foldr vertex tail := by
  have h1:(SemiprimeFiniteEnumerations.fin 1).values=[0]:=rfl
  have h2:(SemiprimeFiniteEnumerations.fin 2).values=[0,1]:=rfl
  have h3:(SemiprimeFiniteEnumerations.fin 3).values=[0,1,2]:=rfl
  have ht:SemiprimeMacroFiniteEnumerations.transforms.values=[Sum.inl 0,Sum.inl 1,Sum.inr ()]:=rfl
  have hu:SemiprimeMacroFiniteEnumerations.unit.values=[()]:=rfl
  simp [catalogue,order,modeCatalogue_fin,dims,roles,dimension,
    SemiprimeMacroFiniteEnumerations.subdividedVertices,SemiprimeMacroFiniteEnumerations.vertices,
    SemiprimeMacroFiniteEnumerations.bits,SemiprimeMacroFiniteEnumerations.words,SemiprimeMacroFiniteEnumerations.flags,
    SemiprimeFiniteEnumerations.sum,SemiprimeFiniteEnumerations.prod,SemiprimeFiniteEnumerations.transport,
    List.foldr_append,List.foldr_map,foldr_product,h1,h2,h3,ht,hu,
    SemiprimeMacroFiniteEnumerations.verticesEquiv,SemiprimeMacroFiniteEnumerations.wordsEquiv,
    SemiprimeMacroFiniteEnumerations.flagsEquiv,vertex,arithmetic,wordEquality,flagEquality,transformCode]
end RiemannGaussian.SemiprimeD1VertexCatalogueEncoding
