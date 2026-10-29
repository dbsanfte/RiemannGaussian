/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeMacroEntryBitPrimitives
import RiemannGaussian.SemiprimeSourceHistogramKeyBits

/-! # Physical public arithmetic expression syntax
Prefix tags 00/01/10/11 denote literal/add/sub/multiply. Literal payloads are
self-delimiting actual bit fields. All repeated subtree and literal cells are
retained in the size; no expression object or integer is put in finite control.
The fixed recursive evaluator will use actual finite-label call/return frames.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackExprCodec
open SemiprimeMacroEntryBitPrimitives (Expr nodes)
open SemiprimeSourceHistogramKeyBits (frame)

/-- Literal prefix byte stream, with an explicit already acquired suffix. -/
def encode : Expr→List Bool→List Bool
  | .literal bits,tail => false::false::frame bits tail
  | .add a b,tail => false::true::encode a (encode b tail)
  | .sub a b,tail => true::false::encode a (encode b tail)
  | .mul a b,tail => true::true::encode a (encode b tail)

/-- Every occurrence of a literal payload is counted, including repeated words. -/
def literalCells : Expr→ℕ
  | .literal bits => bits.length
  | .add a b | .sub a b | .mul a b => literalCells a+literalCells b

/-- Exact physical syntax size, including both tags and literal delimiters. -/
def size : Expr→ℕ
  | .literal bits => 2*bits.length+3
  | .add a b | .sub a b | .mul a b => size a+size b+2

/-- The actual syntax consumes exactly its own counted physical prefix. -/
theorem encode_length (expr : Expr) (tail : List Bool) :
    (encode expr tail).length=size expr+tail.length := by
  induction expr generalizing tail <;>
    simp_all only [encode,size,List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length] <;> omega

/-- Framed payloads preserve arbitrary literal stream suffixes. -/
theorem frame_append (word tail : List Bool) : frame word tail=frame word []++tail := by
  induction word with
  | nil => rfl
  | cons b word ih => simpa only [frame,List.cons_append] using congrArg (fun t=>true::b::t) ih

/-- Encoding retains the exact supplied suffix, without an input-sized label. -/
theorem encode_append (expr : Expr) (tail : List Bool) :
    encode expr tail=encode expr []++tail := by
  induction expr generalizing tail with
  | literal bits => exact congrArg (fun s=>false::false::s) (frame_append bits tail)
  | add a b ia ib =>
    change false::true::encode a (encode b tail)=false::true::(encode a (encode b [])++tail)
    apply congrArg (fun s=>false::true::s)
    rw [ia (encode b tail),ib tail,ia (encode b []),List.append_assoc]
  | sub a b ia ib =>
    change true::false::encode a (encode b tail)=true::false::(encode a (encode b [])++tail)
    apply congrArg (fun s=>true::false::s)
    rw [ia (encode b tail),ib tail,ia (encode b []),List.append_assoc]
  | mul a b ia ib =>
    change true::true::encode a (encode b tail)=true::true::(encode a (encode b [])++tail)
    apply congrArg (fun s=>true::true::s)
    rw [ia (encode b tail),ib tail,ia (encode b []),List.append_assoc]

/-- Whole syntax acquisition must pay every literal occurrence and node tag. -/
theorem size_le (expr : Expr) : size expr ≤ 2*literalCells expr+3*nodes expr := by
  induction expr <;> simp_all only [size,literalCells,nodes] <;> omega

/-- Every syntax tree occupies a nonempty physical prefix. -/
theorem size_pos (expr : Expr) : 0 < size expr := by
  cases expr <;> simp only [size] <;> omega

/-- The two-tag syntax always begins with two actual available Boolean cells. -/
theorem encode_two_tags (expr : Expr) (tail : List Bool) :
    ∃a b rest,encode expr tail=a::b::rest := by
  cases expr <;> exact ⟨_,_,_,rfl⟩

end RiemannGaussian.SemiprimeD1StackExprCodec
