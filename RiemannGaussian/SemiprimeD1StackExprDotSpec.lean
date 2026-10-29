/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackExprDot

/-! # Exact counted source syntax for the original DFT expression
The original natural-index input function is represented by the actual framed
word vector. Selected words below specify the output of the real cached reader;
they are never arguments of the executing instruction table.
-/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackExprDotSpec
open SemiprimeMacroEntryBitPrimitives (Expr powerExpr dotExpr)
open SemiprimeD1StackExprCodec (encode)
open SemiprimeSourceHistogramKeyBits (frame)

/-- The old default-zero natural-index view of the actual physical word cache. -/
def wordAt (words : List (List Bool)) (j : ℕ) : List Bool := (words[j]?).getD []
/-- Exact term acquired from real word read, exponent products, Power and Frame. -/
def term (baseCode : List Bool) (words : List (List Bool)) (stride frequency j : ℕ)
    (tail : List Bool) : List Bool :=
  true::true::false::false::frame (wordAt words j)
    (SemiprimeD1StackExprPowerSpec.result (stride*(j*frequency)) baseCode tail)
/-- Descending physical construction prepends the terms into original ascending order. -/
def terms : ℕ→List Bool→List (List Bool)→ℕ→ℕ→List Bool→List Bool
  | 0,_,_,_,_,tail => tail
  | n+1,baseCode,words,stride,frequency,tail =>
      terms n baseCode words stride frequency (term baseCode words stride frequency n tail)
/-- Each original addition constructor is a literal false/true tag pair. -/
def addTags : ℕ→List Bool→List Bool
  | 0,word => word
  | n+1,word => false::true::addTags n word
/-- Complete code produced by term construction, zero and additive-tag passes. -/
def result (n : ℕ) (baseCode : List Bool) (words : List (List Bool)) (stride frequency : ℕ)
    (tail : List Bool) : List Bool :=
  addTags n (false::false::false::terms n baseCode words stride frequency tail)

/-- Literal physical tag pushes agree regardless of their loop visit order. -/
theorem addTags_push (n : ℕ) (word : List Bool) :
    addTags n (false::true::word)=false::true::addTags n word := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (fun t=>false::true::t) ih

/-- Exact original syntax of ONE acquired DFT term, including the integer
exponent formula. No mathematical power is executed by the source builder. -/
theorem term_original (baseExpr : Expr) (words : List (List Bool)) (stride frequency j : ℕ)
    (tail : List Bool) :
    term (encode baseExpr []) words stride frequency j tail=
      encode (.mul (.literal (wordAt words j)) (powerExpr baseExpr (stride*(j*frequency)))) tail := by
  unfold term
  rw [SemiprimeD1StackExprPowerSpec.result_original]
  rfl

/-- The acquired source is EXACTLY the original dotExpr, retaining every
repeated word/base/power and the complete supplied physical suffix. -/
theorem result_original (baseExpr : Expr) (words : List (List Bool)) (stride frequency n : ℕ)
    (tail : List Bool) :
    result n (encode baseExpr []) words stride frequency tail=
      encode (dotExpr baseExpr stride frequency (wordAt words) n) tail := by
  induction n generalizing tail with
  | zero => rfl
  | succ n ih =>
    have h:=ih (term (encode baseExpr []) words stride frequency n tail)
    rw [term_original] at h
    change false::true::result n (encode baseExpr []) words stride frequency
        (term (encode baseExpr []) words stride frequency n tail)=
      false::true::encode (dotExpr baseExpr stride frequency (wordAt words) n)
        (encode (.mul (.literal (wordAt words n)) (powerExpr baseExpr (stride*(n*frequency)))) tail)
    rw [term_original]
    exact congrArg (fun t=>false::true::t) h

/-- Exact repeated-base, delimiter, tag and selected-word growth of a term. -/
theorem term_length (baseCode : List Bool) (words : List (List Bool)) (stride frequency j : ℕ)
    (tail : List Bool) :
    (term baseCode words stride frequency j tail).length=
      2*(wordAt words j).length+2*(stride*(j*frequency))+5+
        (stride*(j*frequency))*baseCode.length+tail.length+5 := by
  simp only [term,List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length,
    SemiprimeD1StackExprPowerSpec.result_length]
  omega

end RiemannGaussian.SemiprimeD1StackExprDotSpec
