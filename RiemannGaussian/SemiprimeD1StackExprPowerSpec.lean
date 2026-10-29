/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackExprPower

/-! # Exact syntax produced by counted physical base copies
All repetition here specifies the output of the literal program. The evaluator
receives these bytes, never a supplied expression tree or desired power value.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackExprPowerSpec
open SemiprimeMacroEntryBitPrimitives (Expr powerExpr)
open SemiprimeD1StackExprCodec (encode)

/-- Output of repeating the real base-code Copy a counted number of times. -/
def repeated : ℕ→List Bool→List Bool→List Bool
  | 0,_,tail => tail
  | n+1,baseCode,tail => baseCode++repeated n baseCode tail
/-- Each multiplication constructor is two physical true bits. -/
def tags : ℕ→List Bool→List Bool
  | 0,word => word
  | n+1,word => true::true::tags n word
/-- Exact fixed literal-one tag and framed-payload bits. -/
def oneCode : List Bool := [false,false,true,true,false]
/-- Expected code after BOTH physical loops and the five literal-one pushes. -/
def result (n : ℕ) (baseCode tail : List Bool) : List Bool :=
  tags n (oneCode++repeated n baseCode tail)

/-- A repeated identical base block commutes with its own remaining block stream. -/
theorem repeated_push (n : ℕ) (baseCode tail : List Bool) :
    repeated n baseCode (baseCode++tail)=baseCode++repeated n baseCode tail := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change baseCode++repeated n baseCode (baseCode++tail)=baseCode++(baseCode++repeated n baseCode tail)
    rw [ih]

/-- The two tag pushes commute with an already produced identical-tag tags. -/
theorem prefix_push (n : ℕ) (word : List Bool) :
    tags n (true::true::word)=true::true::tags n word := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (fun t=>true::true::t) ih

/-- The source bytes are the EXACT original repeated-multiplication expression,
with every repeated base subtree retained, rather than a numerical power oracle. -/
theorem result_original (baseExpr : Expr) (n : ℕ) (tail : List Bool) :
    result n (encode baseExpr []) tail=encode (powerExpr baseExpr n) tail := by
  induction n generalizing tail with
  | zero => rfl
  | succ n ih =>
    have h:=ih (encode baseExpr []++tail)
    unfold result at h
    rw [repeated_push] at h
    change true::true::tags n (oneCode++(encode baseExpr []++repeated n (encode baseExpr []) tail))=
      true::true::encode (powerExpr baseExpr n) (encode baseExpr tail)
    rw [SemiprimeD1StackExprCodec.encode_append baseExpr tail]
    exact congrArg (fun t=>true::true::t) h

/-- Actual repeated-base output size includes EVERY copied base occurrence. -/
theorem repeated_length (n : ℕ) (baseCode tail : List Bool) :
    (repeated n baseCode tail).length=n*baseCode.length+tail.length := by
  induction n with
  | zero => simp only [repeated,Nat.zero_mul,Nat.zero_add]
  | succ n ih => simp only [repeated,List.length_append,ih,Nat.succ_mul];omega
/-- Every emitted multiplication tag cell is retained in physical output size. -/
theorem prefix_length (n : ℕ) (word : List Bool) :
    (tags n word).length=2*n+word.length := by
  induction n with
  | zero => simp only [tags,Nat.mul_zero,Nat.zero_add]
  | succ n ih => simp only [tags,List.length_cons,ih];omega
/-- Total code size pays both counted construction passes and the supplied tail. -/
theorem result_length (n : ℕ) (baseCode tail : List Bool) :
    (result n baseCode tail).length=2*n+5+n*baseCode.length+tail.length := by
  simp only [result,prefix_length,List.length_append,oneCode,List.length_cons,List.length_nil,repeated_length]
  omega

end RiemannGaussian.SemiprimeD1StackExprPowerSpec
