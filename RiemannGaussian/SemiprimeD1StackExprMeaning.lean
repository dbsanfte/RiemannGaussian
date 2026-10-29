/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackExprArithmetic
import RiemannGaussian.SemiprimeD1StackExprDispatch
/-! # Original-only semantic obligations for the executed operator calls -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1StackExprMeaning
open SemiprimeD1StackExpr
open SemiprimeMacroEntryBitPrimitives (Expr execute Valid execute_bounds)
/-- Proof-side original constructor corresponding to the physically read finite tag. -/
def node : Op→Expr→Expr→Expr
  | .add,a,b=>.add a b
  | .sub,a,b=>.sub a b
  | .mul,a,b=>.mul a b
/-- Actual original constructor bytes agree with the fixed tag dispatcher. -/
theorem encode_node (op : Op) (a b : Expr) (tail : List Bool) :
    SemiprimeD1StackExprCodec.encode (node op a b) tail=
      SemiprimeD1StackExprDispatch.tags op
        (SemiprimeD1StackExprCodec.encode a (SemiprimeD1StackExprCodec.encode b tail)) := by
  cases op <;> rfl

/-- Exact operator-byte refinement uses only ORIGINAL literal validity. The
canonical child premises are derived from execute_bounds, never supplied as
an intermediate-value, height, Fits or arithmetic-answer oracle. -/
theorem arithmetic_original (op : Op) (cached : List Bool) (a b : Expr)
    (hm : 0<SemiprimeBitArithmetic.bitValue cached) (ha : Valid cached a) (hb : Valid cached b) :
    SemiprimeD1StackExprArithmetic.word op (execute cached a).bits (execute cached b).bits cached=
      (execute cached (node op a b)).bits := by
  have hleft := execute_bounds cached hm a ha
  have hright := execute_bounds cached hm b hb
  cases op with
  | add=>
    exact SemiprimeD1StackResidueAddBounds.residue_original _ _ cached hleft.2 hright.2
  | sub=>
    exact SemiprimeD1StackResidueSubBounds.residue_original _ _ cached hleft.2 hright.2
  | mul=>
    exact SemiprimeD1StackResidueMulBounds.residue_original _ _ cached hm

/-- Actual complete arithmetic transition envelope from original child syntax
and literal validity. No supplied intermediate widths or operation clocks. -/
theorem arithmetic_time_le (op : Op) (cached : List Bool) (a b : Expr)
    (hm : 0<SemiprimeBitArithmetic.bitValue cached) (ha : Valid cached a) (hb : Valid cached b) :
    SemiprimeD1StackExprArithmetic.time op (execute cached a).bits (execute cached b).bits cached≤
      10000*(3*cached.length+3)^3 := by
  have hleft := (execute_bounds cached hm a ha).1
  have hright := (execute_bounds cached hm b hb).1
  have hpow : (3*cached.length+3)^2≤(3*cached.length+3)^3 :=
    Nat.pow_le_pow_right (by omega : 1≤3*cached.length+3) (by decide : 2≤3)
  cases op with
  | add=>
    have h := (SemiprimeD1StackResidueAddBounds.totalTime_le (execute cached a).bits (execute cached b).bits cached).trans
      (SemiprimeD1StackResidueAddBounds.timeBound_le_square _ _ _)
    simp only [hleft,hright,show cached.length+cached.length+cached.length=3*cached.length by omega] at h
    exact h.trans (by omega)
  | sub=>
    have h := (SemiprimeD1StackResidueSubBounds.totalTime_le (execute cached a).bits (execute cached b).bits cached).trans
      (SemiprimeD1StackResidueSubBounds.timeBound_le_cube _ _ _)
    simp only [hleft,hright,show cached.length+cached.length+cached.length=3*cached.length by omega] at h
    exact h.trans (by omega)
  | mul=>
    have h := (SemiprimeD1StackResidueMulBounds.totalTime_le (execute cached a).bits (execute cached b).bits cached).trans
      (SemiprimeD1StackResidueMulBounds.timeBound_le_cube _ _ _)
    simpa only [SemiprimeD1StackExprArithmetic.time,hleft,hright,show cached.length+cached.length+cached.length=3*cached.length by omega] using h
end RiemannGaussian.SemiprimeD1StackExprMeaning
