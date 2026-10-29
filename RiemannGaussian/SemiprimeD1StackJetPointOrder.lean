/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetPoint
import RiemannGaussian.SemiprimeD1JetRingBits
import RiemannGaussian.SemiprimeSourceCompactWordIds
/-! # Proof-side descending convolution order
These definitions describe the scalar effects of the physical counter loops;
they are specifications, not executable instruction or coefficient suppliers.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RiemannGaussian.SemiprimeD1StackJetPointOrder
open SemiprimeBitArithmetic (bitValue bitValue_lt_width)
open SemiprimeD1JetAxes (Context)
namespace S
export SemiprimeD1JetScalarBits (add mul)
end S
namespace J
export SemiprimeD1JetRingBits (plan term mulAt read)
end J

/-- The actual nested physical decrement loops visit these pairs. -/
def descending (rank : ℕ) : List (ℕ×ℕ) :=
  (List.range rank).reverse.flatMap (fun i=>(List.range rank).reverse.map (fun j=>(i,j)))

/-- Descending visits contain exactly the original pairs, including duplicates. -/
theorem descending_perm (rank : ℕ) : (descending rank).Perm (J.plan rank) := by
  apply List.Perm.flatMap (List.reverse_perm _)
  intro i hi
  exact (List.reverse_perm _).map (fun j=>(i,j))

/-- Proof-side scalar effect of one physically routed pair. -/
def pairStep (ctx : Context) (a b : List (List Bool)) (k : ℕ) (ij : ℕ×ℕ) (acc : List Bool) : List Bool :=
  if SemiprimeD1JetRouting.admissible ctx.axes ij.1 ij.2 ∧
      SemiprimeD1JetRouting.sumIndex ctx.axes ij.1 ij.2=k then
    (S.add ctx.precision (S.mul ctx.precision (J.read a ij.1).bits (J.read b ij.2).bits).bits acc).bits
  else acc

/-- Every acquired scalar effect is the original term plus the current sum. -/
theorem pairStep_value (ctx : Context) (a b : List (List Bool)) (k : ℕ) (ij : ℕ×ℕ) (acc : List Bool) :
    (bitValue (pairStep ctx a b k ij acc):ZMod (2^ctx.precision))=
      (bitValue (J.term ctx a b k ij).bits:ZMod (2^ctx.precision))+(bitValue acc:ZMod (2^ctx.precision)) := by
  rw [SemiprimeD1JetRingBits.term_value]
  unfold pairStep
  split_ifs with h
  · rw [SemiprimeD1JetScalarBits.add_zmod,SemiprimeD1JetScalarBits.mul_zmod]
    simp only [SemiprimeD1JetRingBits.read_bits,SemiprimeD1JetRingBits.coefficient]
  · simp

/-- Proof-side fold of the physical pair order. -/
def accumulate (ctx : Context) (a b : List (List Bool)) (k : ℕ) : List (ℕ×ℕ) → List Bool → List Bool
  | [],acc => acc
  | ij::rest,acc => accumulate ctx a b k rest (pairStep ctx a b k ij acc)

/-- All scalar effects add to the exact original finite term sum. -/
theorem accumulate_value (ctx : Context) (a b : List (List Bool)) (k : ℕ)
    (pairs : List (ℕ×ℕ)) (acc : List Bool) :
    (bitValue (accumulate ctx a b k pairs acc):ZMod (2^ctx.precision))=
      (pairs.map (fun ij=>(bitValue (J.term ctx a b k ij).bits:ZMod (2^ctx.precision)))).sum+
        (bitValue acc:ZMod (2^ctx.precision)) := by
  induction pairs generalizing acc with
  | nil => simp [accumulate]
  | cons ij rest ih =>
    rw [accumulate,ih,pairStep_value,List.map_cons,List.sum_cons]
    abel

/-- Every intermediate scalar output is canonical, including all skipped terms. -/
theorem accumulate_compact (ctx : Context) (a b : List (List Bool)) (k : ℕ)
    (pairs : List (ℕ×ℕ)) (acc : List Bool) (hc : SemiprimeSourceCompactBits.Compact acc) :
    SemiprimeSourceCompactBits.Compact (accumulate ctx a b k pairs acc) := by
  induction pairs generalizing acc with
  | nil => exact hc
  | cons ij rest ih =>
    apply ih
    unfold pairStep
    split_ifs
    · exact SemiprimeD1JetScalarBits.add_compact _ _ _
    · exact hc

/-- Every intermediate scalar has the actual precision width. -/
theorem accumulate_length (ctx : Context) (a b : List (List Bool)) (k : ℕ)
    (pairs : List (ℕ×ℕ)) (acc : List Bool) (hc : acc.length ≤ ctx.precision) :
    (accumulate ctx a b k pairs acc).length ≤ ctx.precision := by
  induction pairs generalizing acc with
  | nil => exact hc
  | cons ij rest ih =>
    apply ih
    unfold pairStep
    split_ifs
    · exact SemiprimeD1JetScalarBits.add_length _ _ _
    · exact hc

/-- Descending scalar accumulation has exactly the original coefficient bytes.
No positivity, input word bound or intermediate fit oracle is required. -/
theorem descending_eq_original (ctx : Context) (a b : List (List Bool)) (k : ℕ) :
    accumulate ctx a b k (descending ctx.rank) []=(J.mulAt ctx a b k).bits := by
  have hv:=accumulate_value ctx a b k (descending ctx.rank) []
  have hp:=(descending_perm ctx.rank).map (fun ij=>(bitValue (J.term ctx a b k ij).bits:ZMod (2^ctx.precision)))
  rw [hp.sum_eq] at hv
  have ht : (bitValue (J.mulAt ctx a b k).bits:ZMod (2^ctx.precision))=
      ((J.plan ctx.rank).map (fun ij=>(bitValue (J.term ctx a b k ij).bits:ZMod (2^ctx.precision)))).sum := by
    simpa only [SemiprimeD1JetRingBits.mulAt,List.map_map,Function.comp_def] using
      SemiprimeD1JetRingBits.sumReports_value ctx.precision ((J.plan ctx.rank).map (J.term ctx a b k))
  have he : (bitValue (accumulate ctx a b k (descending ctx.rank) []):ZMod (2^ctx.precision))=
      (bitValue (J.mulAt ctx a b k).bits:ZMod (2^ctx.precision)) := by
    simp only [bitValue,Nat.cast_zero,add_zero] at hv
    exact hv.trans ht.symm
  have hc:=accumulate_compact ctx a b k (descending ctx.rank) [] (by trivial)
  have hl:=accumulate_length ctx a b k (descending ctx.rank) [] (by simp)
  have hr:=SemiprimeD1JetRingBits.mulAt_length ctx a b k
  have hlo : bitValue (accumulate ctx a b k (descending ctx.rank) [])<2^ctx.precision :=
    (bitValue_lt_width _).trans_le (Nat.pow_le_pow_right (by decide : 1≤2) hl)
  have hro : bitValue (J.mulAt ctx a b k).bits<2^ctx.precision :=
    (bitValue_lt_width _).trans_le (Nat.pow_le_pow_right (by decide : 1≤2) hr)
  let _ : NeZero (2^ctx.precision) := ⟨by positivity⟩
  have hn:=congrArg ZMod.val he
  simp only [ZMod.val_natCast,Nat.mod_eq_of_lt hlo,Nat.mod_eq_of_lt hro] at hn
  exact SemiprimeSourceCompactWordIds.compact_value_injective _ _ hc
    (SemiprimeD1JetRingBits.mulAt_compact _ _ _ _) hn

end RiemannGaussian.SemiprimeD1StackJetPointOrder
