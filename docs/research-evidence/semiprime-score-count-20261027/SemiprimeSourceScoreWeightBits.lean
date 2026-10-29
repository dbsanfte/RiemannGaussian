/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceOffsetInputsCore

/-! # Physical unsigned weighting of the original integer source counts
All multiplications and the final sum execute Boolean circuits. Natural dimensions
remain host loop inputs at the explicitly acquired initializer boundary.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeSourceScoreWeightBits
open SemiprimeBitArithmetic SemiprimeSourceOffsetInputsCore SemiprimeRationalBits

/-- Two cached integer weights and the work of their actual acquisition. -/
structure Weights where
  /-- Weight of the incidence count. -/
  incidence : List Bool
  /-- Weight of the head count. -/
  head : List Bool
  /-- Seven executed multiplication reports and control/cell work. -/
  clock : ℕ

/-- Cache both weights once from the four original acquired unsigned words. -/
def weights (M n lam U : List Bool) : Weights :=
  let nn := mulBits n n
  let ll := mulBits lam lam
  let uu := mulBits U U
  let nl := mulBits nn.bits ll.bits
  let a := mulBits nl.bits uu.bits
  let mm := mulBits M M
  let b := mulBits [false,false,true] mm.bits
  ⟨a.bits,b.bits,bitCost nn+bitCost ll+bitCost uu+bitCost nl+bitCost a+
    bitCost mm+bitCost b+M.length+n.length+lam.length+U.length+30⟩

/-- Exact incidence and head coefficients of the physical weighted count. -/
theorem weights_value (M n lam U : List Bool) :
    bitValue (weights M n lam U).incidence=bitValue n^2*bitValue lam^2*bitValue U^2 ∧
      bitValue (weights M n lam U).head=4*bitValue M^2 := by
  simp only [weights,mulBits_correct,bitValue,bitNat,Bool.false_eq_true,ite_false,
    ite_true]
  constructor <;> ring

/-- Per-candidate physical multiplication and summation, reusing cached weights. -/
def combine (w : Weights) (I H : List Bool) : NatRun :=
  let a := mulBits w.incidence I
  let b := mulBits w.head H
  let out := addBits a.bits b.bits false
  ⟨out.bits,bitCost a+bitCost b+bitCost out+I.length+H.length+10⟩

/-- The count words, rather than advised count integers, drive the circuit. -/
theorem combine_value (w : Weights) (I H : List Bool) :
    bitValue (combine w I H).bits=
      bitValue w.incidence*bitValue I+bitValue w.head*bitValue H := by
  simp [combine,addBits_correct,mulBits_correct,bitNat]

/-- Denominator-one physical comparator input, without rational normalization. -/
def scoreWord (w : Weights) (I H : List Bool) : RationalWord :=
  ⟨⟨false,(combine w I H).bits⟩,[true]⟩

/-- A denominator-one output is always legal, independently of its magnitude. -/
theorem scoreWord_valid (w : Weights) (I H : List Bool) : (scoreWord w I H).Valid := by
  change 0<(1:ℕ)
  decide

/-- Decoding is used only to state correctness of the physical output. -/
theorem scoreWord_value (w : Weights) (I H : List Bool) :
    (scoreWord w I H).value=
      ((bitValue w.incidence*bitValue I+bitValue w.head*bitValue H:ℕ):ℚ) := by
  simp [scoreWord,RationalWord.value,SemiprimeBitIndexClipping.SignedWord.value,
    combine_value,bitValue,bitNat]

/-- Uniform physical size for both cached weights. -/
def weightWidth (L : ℕ) : ℕ := 100*(L+1)

/-- Both actual weight arrays have polynomial size in the original input widths. -/
theorem weights_length (M n lam U : List Bool) (L : ℕ)
    (hM : M.length ≤ L) (hn : n.length ≤ L) (hl : lam.length ≤ L) (hU : U.length ≤ L) :
    (weights M n lam U).incidence.length ≤ weightWidth L ∧
      (weights M n lam U).head.length ≤ weightWidth L := by
  have h1 := mulBits_length n n
  have h2 := mulBits_length lam lam
  have h3 := mulBits_length U U
  have h4 := mulBits_length (mulBits n n).bits (mulBits lam lam).bits
  have h5 := mulBits_length (mulBits (mulBits n n).bits (mulBits lam lam).bits).bits
    (mulBits U U).bits
  have h6 := mulBits_length M M
  have h7 := mulBits_length [false,false,true] (mulBits M M).bits
  simp only [List.length_cons,List.length_nil] at h7
  dsimp only [weights,weightWidth]
  constructor <;> omega

/-- Generic physical multiplier cost with bounded original operand arrays. -/
theorem mul_cost_le (a b : List Bool) (L : ℕ) (ha : a.length ≤ L) (hb : b.length ≤ L) :
    bitCost (mulBits a b) ≤ 12*L*(2*L+2)+1 := by
  apply (mulBits_cost a b).trans
  gcongr
  omega

/-- Closed acquisition budget for the seven cached-weight products. -/
def weightBudget (L : ℕ) : ℕ :=
  7*(12*weightWidth L*(2*weightWidth L+2)+1)+4*L+30

/-- All actual products and their original input scans are retained. -/
theorem weights_clock (M n lam U : List Bool) (L : ℕ)
    (hM : M.length ≤ L) (hn : n.length ≤ L) (hl : lam.length ≤ L) (hU : U.length ≤ L) :
    (weights M n lam U).clock ≤ weightBudget L := by
  let K := weightWidth L
  have hk : L ≤ K := by dsimp [K,weightWidth];omega
  have h1 := mulBits_length n n
  have h2 := mulBits_length lam lam
  have h3 := mulBits_length U U
  have h4 := mulBits_length (mulBits n n).bits (mulBits lam lam).bits
  have h6 := mulBits_length M M
  have hc1 := mul_cost_le n n K (hn.trans hk) (hn.trans hk)
  have hc2 := mul_cost_le lam lam K (hl.trans hk) (hl.trans hk)
  have hc3 := mul_cost_le U U K (hU.trans hk) (hU.trans hk)
  have hc4 := mul_cost_le (mulBits n n).bits (mulBits lam lam).bits K
    (by dsimp [K,weightWidth];omega) (by dsimp [K,weightWidth];omega)
  have hc5 := mul_cost_le (mulBits (mulBits n n).bits (mulBits lam lam).bits).bits
    (mulBits U U).bits K (by dsimp [K,weightWidth];omega) (by dsimp [K,weightWidth];omega)
  have hc6 := mul_cost_le M M K (hM.trans hk) (hM.trans hk)
  have hc7 := mul_cost_le [false,false,true] (mulBits M M).bits K
    (by simp only [List.length_cons,List.length_nil];dsimp [K,weightWidth];omega)
    (by dsimp [K,weightWidth];omega)
  dsimp only [weights,weightBudget]
  change _ ≤ 7*(12*K*(2*K+2)+1)+4*L+30
  omega

/-- Uniform per-candidate output width from actual operand widths. -/
theorem combine_length (w : Weights) (I H : List Bool) (L : ℕ)
    (ha : w.incidence.length ≤ L) (hb : w.head.length ≤ L)
    (hi : I.length ≤ L) (hh : H.length ≤ L) :
    (combine w I H).bits.length ≤ 3*L+1 := by
  have h1 := mulBits_length w.incidence I
  have h2 := mulBits_length w.head H
  have h3 := (addBits_counts (mulBits w.incidence I).bits
    (mulBits w.head H).bits false).2.2.2.2
  dsimp only [combine]
  omega

/-- Per-candidate Boolean circuit and original count scans. -/
def combineBudget (L : ℕ) : ℕ := 2*(12*L*(2*L+2)+1)+33*L+2*L+14

/-- Polynomial per-candidate cost requires only actual operand widths. -/
theorem combine_clock (w : Weights) (I H : List Bool) (L : ℕ)
    (ha : w.incidence.length ≤ L) (hb : w.head.length ≤ L)
    (hi : I.length ≤ L) (hh : H.length ≤ L) :
    (combine w I H).clock ≤ combineBudget L := by
  have h1 := mulBits_length w.incidence I
  have h2 := mulBits_length w.head H
  have hc1 := mul_cost_le w.incidence I L ha hi
  have hc2 := mul_cost_le w.head H L hb hh
  have hc3 := addBits_cost (mulBits w.incidence I).bits (mulBits w.head H).bits false
  have hmax : max (mulBits w.incidence I).bits.length (mulBits w.head H).bits.length ≤ 3*L := by
    apply max_le <;> omega
  dsimp only [combine,combineBudget]
  omega

end RiemannGaussian.SemiprimeSourceScoreWeightBits
