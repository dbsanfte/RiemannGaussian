/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeNormalizedInverseBits

/-! # Actual normalized inverse loop clock
The bound charges physical arithmetic, cached pair reads, list allocation and
array-prefix copying. Initial source production and a full address/tape simulation
are separate. There is no inverse coefficient or intermediate fit input.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeNormalizedInverseBitsBounds
open SemiprimeRationalBits SemiprimeDotBits SemiprimeJetBits
open SemiprimeNormalizedInverseBits

/-- A polynomial uniform bound for one cached extension. -/
def stepBudget (W A J : ℕ) : ℕ :=
  J*(40000*(W+1)^3+4)+4+20000*(W+1)^3+
    J*((A+1)*(2*W+3)+(J+1)*(2*W+3)+5)+
    (J+1)*(2*W+3)+2*W+10

/-- Paid pair formation and scalar operations are bounded at every prefix. -/
theorem extend_clock (template : List Bool) (ht : 0<template.length)
    (a : Array RationalWord) (A J n : ℕ) (old : JetReport)
    (ha : a.size≤A) (hn : n≤J) (hold : old.words.size≤J)
    (haw : Bounded a template.length) (how : Bounded old.words template.length) :
    (extend template a n old).clock≤old.clock+stepBudget template.length A J := by
  by_cases hz : n=0
  · simp only [extend,ite_eq_left hz]
    unfold stepBudget
    omega
  · have hp (p) (hm : p∈pairs a old.words n) : Width p.1 template.length ∧ Width p.2 template.length := by
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hm
      exact ⟨wordAt_width a ht haw _,wordAt_width old.words ht how _⟩
    have hs := dotBits_cost template ht (pairs a old.words n) hp
    rw [pairs_length] at hs
    have ho := executeOperation_cost .neg (dotBits template (pairs a old.words n)).word
      zeroWord template (dotBits_width template ht _) (show Width zeroWord template.length from ⟨by simp [zeroWord],by simpa [zeroWord] using (show 1≤template.length by omega)⟩) le_rfl
    have hm : n*(accessCost template a+accessCost template old.words+5)+
        (old.words.size+1)*(2*template.length+3) ≤
        J*((A+1)*(2*template.length+3)+(J+1)*(2*template.length+3)+5)+
          (J+1)*(2*template.length+3) := by
      unfold accessCost
      gcongr
    have hn' := Nat.mul_le_mul_right (40000*(template.length+1)^3+4) hn
    simp only [extend,ite_eq_right hz]
    unfold stepBudget
    omega

/-- Polynomial clock for the actual complete cached inverse construction. -/
theorem build_clock (template : List Bool) (ht : 0<template.length)
    (a : Array RationalWord) (A J : ℕ) (ha : a.size≤A)
    (haw : Bounded a template.length) :
    ∀ n≤J, (build template a n).clock≤1+n*stepBudget template.length A J := by
  intro n hn
  induction n with
  | zero => simp [build]
  | succ n ih =>
    have hc := extend_clock template ht a A J n (build template a n) ha (by omega)
      (by simpa using (show n≤J by omega)) haw (build_bounded template ht a n)
    have hh := ih (by omega)
    change (extend template a n (build template a n)).clock≤_
    calc
      _ ≤ (build template a n).clock+stepBudget template.length A J := hc
      _ ≤ 1+(n+1)*stepBudget template.length A J := by nlinarith

end RiemannGaussian.SemiprimeNormalizedInverseBitsBounds
