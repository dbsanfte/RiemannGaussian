/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceScoreWeightBits
import RiemannGaussian.SemiprimeReportPolynomialGrowth

/-! # Acquired collision-count powers without unary cardinality expansion
The actual Boolean multiplier keeps its fixed base as the left operand, so
high-zero padding grows only linearly with the original exponent. Natural
exponent/control and report stages retain their explicit native interface.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeSourceCountPowers
open SemiprimeBitArithmetic SemiprimeSourceOffsetInputsCore
open SemiprimeReportPolynomialGrowth

/-- Repeated physical multiplication; no native power supplies the output. -/
def powerBits (base : List Bool) : ℕ → NatRun
  | 0 => ⟨[true],1⟩
  | k+1 =>
    let old := powerBits base k
    let out := mulBits base old.bits
    ⟨out.bits,old.clock+bitCost out+out.bits.length+3⟩

/-- The returned bits encode the exact power on every original exponent. -/
theorem powerBits_value (base : List Bool) (k : ℕ) :
    bitValue (powerBits base k).bits=bitValue base^k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [powerBits,mulBits_correct,ih,pow_succ,Nat.mul_comm]

/-- Fixing the multiplier's left operand prevents repeated doubling of padding. -/
theorem powerBits_length (base : List Bool) (k : ℕ) :
    (powerBits base k).bits.length ≤ 2*k*base.length+1 := by
  induction k with
  | zero => simp [powerBits]
  | succ k ih =>
    have hm := mulBits_length base (powerBits base k).bits
    simp only [powerBits]
    nlinarith

/-- A single physical product and its returned payload scan at exponent cap K. -/
def stepBudget (B K : ℕ) : ℕ :=
  12*B*(B+(2*K*B+1)+2)+1+(2*K*B+1)+3

/-- All repeated products and output-cell work are bounded without a power oracle. -/
theorem powerBits_clock (base : List Bool) (k K : ℕ) (hk : k ≤ K) :
    (powerBits base k).clock ≤ 1+k*stepBudget base.length K := by
  induction k with
  | zero => simp [powerBits]
  | succ k ih =>
    have hc := ih (by omega)
    have hl := powerBits_length base k
    have ho := powerBits_length base (k+1)
    have hm := mulBits_cost base (powerBits base k).bits
    have hk' : k ≤ K := by omega
    have hx : (powerBits base k).bits.length ≤ 2*K*base.length+1 := by
      exact hl.trans (Nat.add_le_add_right (Nat.mul_le_mul_right base.length
        (Nat.mul_le_mul_left 2 hk')) 1)
    have hy : (powerBits base (k+1)).bits.length ≤ 2*K*base.length+1 := by
      exact ho.trans (Nat.add_le_add_right (Nat.mul_le_mul_right base.length
        (Nat.mul_le_mul_left 2 hk)) 1)
    have hp : bitCost (mulBits base (powerBits base k).bits) ≤
        12*base.length*(base.length+(2*K*base.length+1)+2)+1 := by
      apply hm.trans
      gcongr
    change (powerBits base k).clock+bitCost (mulBits base (powerBits base k).bits)+
      (powerBits base (k+1)).bits.length+3 ≤ _
    unfold stepBudget at hc ⊢
    nlinarith

/-- Four physically acquired constants shared by every original score term. -/
structure Powers where
  /-- L squared, where the original alphabet has L=r^Q words. -/
  square : List Bool
  /-- L cubed. -/
  cube : List Bool
  /-- L to the fourth power, the original padding denominator. -/
  fourth : List Bool
  /-- The distinct-key head count, r to the power 4Q-1. -/
  head : List Bool
  /-- All input acquisition and physical multiplication reports. -/
  clock : ℕ

/-- Acquire only original r, then produce all four constants physically. -/
def acquire (r Q : ℕ) : Powers :=
  let base := natBits r
  let square := powerBits base.bits (2*Q)
  let cube := powerBits base.bits (3*Q)
  let fourth := powerBits base.bits (4*Q)
  let head := powerBits base.bits (4*Q-1)
  ⟨square.bits,cube.bits,fourth.bits,head.bits,
    base.clock+square.clock+cube.clock+fourth.clock+head.clock+5⟩

/-- The actual acquired payloads, with no input encoded-power or count advice. -/
theorem acquire_value (r Q : ℕ) :
    bitValue (acquire r Q).square=r^(2*Q) ∧
    bitValue (acquire r Q).cube=r^(3*Q) ∧
    bitValue (acquire r Q).fourth=r^(4*Q) ∧
    bitValue (acquire r Q).head=r^(4*Q-1) := by
  simp only [acquire,powerBits_value,natBits_value,and_self]

/-- A common actual array bound polynomial in original r,Q, independent of L^4. -/
def width (r Q : ℕ) : ℕ := 8*Q*(r+1)+1

/-- All four payload widths follow physical multiplication growth. -/
theorem acquire_length (r Q : ℕ) :
    (acquire r Q).square.length ≤ width r Q ∧
    (acquire r Q).cube.length ≤ width r Q ∧
    (acquire r Q).fourth.length ≤ width r Q ∧
    (acquire r Q).head.length ≤ width r Q := by
  have hb := natBits_length r
  have h2 := powerBits_length (natBits r).bits (2*Q)
  have h3 := powerBits_length (natBits r).bits (3*Q)
  have h4 := powerBits_length (natBits r).bits (4*Q)
  have hh := powerBits_length (natBits r).bits (4*Q-1)
  have hh' : 4*Q-1 ≤ 4*Q := by omega
  have h2' : 2*(2*Q)*(natBits r).bits.length+1 ≤ width r Q := by
    unfold width
    nlinarith
  have h3' : 2*(3*Q)*(natBits r).bits.length+1 ≤ width r Q := by
    unfold width
    nlinarith
  have h4' : 2*(4*Q)*(natBits r).bits.length+1 ≤ width r Q := by
    unfold width
    nlinarith
  have hh'' : 2*(4*Q-1)*(natBits r).bits.length+1 ≤ width r Q := by
    apply le_trans _ h4'
    gcongr
  exact ⟨h2.trans h2',h3.trans h3',h4.trans h4',hh.trans hh''⟩

/-- Closed input/multiplication budget with no exponential materialized factor. -/
def budget (r Q : ℕ) : ℕ :=
  20*(r+1)^2+4*(1+4*Q*stepBudget (r+1) (4*Q))+5

/-- The complete actual power acquisition has original-dimension polynomial work. -/
theorem acquire_clock (r Q : ℕ) : (acquire r Q).clock ≤ budget r Q := by
  have hb := natBits_clock r
  have hl := natBits_length r
  have h2 := powerBits_clock (natBits r).bits (2*Q) (4*Q) (by omega)
  have h3 := powerBits_clock (natBits r).bits (3*Q) (4*Q) (by omega)
  have h4 := powerBits_clock (natBits r).bits (4*Q) (4*Q) (by omega)
  have hh := powerBits_clock (natBits r).bits (4*Q-1) (4*Q) (by omega)
  have hs : stepBudget (natBits r).bits.length (4*Q) ≤ stepBudget (r+1) (4*Q) := by
    unfold stepBudget
    gcongr
  have h2' : 1+2*Q*stepBudget (natBits r).bits.length (4*Q) ≤
      1+4*Q*stepBudget (r+1) (4*Q) := by gcongr; omega
  have h3' : 1+3*Q*stepBudget (natBits r).bits.length (4*Q) ≤
      1+4*Q*stepBudget (r+1) (4*Q) := by gcongr; omega
  have h4' : 1+4*Q*stepBudget (natBits r).bits.length (4*Q) ≤
      1+4*Q*stepBudget (r+1) (4*Q) := by gcongr
  have hh' : 1+(4*Q-1)*stepBudget (natBits r).bits.length (4*Q) ≤
      1+4*Q*stepBudget (r+1) (4*Q) := by gcongr; omega
  unfold acquire budget
  dsimp only
  omega

/-- Fixed constants precede the entire original-dimension family. -/
theorem budget_monomial : ∃ C k : ℕ,∀ r Q S,r ≤ S → Q ≤ S → budget r Q ≤ C*(S+1)^k := by
  have hp : Bound (fun S => budget S S) := by
    simp only [budget,stepBudget]
    boundArithmetic
  obtain ⟨C,k,h⟩ := hp
  refine ⟨C,k,?_⟩
  intro r Q S hr hQ
  apply le_trans _ (h S)
  simp only [budget,stepBudget]
  gcongr

end RiemannGaussian.SemiprimeSourceCountPowers
