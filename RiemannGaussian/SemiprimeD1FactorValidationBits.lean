/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeBitPrimeScan

/-! # Physical binary proper-divisor validation and cofactor recovery
Original input and candidate are literal Boolean words. Ordering, restoring
division and remainder testing execute their bit programs. No natural-number
comparison, division or modulus supplies the validation result at runtime.
-/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1FactorValidationBits
open SemiprimeBitArithmetic SemiprimeBitDivision SemiprimeBitPrimeScan

/-- Actual validation flag, cofactor bits, and all physical component reports. -/
structure Run where
  /-- Ordinary proper-divisor test, assembled from actual bit flags. -/
  valid : Bool
  /-- Actual restoring quotient, available for completing the factor pair. -/
  cofactor : List Bool
  /-- Primitive comparison, division, remainder scans and final Boolean gates. -/
  clock : ℕ

/-- Closed physical validation from two literal binary words. -/
def run (input candidate : List Bool) : Run :=
  let lower := orderWords candidate [false,true]
  let upper := orderWords candidate input
  let division := divideBits input candidate
  let remainder := nonzeroBits division.remainder
  ⟨(!lower.difference.borrow && upper.difference.borrow) && !remainder.nonzero,
    division.quotient,lower.clock+upper.clock+division.clock+remainder.clock+7⟩

/-- Validation is precisely the ordinary integer proper-divisor predicate,
including arbitrary physical high-zero padding and all invalid candidates. -/
theorem run_valid (input candidate : List Bool) :
    (run input candidate).valid=true ↔
      2 ≤ bitValue candidate ∧ bitValue candidate < bitValue input ∧
        bitValue input%bitValue candidate=0 := by
  have hl := orderWords_less candidate [false,true]
  have hu := orderWords_less candidate input
  have hd := (divideBits_correct input candidate).2
  have hz := nonzeroBits_false_iff (divideBits input candidate).remainder
  have htwo : bitValue [false,true]=2 := rfl
  rw [htwo] at hl
  have hlo : (orderWords candidate [false,true]).difference.borrow=false ↔ 2 ≤ bitValue candidate := by
    constructor
    · intro h
      by_contra hn
      have hb := hl.mpr (by omega)
      rw [h] at hb
      exact Bool.false_ne_true hb
    · intro h
      apply Bool.eq_false_of_not_eq_true
      intro hb
      have hh := hl.mp hb
      omega
  change ((!_ && _) && !_)=true ↔ _
  simp only [Bool.and_eq_true,Bool.not_eq_true_eq_eq_false]
  rw [hlo,hu,hz,hd]
  exact and_assoc

/-- Literal cofactor bytes are the ordinary integer quotient on every input. -/
theorem run_cofactor (input candidate : List Bool) :
    bitValue (run input candidate).cofactor=bitValue input/bitValue candidate :=
  (divideBits_correct input candidate).1

/-- A valid result recovers an entire ordinary factor pair. -/
theorem run_factor_pair (input candidate : List Bool) (h : (run input candidate).valid=true) :
    bitValue candidate*bitValue (run input candidate).cofactor=bitValue input ∧
      2 ≤ bitValue candidate ∧ 2 ≤ bitValue (run input candidate).cofactor := by
  obtain ⟨hlo,hlt,hm⟩ := (run_valid input candidate).mp h
  have hpos : 0 < bitValue candidate := by omega
  have he := Nat.mod_add_div (bitValue input) (bitValue candidate)
  rw [hm,Nat.zero_add] at he
  have hq : 2 ≤ bitValue input/bitValue candidate := by
    by_contra hn
    have hle : bitValue input/bitValue candidate ≤ 1 := by omega
    have hh := Nat.mul_le_mul_left (bitValue candidate) hle
    omega
  rw [run_cofactor]
  exact ⟨he,hlo,hq⟩

/-- Restoring division's remainder stays within either supplied physical width,
including the all-zero-divisor fallback. -/
theorem remainder_width (input candidate : List Bool) (W : ℕ)
    (hi : input.length ≤ W) (hc : candidate.length ≤ W) :
    (divideBits input candidate).remainder.length ≤ W := by
  by_cases hp : 0 < bitValue candidate
  · rw [(divideBits_widths hp).1]
    exact hc
  · have hb : (nonzeroBits candidate).nonzero ≠ true := by
      intro hb
      exact hp ((nonzeroBits_correct candidate).mp hb)
    simp only [divideBits,ite_eq_right hb]
    exact hi

/-- Complete physical validation and cofactor recovery has a fixed quadratic
bound in the actual maximum supplied word width, not their decoded magnitudes. -/
theorem run_clock (input candidate : List Bool) (W : ℕ) (hW : 2 ≤ W)
    (hi : input.length ≤ W) (hc : candidate.length ≤ W) :
    (run input candidate).clock ≤ 100*(W+1)^2 := by
  have hl := orderWords_cost (left:=candidate) (right:=[false,true]) hc
    (by simpa only [List.length_cons,List.length_nil] using hW)
  have hu := orderWords_cost hc hi
  have hd := divideBits_cost input candidate
  have hr := nonzeroBits_cost (divideBits input candidate).remainder
  have hw := remainder_width input candidate W hi hc
  have hdb : input.length*(16*candidate.length+20)+7*candidate.length+4 ≤
      W*(16*W+20)+7*W+4 := by gcongr
  unfold run
  nlinarith

end RiemannGaussian.SemiprimeD1FactorValidationBits
