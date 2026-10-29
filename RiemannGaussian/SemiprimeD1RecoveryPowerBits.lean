/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RecoveryWeightRunState
import RiemannGaussian.SemiprimeRationalBits
import RiemannGaussian.SemiprimeJetBits

/-! # Physical rational-power lowering for the actual recovery producer
Every multiply is the existing executable signed Boolean/GCD/restoring-division
primitive. The original integer and rational-power endpoints derive all
intermediate capacities; they do not take a Fits sequence as an input.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeD1RecoveryPowerBits
open SemiprimeRationalBits SemiprimeJetBits
open SemiprimeD1RecoveryScalarRun SemiprimeD1WireKernelOriginal
open SemiprimeD1JetRecoveryGrid SemiprimeD1RecoveryWeightRunState

/-- Actual physical counterpart of the original right-recursive rational power. -/
def power (template : List Bool) (x : RationalWord) : ℕ → RationalReport
  | 0 => ⟨oneWord,3⟩
  | n+1 =>
    let old:=power template x n
    let out:=executeOperation .mul old.word x template
    ⟨out.word,old.clock+out.clock+4⟩

/-- Every actual output fits the physical template, including all earlier frames. -/
theorem power_width (template : List Bool) (x : RationalWord) (n : ℕ)
    (ht : 0 < template.length) : Width (power template x n).word template.length := by
  cases n with
  | zero => exact oneWord_width ht
  | succ n => exact ⟨(fitRationalBits_width _ _).1.le,(fitRationalBits_width _ _).2.le⟩

/-- Scalar-semantic induction for the actual physical loop. Capacity hypotheses
are discharged from original recovery bounds at the exported endpoints below. -/
theorem power_correct (template : List Bool) (x : RationalWord) (n : ℕ)
    (hx : x.Valid) (hfit : ∀k ≤ n,Fits (x.value^k) template.length) :
    (power template x n).word.value=x.value^n ∧ (power template x n).word.Valid := by
  induction n with
  | zero => exact ⟨by simp [power,oneWord_value],oneWord_valid⟩
  | succ n ih =>
    have old:=ih (fun k hk => hfit k (by omega))
    have cap : Fits (Operation.mul.value (power template x n).word.value x.value) template.length := by
      simpa only [Operation.value,old.1,pow_succ] using hfit (n+1) le_rfl
    have out:=executeOperation_correct .mul (power template x n).word x template old.2 hx cap
    exact ⟨out.1.trans (by simp only [Operation.value,old.1,pow_succ]),out.2.1⟩

/-- Actual physical multiplications, normalization/GCD, reads and padding are
all charged; no unit native rational-operation budget is used. -/
theorem power_clock (template : List Bool) (x : RationalWord) (n : ℕ)
    (ht : 0 < template.length) (hx : Width x template.length) :
    (power template x n).clock ≤ n*(20000*(template.length+1)^3+4)+3 := by
  induction n with
  | zero => simp [power]
  | succ n ih =>
    have old:=power_width template x n ht
    have out:=executeOperation_cost .mul (power template x n).word x template old hx le_rfl
    simp only [power]
    simp only [Nat.add_mul,Nat.one_mul]
    omega

/-- Integer powers have canonical numerator/denominator capacities from the
original signed factor bound, not an advised normalized result. -/
theorem integer_power_fits (a m k : ℕ) (x : ℤ) (hx : x.natAbs ≤ size a)
    (hk : k ≤ m) (W : ℕ) (hW : (a+1)*m+1 ≤ W) : Fits ((x:ℚ)^k) W := by
  have hp : (x^k).natAbs ≤ (size a)^m := by
    rw [Int.natAbs_pow]
    exact (Nat.pow_le_pow_left hx k).trans (Nat.pow_le_pow_right (by unfold size;positivity) hk)
  have he : (size a)^m=2^((a+1)*m) := by unfold size; rw [← pow_mul]
  rw [he] at hp
  have ht : 2^((a+1)*m) < 2^W := Nat.pow_lt_pow_right (by decide : 1 < (2:ℕ)) (by omega)
  have hi : 1 < 2^W := Nat.one_lt_two_pow (by omega)
  change (((x:ℚ)^k).num).natAbs < 2^W ∧ ((x:ℚ)^k).den < 2^W
  rw [← Int.cast_pow]
  simpa only [Rat.num_intCast,Rat.den_intCast] using And.intro (hp.trans_lt ht) hi

/-- Original signed-integer power lowering with ALL capacities derived from
original factor/grid and loop-index bounds. -/
theorem integer_correct (template : List Bool) (word : RationalWord)
    (a m n : ℕ) (x : ℤ) (hx : x.natAbs ≤ size a) (hn : n ≤ m)
    (hv : word.value=(x:ℚ)) (hvalid : word.Valid)
    (hW : (a+1)*m+1 ≤ template.length) :
    (power template word n).word.value=((intPower x n).value:ℚ) ∧
      (power template word n).word.Valid := by
  have h:=power_correct template word n hvalid (by
    intro k hk
    rw [hv]
    exact integer_power_fits a m k x hx (hk.trans hn) template.length hW)
  simpa only [hv,intPower_value,Int.cast_pow] using h

/-- Original rational argument powers derive ALL normalized prefix capacities
from the original common integer representation, not a Fits oracle. -/
theorem argument_power_fits (a h u : ℕ) (t : Fin (size a)) (k : ℕ)
    (hk : k ≤ nodeMultiplicity a h u t.val) (W : ℕ)
    (hW : (a+1)*nodeMultiplicity a h u t.val+1 ≤ W) :
    Fits ((SemiprimeD1WeightPrecision.argument a t.val)^k) W := by
  have hb:=rationalPower_bounds a h u t k hk
  rw [rationalPower_value] at hb
  have he : (size a)^nodeMultiplicity a h u t.val=2^((a+1)*nodeMultiplicity a h u t.val) := by
    unfold size; rw [← pow_mul]
  rw [he] at hb
  have ht : 2^((a+1)*nodeMultiplicity a h u t.val) < 2^W :=
    Nat.pow_lt_pow_right (by decide : 1 < (2:ℕ)) (by omega)
  exact ⟨hb.2.trans_lt ht,hb.1.trans_lt ht⟩

/-- Actual original argument power execution, refined to the FROZEN producer
and with every multiply/GCD/division on physical words. -/
theorem argument_correct (template : List Bool) (word : RationalWord)
    (a h u : ℕ) (t : Fin (size a)) (n : ℕ)
    (hn : n ≤ nodeMultiplicity a h u t.val)
    (hv : word.value=SemiprimeD1WeightPrecision.argument a t.val) (hvalid : word.Valid)
    (hW : (a+1)*nodeMultiplicity a h u t.val+1 ≤ template.length) :
    (power template word n).word.value=
      (rationalPower (SemiprimeD1WeightPrecision.argument a t.val) n).value ∧
      (power template word n).word.Valid := by
  have h:=power_correct template word n hvalid (by
    intro k hk
    rw [hv]
    exact argument_power_fits a h u t k (hk.trans hn) template.length hW)
  simpa only [hv,rationalPower_value] using h

end RiemannGaussian.SemiprimeD1RecoveryPowerBits
