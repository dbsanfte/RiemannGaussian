/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1DyadicInteger
import RiemannGaussian.SemiprimeBitArithmetic

/-! # Exact kernel of the legitimate dyadic reduction map
Actual child residue equality derives the scalar D.5 error contract. The kernel
proof uses actual canonical odd denominators, not a rational-to-modular map.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1DyadicCongruence
open SemiprimeD1DyadicBounds SemiprimeD1DyadicInteger SemiprimeD1RecoveryResidue
  SemiprimeD1CrossingCoefficient SemiprimeD1CrossingResidue

/-- The kernel of actual restricted reduction is EXACTLY the required dyadic precision. -/
theorem reduce_zero_iff (p : ℕ) (q : ℚ) (hq : AtLeast 0 q) :
    reduce p q=0 ↔ AtLeast (p:ℤ) q := by
  refine ⟨?_,reduce_error_zero p q⟩
  intro hz
  by_cases hqz : q=0
  · rw [hqz]
    exact zero _
  have hodd := denominator_odd q hq
  have hnot : ¬2∣q.den := by
    simpa only [← even_iff_two_dvd] using Nat.not_even_iff_odd.mpr hodd
  have hvden : padicValNat 2 q.den=0 := padicValNat.eq_zero_of_not_dvd hnot
  have ho : Odd (canonicalFraction q).denominator := by
    change Odd ((q.den:ℕ):ℤ)
    exact_mod_cast hodd
  have he := residue_denominator p (canonicalFraction q) ho
  have he' : (q.den:ZMod (2^p))*reduce p q=(q.num:ZMod (2^p)) := by
    simpa only [reduce,canonicalFraction,Int.cast_natCast] using he
  rw [hz,mul_zero] at he'
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd q.num (2^p)).mp he'.symm
  have hd' : (2:ℤ)^p∣q.num := by exact_mod_cast hd
  have hv := (padicValInt_dvd_iff (p:=2) p q.num).mp hd'
  have hvn := hv.resolve_left (Rat.num_ne_zero.mpr hqz)
  right
  simp only [padicValRat,hvden,Nat.cast_zero,sub_zero]
  exact_mod_cast hvn

/-- Integral rationals have the same actual residue IFF their difference has full precision. -/
theorem reduce_eq_iff (p : ℕ) (q r : ℚ) (hq : AtLeast 0 q) (hr : AtLeast 0 r) :
    reduce p q=reduce p r ↔ AtLeast (p:ℤ) (q-r) := by
  have hs : AtLeast 0 (q-r) := by simpa only [sub_eq_add_neg] using add hq (neg hr)
  have he := map_sub (reduction p) (⟨q,hq⟩:integers) (⟨r,hr⟩:integers)
  change reduce p (q-r)=reduce p q-reduce p r at he
  rw [← sub_eq_zero,← he]
  exact reduce_zero_iff p (q-r) hs

/-- Actual canonical child word equality DERIVES the retained D.5 representative error. -/
theorem child_word_error (p : ℕ) (q : ℚ) (hq : AtLeast 0 q) (bs : List Bool)
    (hchild : reduce p q=(SemiprimeBitArithmetic.bitValue bs:ZMod (2^p))) :
    AtLeast (p:ℤ) ((SemiprimeBitArithmetic.bitValue bs:ℚ)-q) := by
  have hi : AtLeast 0 (SemiprimeBitArithmetic.bitValue bs:ℚ) := by
    simpa only [Int.cast_natCast] using integer (SemiprimeBitArithmetic.bitValue bs:ℤ)
  have he : reduce p (SemiprimeBitArithmetic.bitValue bs:ℚ)=
      (SemiprimeBitArithmetic.bitValue bs:ZMod (2^p)) := by
    simpa only [Int.cast_natCast] using reduce_integer p (SemiprimeBitArithmetic.bitValue bs:ℤ)
  exact (reduce_eq_iff p _ q hi hq).mp (he.trans hchild.symm)

/-- The explicit integral source needs no supplied integrality proof at the child seam. -/
theorem source_word_error (p : ℕ) (q : integers) (bs : List Bool)
    (hchild : reduction p q=(SemiprimeBitArithmetic.bitValue bs:ZMod (2^p))) :
    AtLeast (p:ℤ) ((SemiprimeBitArithmetic.bitValue bs:ℚ)-q.val) :=
  child_word_error p q.val q.property bs hchild

end RiemannGaussian.SemiprimeD1DyadicCongruence
