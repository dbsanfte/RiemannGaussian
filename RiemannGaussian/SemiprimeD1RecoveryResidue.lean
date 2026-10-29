/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1JetRecoveryPrecision
import RiemannGaussian.SemiprimeD1CrossingModulo

/-! # Actual canonical rational cancellation after D.5 recovery
Integrality DERIVES oddness of the actual canonical denominator. Reduction uses
actual canonical numerator/denominator and native ZMod extended-gcd inversion.
This is not yet Boolean-word execution or an attached primitive-bit clock.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1RecoveryResidue
open scoped BigOperators
open Polynomial SemiprimeD1DyadicBounds SemiprimeD1JetRecoveryPrecision
  SemiprimeD1WeightPrecision SemiprimeD1WireKernelOriginal
  SemiprimeD1TaperedLoss SemiprimeD1JetRecoveryGrid SemiprimeD1JetRecoveryWeights
  SemiprimeD1HermiteNodes SemiprimeD1HermiteOriginal SemiprimeJetArray
  SemiprimeD1CrossingCoefficient SemiprimeD1CrossingResidue SemiprimeD1CrossingModulo

/-- Integrality forces the ACTUAL reduced rational denominator to be odd. -/
theorem denominator_odd (q : ℚ) (hq : AtLeast 0 q) : Odd q.den := by
  rcases hq with hq0|hv
  · simp only [hq0,Rat.den_zero]
    exact odd_one
  apply Nat.not_even_iff_odd.mp
  rw [even_iff_two_dvd]
  intro hd
  have hden : 0<padicValNat 2 q.den := by
    by_contra h
    have hz : padicValNat 2 q.den=0 := by omega
    rcases padicValNat.eq_zero_iff.mp hz with h1|h0|hnot
    · norm_num at h1
    · exact q.den_nz h0
    · exact hnot hd
  have hnum : padicValNat 2 q.num.natAbs≠0 := by
    unfold padicValRat padicValInt at hv
    omega
  have hn : 2∣q.num.natAbs := padicValNat.dvd_of_ne_zero hnum
  have hg := Nat.dvd_gcd hn hd
  rw [q.reduced.gcd_eq_one] at hg
  norm_num at hg

/-- Actual canonical fraction data, not a requested residue/coefficient answer. -/
def canonicalFraction (q : ℚ) : Coefficient := ⟨q.num,(q.den:ℤ)⟩

/-- Canonical numerator and denominator reconstruct the original rational exactly. -/
theorem canonicalFraction_value (q : ℚ) : value (canonicalFraction q)=q := by
  simpa only [value,canonicalFraction,Int.cast_natCast] using Rat.num_div_den q

/-- Actual native modular reduction after rational normalization/cancellation. -/
def reduce (p : ℕ) (q : ℚ) : ZMod (2^p) := residue p (canonicalFraction q)

/-- The native inverse operates on a DERIVED odd canonical denominator. -/
theorem reduce_unit (p : ℕ) (q : ℚ) (hq : AtLeast 0 q) :
    IsUnit ((q.den:ℤ):ZMod (2^p)) :=
  odd_unit _ (by exact_mod_cast denominator_odd q hq) p

/-- A true parent-precision error reduces to zero under actual native cancellation. -/
theorem reduce_error_zero (p : ℕ) (q : ℚ) (hq : AtLeast (p:ℤ) q) : reduce p q=0 := by
  by_cases hq0 : q=0
  · simp [reduce,canonicalFraction,residue,hq0]
  have hqi : AtLeast 0 q := mono hq (by positivity)
  have hd := denominator_odd q hqi
  have hnot : ¬2∣q.den := by rw [← even_iff_two_dvd];exact Nat.not_even_iff_odd.mpr hd
  have hvden : padicValNat 2 q.den=0 := padicValNat.eq_zero_of_not_dvd hnot
  have hv : (p:ℤ)≤(padicValInt 2 q.num:ℤ) := by
    have he := hq.resolve_left hq0
    simpa only [padicValRat,hvden,Nat.cast_zero,sub_zero] using he
  have hdiv : (2:ℤ)^p∣q.num := (padicValInt_dvd_iff (p:=2) _ _).mpr (Or.inr (by exact_mod_cast hv))
  exact residue_zero p (canonicalFraction q) hdiv

/-- Congruent integral rationals have the SAME actual canonical unit-inverse residue. -/
theorem reduce_congruent (p : ℕ) (q r : ℚ) (hr : AtLeast 0 r)
    (herr : AtLeast (p:ℤ) (q-r)) : reduce p q=reduce p r := by
  have he0 := mono herr (show (0:ℤ)≤p by positivity)
  have hq : AtLeast 0 q := by simpa only [sub_add_cancel] using add he0 hr
  have heodd : Odd (canonicalFraction (q-r)).denominator := by
    change Odd ((q-r).den:ℤ)
    exact_mod_cast denominator_odd (q-r) he0
  have hrodd : Odd (canonicalFraction r).denominator := by
    change Odd (r.den:ℤ)
    exact_mod_cast denominator_odd r hr
  have hqodd : Odd (canonicalFraction q).denominator := by
    change Odd (q.den:ℤ)
    exact_mod_cast denominator_odd q hq
  have heq : value (canonicalFraction q)=
      value (fractionAdd (canonicalFraction (q-r)) (canonicalFraction r)) := by
    rw [fractionAdd_value _ _ heodd hrodd,canonicalFraction_value,canonicalFraction_value,canonicalFraction_value]
    ring
  have he := residue_eq_of_value_eq p (canonicalFraction q)
    (fractionAdd (canonicalFraction (q-r)) (canonicalFraction r)) hqodd (heodd.mul hrodd) heq
  rw [fractionAdd_residue p _ _ heodd hrodd] at he
  change reduce p q=reduce p (q-r)+reduce p r at he
  rw [reduce_error_zero p (q-r) herr,zero_add] at he
  exact he

/-- Original integer final values reduce to their usual original modular encoding. -/
theorem reduce_integer (p : ℕ) (z : ℤ) : reduce p (z:ℚ)=(z:ZMod (2^p)) := by
  simp [reduce,canonicalFraction,residue]

/-- ACTUAL native D.5 recovered residues agree at parent precision, from original
weights/taper/grid and only retained CHILD jet residue errors. -/
theorem original_recover_modulo (a M u p : ℕ) (hu : 0<u) (hM : u≤M) (H : ℚ[X])
    (hH : H.natDegree≤M*(2*(2^a)-1)) (packets : ℕ→Array ℚ) (h0 : AtLeast 0 (H.eval 0))
    (herr : ∀t∈active a (height M u) u,∀j<nodeMultiplicity a (height M u) u t,
      AtLeast (precision a M u p t:ℤ)
        (coefficient (packets t) j-
          (H.comp (SemiprimeD1ScaledHermite.affine (alpha a) (node a t))).coeff j)) :
    reduce p (recover a M u packets)=reduce p (H.eval 0) :=
  reduce_congruent p _ _ h0 (recover_error a M u p hu hM H hH packets herr)

end RiemannGaussian.SemiprimeD1RecoveryResidue
