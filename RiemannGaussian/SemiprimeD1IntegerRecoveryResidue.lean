/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1IntegerRecoveryHeight

/-! # Explicit dyadic cancellation of the actual integer recovery accumulator
The native path strips the common denominator's actual2-adic content and takes
one odd-unit inverse. No rational-to-modular map or requested residue is supplied.
Native integer division/valuation/ZMod inverse are not yet physical bit programs.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1IntegerRecoveryResidue
open SemiprimeD1IntegerRecovery SemiprimeD1DyadicBounds
  SemiprimeD1RecoveryResidue SemiprimeD1CrossingCoefficient
  SemiprimeD1CrossingResidue SemiprimeD1JetRecoveryPrecision

/-- The actual dyadic content of the acquired positive common denominator. -/
def content (D : ℕ) : ℕ := 2^padicValNat 2 D

/-- Explicit integer cancellation before the one odd-unit inverse. -/
def stripped (N : ℤ) (D : ℕ) : Coefficient :=
  ⟨N/(content D:ℤ),(D/content D:ℕ)⟩

/-- Actual native modular output from the integer common-denominator accumulator. -/
def finish (p : ℕ) (r : Result) : ZMod (2^p) :=
  residue p (stripped r.numerator r.denominator)

/-- Dyadic content is a genuine positive divisor of the actual denominator. -/
theorem content_pos_dvd (D : ℕ) : 0<content D ∧ content D∣D :=
  ⟨by unfold content;positivity,pow_padicValNat_dvd⟩

/-- Stripping maximal content DERIVES oddness of the actual remaining denominator. -/
theorem stripped_odd (N : ℤ) (D : ℕ) (hD : 0<D) : Odd (stripped N D).denominator := by
  have hp := content_pos_dvd D
  have hq : 0<D/content D := Nat.div_pos (Nat.le_of_dvd hD hp.2) hp.1
  have hv : padicValNat 2 (D/content D)=0 := by
    simpa only [content,Nat.sub_self] using (padicValNat.div_pow (p:=2) (a:=padicValNat 2 D) hp.2)
  have hn : ¬2∣D/content D := by
    rcases padicValNat.eq_zero_iff.mp hv with h|h|h
    · norm_num at h
    · omega
    · exact h
  change Odd ((D/content D:ℕ):ℤ)
  exact_mod_cast (Nat.not_even_iff_odd.mp (by simpa only [even_iff_two_dvd] using hn))

/-- Integral-at2 actual fractions have enough numerator content for exact division. -/
theorem content_dvd_numerator (N : ℤ) (D : ℕ) (hD : 0<D)
    (hi : AtLeast 0 ((N:ℚ)/(D:ℚ))) : (content D:ℤ)∣N := by
  by_cases hN : N=0
  · simp [hN]
  have hNq : (N:ℚ)≠0 := by exact_mod_cast hN
  have hDq : (D:ℚ)≠0 := by positivity
  have hv := hi.resolve_left (div_ne_zero hNq hDq)
  rw [padicValRat.div hNq hDq,padicValRat.of_int,padicValRat.of_nat] at hv
  change (2:ℤ)^padicValNat 2 D∣N
  exact (padicValInt_dvd_iff (p:=2) _ _).mpr (Or.inr (by omega))

/-- The explicit cancelled integer fraction retains the EXACT scalar value. -/
theorem stripped_value (N : ℤ) (D : ℕ) (hD : 0<D)
    (hi : AtLeast 0 ((N:ℚ)/(D:ℚ))) :
    value (stripped N D)=(N:ℚ)/(D:ℚ) := by
  have hN := content_dvd_numerator N D hD hi
  have hp := content_pos_dvd D
  have hP : (content D:ℚ)≠0 := by exact_mod_cast (ne_of_gt hp.1)
  have hDq : (D:ℚ)≠0 := by positivity
  simp only [stripped,value,Int.cast_natCast,Int.cast_div_charZero hN,Nat.cast_div_charZero hp.2]
  field_simp

/-- Explicit integer cancellation and unit inversion equals canonical native reduction. -/
theorem finish_eq_reduce (p : ℕ) (r : Result) (hD : 0<r.denominator)
    (hi : AtLeast 0 ((r.numerator:ℚ)/(r.denominator:ℚ))) :
    finish p r=SemiprimeD1RecoveryResidue.reduce p ((r.numerator:ℚ)/(r.denominator:ℚ)) := by
  exact residue_eq_of_value_eq p _ _ (stripped_odd _ _ hD)
    (by change Odd (((r.numerator:ℚ)/(r.denominator:ℚ)).den:ℤ)
        exact_mod_cast denominator_odd _ hi)
    (by rw [stripped_value _ _ hD hi,canonicalFraction_value])

/-- The ACTUAL original child-word path gives precisely the frozen recovery residue.
Only integral recovery is an internal mathematical contract here; original D.5
representative precision derives it through the existing recover_integral theorem. -/
theorem run_finish (a M u p : ℕ) (children : ℕ → Array (List Bool))
    (hi : AtLeast 0 (recover a M u (decodedPackets children))) :
    finish p (run a M u children)=
      SemiprimeD1RecoveryResidue.reduce p (recover a M u (decodedPackets children)) := by
  have hD : 0<(run a M u children).denominator := by
    simpa only [run,denominatorRun_value] using denominator_pos (terms a M u children)
  have hv := run_recover a M u children
  rw [← hv] at hi
  rw [finish_eq_reduce p _ hD hi,hv]

/-- Original child-precision contracts derive integrality and exact parent residue;
no integrality, weight, inverse, or requested output answer is supplied. -/
theorem original_run_modulo (a M u p : ℕ) (hu : 0<u) (hM : u≤M) (H : Polynomial ℚ)
    (hH : H.natDegree≤M*(2*(2^a)-1)) (children : ℕ → Array (List Bool))
    (h0 : AtLeast 0 (H.eval 0))
    (herr : ∀t∈SemiprimeD1HermiteNodes.active a (SemiprimeD1TaperedLoss.height M u) u,
      ∀j<SemiprimeD1JetRecoveryGrid.nodeMultiplicity a (SemiprimeD1TaperedLoss.height M u) u t,
      AtLeast (SemiprimeD1WeightPrecision.precision a M u p t:ℤ)
        (SemiprimeJetArray.coefficient (decodedPackets children t) j-
          (H.comp (SemiprimeD1ScaledHermite.affine (SemiprimeD1HermiteOriginal.alpha a)
            (SemiprimeD1HermiteNodes.node a t))).coeff j)) :
    finish p (run a M u children)=SemiprimeD1RecoveryResidue.reduce p (H.eval 0) := by
  rw [run_finish a M u p children
    (recover_integral a M u p hu hM H hH (decodedPackets children) h0 herr)]
  exact original_recover_modulo a M u p hu hM H hH (decodedPackets children) h0 herr

end RiemannGaussian.SemiprimeD1IntegerRecoveryResidue
