/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszShiftedZeroModes

/-!
# Ordinary-prime shifted legs with genuine global negative zero modes

Both proper-prime-power terms are paid independently. The result concerns
complete individual legs, not their hard-share-masked products.
-/

namespace RiemannGaussian.ZetaRieszShiftedCenter
noncomputable section
open Complex Filter Set Topology
open scoped BigOperators Classical

/-- Both proper-prime-power contributions, with the exact shifted scale. -/
def properLeg (u y : ℝ) (n : ℕ) : ℂ :=
  (u : ℂ)^(n+1)*zetaProperPrimePowerMoment n (center y)-
    ((u : ℂ)*ratio y)^(n+1)*zetaProperPrimePowerMoment n (center y+1)

theorem completeLeg_eq_full_sub_proper (u y : ℝ) (n : ℕ) :
    completeLeg u y (n+1) = fullLeg u y n-properLeg u y n := by
  rw [completeLeg_succ, fullLeg, properLeg,
    zetaPrimeLogMoment_eq_prime_add_proper n (by norm_num [center]),
    zetaPrimeLogMoment_eq_prime_add_proper n (by norm_num [center])]
  rw [mul_pow]
  ring

private theorem scaled_proper_bound (n : ℕ) {a s : ℂ} (ha : ‖a‖ ≤ 9/16)
    (hs : (5/4 : ℝ) < s.re) :
    ‖a^(n+1)*zetaProperPrimePowerMoment n s‖ ≤
      zetaProperPrimePowerExpMass (s.re-3/4)*(3/4 : ℝ)^n := by
  have h := norm_tsum_mul_zetaPrimeLogKernel_le _ zetaProperPrimePowerCoefficient_nonneg
    n s (by norm_num : (0 : ℝ) < 3/4)
    (summable_zetaProperPrimePowerExpMass (by linarith : (1/2 : ℝ) < s.re-3/4))
  change ‖zetaProperPrimePowerMoment n s‖ ≤
    (3/4 : ℝ)⁻¹^n*zetaProperPrimePowerExpMass (s.re-3/4) at h
  have hmass := zetaProperPrimePowerExpMass_nonneg (s.re-3/4)
  rw [norm_mul, norm_pow]
  calc
    _ ≤ ‖a‖^(n+1)*((3/4 : ℝ)⁻¹^n*zetaProperPrimePowerExpMass (s.re-3/4)) := by
      gcongr
    _ = zetaProperPrimePowerExpMass (s.re-3/4)*‖a‖*(‖a‖*(4/3 : ℝ))^n := by
      rw [pow_succ, mul_pow]
      norm_num
      ring
    _ ≤ zetaProperPrimePowerExpMass (s.re-3/4)*1*(3/4 : ℝ)^n := by
      gcongr
      · linarith
      · linarith
    _ = _ := by ring

theorem properLeg_geometric {u y : ℝ} (hu0 : 0 ≤ u)
    (hu : u ≤ 10001/20000) (hy : 54 < |y|) (n : ℕ) :
    ‖properLeg u y n‖ ≤
      (zetaProperPrimePowerExpMass (3/4)+zetaProperPrimePowerExpMass (7/4))*(3/4 : ℝ)^n := by
  have huN : ‖(u : ℂ)‖ ≤ 9/16 := by
    rw [Complex.norm_real, Real.norm_of_nonneg hu0]
    linarith
  have hucN : ‖(u : ℂ)*ratio y‖ ≤ 9/16 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hu0]
    have hc := norm_ratio_lt hy
    nlinarith [mul_nonneg (sub_nonneg.mpr hu) (norm_nonneg (ratio y))]
  have hA := scaled_proper_bound n (s := center y) huN (by norm_num [center])
  have hB := scaled_proper_bound n (s := center y+1) hucN (by norm_num [center])
  have h := norm_sub_le_of_le hA hB
  convert h using 1 <;> norm_num [properLeg, center]
  ring

/-- The requested complete ordinary-prime leg expansion: every actual
zero has negative residue, and the remaining error is geometrically small.
No exposure, simplicity or rightmost-zero hypothesis is needed here. -/
theorem completeLeg_global_error_bound {u y : ℝ} (hu0 : 0 ≤ u)
    (hu : u ≤ 10001/20000) (hy : 54 < |y|) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, 0 < n →
      ‖completeLeg u y (n+1)-(∑' rho : NontrivialZetaZero,
        -(analyticZetaZeroMultiplicity rho : ℂ)*((u : ℂ)/(center y-rho.1))^(n+1))‖ ≤
          M*(3/4 : ℝ)^n := by
  obtain ⟨M, hM, hb⟩ := fullLeg_global_error_bound hu0 hu hy
  let P := zetaProperPrimePowerExpMass (3/4)+zetaProperPrimePowerExpMass (7/4)
  have hP : 0 ≤ P := add_nonneg (zetaProperPrimePowerExpMass_nonneg _)
    (zetaProperPrimePowerExpMass_nonneg _)
  refine ⟨M+P, add_nonneg hM hP, fun n hn => ?_⟩
  rw [completeLeg_eq_full_sub_proper, sub_right_comm]
  apply (norm_sub_le_of_le (hb n hn) (properLeg_geometric hu0 hu hy n)).trans
  calc
    _ ≤ M*(3/4 : ℝ)^n+P*(3/4 : ℝ)^n := by
      exact add_le_add (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2/3)
          (by norm_num : (2/3 : ℝ) ≤ 3/4) n) hM) le_rfl
    _ = _ := by ring

theorem selected_zero_mode (rho : NontrivialZetaZero) (n : ℕ) :
    let u := (3/2 : ℝ)-rho.1.re;
    -(analyticZetaZeroMultiplicity rho : ℂ)*
      ((u : ℂ)/(center rho.1.im-rho.1))^(n+1) = -(analyticZetaZeroMultiplicity rho : ℂ) := by
  dsimp only
  have hu : (0 : ℝ) < 3/2-rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have he : center rho.1.im-rho.1 = ((3/2-rho.1.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [center]
  rw [he, div_self (Complex.ofReal_ne_zero.mpr hu.ne'), one_pow, mul_one]

end
end RiemannGaussian.ZetaRieszShiftedCenter
