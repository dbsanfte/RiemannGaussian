/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPhaseExactZeroBound
import RiemannGaussian.ZetaPhasePrimeRecurrence

/-!
# The exact phase contacts cannot persist from a prime to its square

Doubling an angle sends its cosine through `x ↦ 2*x^2-1`. The four
contacts of the exact optimizer are separated from their doubled images.
Consequently the kernel at an angle and at its double has a uniform
positive sum. This geometric obstruction supplies arithmetic work from
the linked phases of a prime and its square, before any zero hypothesis.

The resulting positive reserve strengthens the existing local zero
budget. It does not bound the different signed moment carrier for RH.
-/

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian

noncomputable section

private theorem root_close (j : Fin 4) :
    |phaseContactExactRoot (phaseContactCosineCoordinate j) -
      phaseContactRootCenter (phaseContactCosineCoordinate j)| ≤ (1 / 10 ^ 30 : ℝ) :=
  (norm_le_pi_norm (phaseContactExactRoot - phaseContactRootCenter)
    (phaseContactCosineCoordinate j)).trans phaseContactExactRoot_dist_le

private theorem center_mem (j : Fin 4) :
    |phaseContactRootCenter (phaseContactCosineCoordinate j)| ≤ 1 := by
  fin_cases j <;> norm_num [phaseContactRootCenter, phaseContactRootCenterQ,
    phaseContactCosineCoordinate]

private theorem center_gap (i j : Fin 4) :
    (1 / 20 : ℝ) + 37 / 10 ^ 30 ≤
      |(2 * phaseContactRootCenter (phaseContactCosineCoordinate i) ^ 2 - 1) -
        phaseContactRootCenter (phaseContactCosineCoordinate j)| := by
  fin_cases i <;> fin_cases j <;>
    norm_num [phaseContactRootCenter, phaseContactRootCenterQ, phaseContactCosineCoordinate]

/-- Every doubled contact is separated from every original contact by
an exact rational gap in the cosine coordinate. -/
theorem phaseContactExact_doubled_contact_gap (i j : Fin 4) :
    (1 / 20 : ℝ) ≤
      |(2 * phaseContactExactRoot (phaseContactCosineCoordinate i) ^ 2 - 1) -
        phaseContactExactRoot (phaseContactCosineCoordinate j)| := by
  have h := abs_phaseChebyshevValue_sub_le 2
    (abs_phaseContactExactRoot_cosine_lt_one i).le (center_mem i)
  norm_num [phaseChebyshevValue, Polynomial.Chebyshev.T_two] at h
  have hi : |(2 * phaseContactExactRoot (phaseContactCosineCoordinate i) ^ 2 - 1) -
      (2 * phaseContactRootCenter (phaseContactCosineCoordinate i) ^ 2 - 1)| ≤
        (36 / 10 ^ 30 : ℝ) := by
    convert h.trans (mul_le_mul_of_nonneg_left (root_close i)
      (by norm_num : (0 : ℝ) ≤ 36)) using 1 <;> congr 1 <;> ring
  have hj := root_close j
  have hg := center_gap i j
  have ht := abs_sub_le
    (2 * phaseContactRootCenter (phaseContactCosineCoordinate i) ^ 2 - 1)
    (2 * phaseContactExactRoot (phaseContactCosineCoordinate i) ^ 2 - 1)
    (phaseContactRootCenter (phaseContactCosineCoordinate j))
  have ht' := abs_sub_le
    (2 * phaseContactExactRoot (phaseContactCosineCoordinate i) ^ 2 - 1)
    (phaseContactExactRoot (phaseContactCosineCoordinate j))
    (phaseContactRootCenter (phaseContactCosineCoordinate j))
  rw [abs_sub_comm (2 * phaseContactRootCenter (phaseContactCosineCoordinate i) ^ 2 - 1)
    (2 * phaseContactExactRoot (phaseContactCosineCoordinate i) ^ 2 - 1)] at ht
  linarith

private theorem double_mem {x : ℝ} (hx : |x| ≤ 1) : |2 * x ^ 2 - 1| ≤ 1 := by
  have hsq : x ^ 2 ≤ 1 := by
    have h := mul_self_le_mul_self (abs_nonneg x) hx
    nlinarith [sq_abs x]
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg x]

private theorem kernel_nonneg {x : ℝ} (hx : |x| ≤ 1) : 0 ≤ phaseContactExactKernel x :=
  phaseContactExactKernel_nonneg_of_quotient (phaseContactExactQuotient_pos hx).le

/-- A contact at an angle forces a noncontact at its double. Thus the
two complete kernel values always have a strictly positive sum. -/
theorem phaseContactExactKernel_add_double_pos {x : ℝ} (hx : |x| ≤ 1) :
    0 < phaseContactExactKernel x + phaseContactExactKernel (2 * x ^ 2 - 1) := by
  have h0 := kernel_nonneg hx
  have h1 := kernel_nonneg (double_mem hx)
  by_contra h
  have hx0 : phaseContactExactKernel x = 0 := by linarith
  have hx1 : phaseContactExactKernel (2 * x ^ 2 - 1) = 0 := by linarith
  obtain ⟨i, hi⟩ := (phaseContactExactKernel_eq_zero_iff hx).mp hx0
  obtain ⟨j, hj⟩ := (phaseContactExactKernel_eq_zero_iff (double_mem hx)).mp hx1
  have hg := phaseContactExact_doubled_contact_gap i j
  rw [← hi, hj, sub_self, abs_zero] at hg
  norm_num at hg

/-- Compactness upgrades contact avoidance to one positive floor for
all angles. The full exact optimizer is used, including its tiny modes. -/
theorem exists_phaseContactExact_doubling_floor :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ,
      c ≤ phaseContactKernel phaseContactExactFamily t +
        phaseContactKernel phaseContactExactFamily (2 * t) := by
  let f (x : ℝ) := phaseContactExactKernel x + phaseContactExactKernel (2 * x ^ 2 - 1)
  have hc : Continuous phaseContactExactKernel := by
    have he : phaseContactExactKernel = fun x ↦ phaseContactExactPolynomial.eval x := by
      funext x
      exact (phaseContactExactPolynomial_eval x).symm
    rw [he]
    exact phaseContactExactPolynomial.continuous
  have hf : Continuous f := hc.add (hc.comp (by fun_prop))
  obtain ⟨x, hx, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Set.Icc (-1 : ℝ) 1).Nonempty from ⟨0, by norm_num⟩) hf.continuousOn
  refine ⟨f x, phaseContactExactKernel_add_double_pos (abs_le.mpr hx), ?_⟩
  intro t
  have h := hmin (show Real.cos t ∈ Set.Icc (-1 : ℝ) 1 from abs_le.mp (Real.abs_cos_le_one t))
  change f x ≤ f (Real.cos t) at h
  simpa only [f, phaseContactExactFamily_kernel, Real.cos_two_mul] using h

/-- A doubling floor for any nonnegative phase kernel forces arithmetic
work from a prime and its square. This comparison precedes every zero
hypothesis and applies to arbitrary summable real-frequency families. -/
theorem zetaPhase_prime_square_floor {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hs : Summable a) (hP : ∀ t, 0 ≤ zetaPhaseKernel a ω t) {c : ℝ}
    (hc : ∀ t, c ≤ zetaPhaseKernel a ω t + zetaPhaseKernel a ω (2 * t))
    {σ : ℝ} (hσ : 1 < σ) {p : ℕ} (hp : p.Prime) (y : ℝ) :
    c * zetaPhasePrimeBlockWeight σ p 2 ≤
      ∑' m : ℕ, zetaPhasePrimeWeight σ m * zetaPhaseKernel a ω (y * Real.log m) := by
  have hpne : p ≠ p ^ 2 := by nlinarith [hp.two_le]
  have hf := zetaPhase_finite_primeWork_le ha hs hP hσ y {p, p ^ 2}
  rw [Finset.sum_pair hpne] at hf
  have hangle : y * Real.log (p ^ 2 : ℕ) = 2 * (y * Real.log p) := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
    ring
  have hweight : zetaPhasePrimeWeight σ (p ^ 2) = zetaPhasePrimeBlockWeight σ p 2 := by
    rw [zetaPhasePrimeWeight, ArithmeticFunction.vonMangoldt_apply_pow (by norm_num : 2 ≠ 0),
      ArithmeticFunction.vonMangoldt_apply_prime hp, Nat.cast_pow, Real.log_pow]
    unfold zetaPhasePrimeBlockWeight
    simp only [Nat.cast_ofNat]
    rw [show -σ * (2 * Real.log p) = -σ * 2 * Real.log p by ring]
  have hw := zetaPhasePrimeBlockWeight_le (by linarith : 0 ≤ σ) hp
    (by norm_num : 1 ≤ 1) (by norm_num : 1 ≤ 2)
  rw [pow_one] at hw
  rw [hangle, hweight] at hf
  have hfirst := mul_le_mul_of_nonneg_right hw (hP (y * Real.log p))
  have hpair := mul_le_mul_of_nonneg_right (hc (y * Real.log p))
    (zetaPhasePrimeBlockWeight_pos σ hp 2).le
  nlinarith

private theorem exact_summable : Summable phaseContactExactFamily :=
  summable_of_phaseContactBudget phaseContactExactFamily_nonneg
    phaseContactExactFamily_hasSum_budget.summable

/-- The exact optimizer has a uniform prime-square reserve at every
height and every prime. The constant depends only on its proved contact
geometry, not on an unknown zero or an arithmetic cancellation premise. -/
theorem exists_phaseContactExact_prime_square_floor :
    ∃ c : ℝ, 0 < c ∧ ∀ (σ : ℝ), 1 < σ → ∀ (p : ℕ), p.Prime → ∀ y : ℝ,
      c * zetaPhasePrimeBlockWeight σ p 2 ≤
        ∑' m : ℕ, zetaPhasePrimeWeight σ m *
          phaseContactKernel phaseContactExactFamily (y * Real.log m) := by
  obtain ⟨c, hc, hfloor⟩ := exists_phaseContactExact_doubling_floor
  refine ⟨c, hc, fun σ hσ p hp y ↦ ?_⟩
  exact zetaPhase_prime_square_floor (ω := fun n ↦ (n : ℝ))
    phaseContactExactFamily_nonneg exact_summable phaseContactExactFamily_kernel_nonneg
    hfloor hσ hp y

/-- Actual zeros near the right edge must pay one additional uniform
positive arithmetic reserve. The exact efficiency, multiplicity and true
height cost are retained. This strengthens the local budget without
assuming a bound for the signed RH moment carrier. -/
theorem exists_phaseContactExact_positive_zero_budget_reserve :
    ∃ b : ℝ, 0 < b ∧ ∀ rho : NontrivialZetaZero, 15 / 16 ≤ rho.1.re →
      phaseContactExactRoot 8 + (4 / 17 : ℝ) * phaseContactExactFamily 1 *
          ((analyticZetaZeroMultiplicity rho : ℝ) - 1) + b * (1 - rho.1.re) ≤
        448 * (1 - rho.1.re) * (∑' n : ℕ,
          phaseContactExactFamily n * localZetaLogHeight ((n : ℝ) * rho.1.im)) +
          (13 / 4 : ℝ) * phaseOscillatoryMass phaseContactExactFamily *
            (1 - rho.1.re) ^ 2 / rho.1.im ^ 2 := by
  obtain ⟨c, hc, hfloor⟩ := exists_phaseContactExact_prime_square_floor
  refine ⟨c * zetaPhasePrimeBlockWeight (5 / 4) 2 2,
    mul_pos hc (zetaPhasePrimeBlockWeight_pos _ Nat.prime_two _), ?_⟩
  intro rho hrho
  have hd : 0 < 1 - rho.1.re := sub_pos.mpr (NontrivialZetaZero.re_lt_one rho)
  have hσ : 1 < 1 + (13 / 4 : ℝ) * (1 - rho.1.re) := by linarith
  have hσle : 1 + (13 / 4 : ℝ) * (1 - rho.1.re) ≤ 5 / 4 := by linarith
  have hw : zetaPhasePrimeBlockWeight (5 / 4) 2 2 ≤
      zetaPhasePrimeBlockWeight (1 + (13 / 4 : ℝ) * (1 - rho.1.re)) 2 2 := by
    unfold zetaPhasePrimeBlockWeight
    apply mul_le_mul_of_nonneg_left _ (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right hσle
      (show 0 ≤ (2 : ℝ) * Real.log 2 by positivity)
    norm_num at h ⊢
    nlinarith
  have hf := (mul_le_mul_of_nonneg_left hw hc.le).trans
    (hfloor _ hσ 2 Nat.prime_two rho.1.im)
  have hmul := mul_le_mul_of_nonneg_left hf hd.le
  have h := phaseContactExact_source_add_primeWork_le rho hrho
  nlinarith

/-- The same positive reserve survives the proved explicit height and
pole allowances. Every coefficient and feasibility condition is discharged
for the exact optimizer. -/
theorem exists_phaseContactExact_refined_zero_source :
    ∃ b : ℝ, 0 < b ∧ ∀ rho : NontrivialZetaZero, 15 / 16 ≤ rho.1.re →
      (11 / 625 : ℝ) + b * (1 - rho.1.re) ≤
        448 * (1 - rho.1.re) * ((61 / 100 : ℝ) * localZetaLogHeight rho.1.im + 83 / 100) +
          (793 / 400 : ℝ) * (1 - rho.1.re) ^ 2 / rho.1.im ^ 2 := by
  obtain ⟨b, hb, hreserve⟩ := exists_phaseContactExact_positive_zero_budget_reserve
  refine ⟨b, hb, fun rho hrho ↦ ?_⟩
  have h := hreserve rho hrho
  have hd : 0 ≤ 1 - rho.1.re := (sub_pos.mpr (NontrivialZetaZero.re_lt_one rho)).le
  have hm : (1 : ℝ) ≤ analyticZetaZeroMultiplicity rho := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive rho
  have hmult : 0 ≤ (4 / 17 : ℝ) * phaseContactExactFamily 1 *
      ((analyticZetaZeroMultiplicity rho : ℝ) - 1) :=
    mul_nonneg (mul_nonneg (by norm_num) (phaseContactExactFamily_nonneg 1)) (sub_nonneg.mpr hm)
  have hheight := mul_le_mul_of_nonneg_left (phaseContactExactFamily_height_le rho.1.im)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 448) hd)
  have hpole := mul_le_mul_of_nonneg_right phaseContactExactFamily_oscillatoryMass_le
    (show 0 ≤ (13 / 4 : ℝ) * (1 - rho.1.re) ^ 2 / rho.1.im ^ 2 by positivity)
  simp only [div_eq_mul_inv] at hpole h ⊢
  nlinarith [phaseContactExactRoot_source_lower]

/-- A proved positive prime-square reserve gives a literal zeta
nonvanishing test with a stronger threshold than the previous zero-source
inequality. The reserve is uniform; no independent arithmetic hypothesis
is left in this theorem. -/
theorem exists_phaseContactExact_prime_square_exclusion :
    ∃ b : ℝ, 0 < b ∧ ∀ s : ℂ, 15 / 16 ≤ s.re → 1 ≤ |s.im| →
      448 * (1 - s.re) * ((61 / 100 : ℝ) * localZetaLogHeight s.im + 83 / 100) +
          (793 / 400 : ℝ) * (1 - s.re) ^ 2 / s.im ^ 2 <
        (11 / 625 : ℝ) + b * (1 - s.re) → riemannZeta s ≠ 0 := by
  obtain ⟨b, hb, hbound⟩ := exists_phaseContactExact_refined_zero_source
  refine ⟨b, hb, fun s hs hy hgap hz ↦ ?_⟩
  have hspos : 0 < s.re := by linarith
  have hs1 : s ≠ 1 := by intro he; subst s; norm_num at hy
  have hpole : riemannZeta₁ s = 0 := by
    rw [riemannZeta₁_eq_sub_one_mul hs1, hz, mul_zero]
  let rho : NontrivialZetaZero :=
    ⟨s, isNontrivialZetaZero_of_poleRemoved_eq_zero hspos hpole⟩
  exact (not_lt_of_ge (hbound rho hs)) hgap

end

end RiemannGaussian
