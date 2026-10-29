/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceRowHeight
import RiemannGaussian.SemiprimeJetArrayHeight

/-!
# Literal Hermite cardinal input heights

The actual normalized Taylor cardinal product has one explicit common
denominator. Its coefficient bounds precede, rather than assume, inverse-jet
height estimates.
-/
set_option autoImplicit false
noncomputable section
namespace RiemannGaussian.SemiprimeCardinalHeight
open scoped BigOperators
open Polynomial
open RiemannGaussian.SemiprimeHermiteRecovery
open RiemannGaussian.SemiprimeSourceRowHeight
open RiemannGaussian.SemiprimeJetArrayHeight
attribute [local instance] Classical.propDecidable

/-- The literal normalized cardinal denominator at the actual integer samples. -/
def cardinalDenominator (Q J : ℕ) : ℕ := Q.factorial ^ (Q * J)

theorem sample_inverse_clears {Q : ℕ} {t s : ℚ}
    (ht : t ∈ samplePoints Q) (hs : s ∈ samplePoints Q) (hst : s ≠ t) :
    Clears Q.factorial (C ((t - s)⁻¹)) := by
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ht
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hs
  have hij : i ≠ j := by intro h; subst j; exact hst rfl
  have h := sample_difference_clears Q i j hij
  rw [sample_difference_inverse Q i j hij] at h
  have he : ((i.val : ℚ) + 1) - ((j.val : ℚ) + 1) = (((i.val : ℤ) - j.val : ℤ) : ℚ) := by
    push_cast
    ring
  rw [he]
  exact h

theorem sample_inverse_abs {Q : ℕ} {t s : ℚ}
    (ht : t ∈ samplePoints Q) (hs : s ∈ samplePoints Q) (hst : s ≠ t) : |(t - s)⁻¹| ≤ 1 := by
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ht
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hs
  have hij : i ≠ j := by intro h; subst j; exact hst rfl
  have h := sample_difference_inverse_abs Q i j hij
  rw [sample_difference_inverse Q i j hij] at h
  have he : ((i.val : ℚ) + 1) - ((j.val : ℚ) + 1) = (((i.val : ℤ) - j.val : ℤ) : ℚ) := by
    push_cast
    ring
  rw [he]
  exact h

/-- Exact finite normalized-factor formula, including every cardinal node. -/
theorem taylor_cardinal_product (points : Finset ℚ) (J : ℕ) (t : ℚ) :
    taylor t (cardinalFactor points J t) =
      ∏ s ∈ points.erase t, (1 + X * C ((t - s)⁻¹)) ^ J := by
  classical
  unfold cardinalFactor
  rw [taylor_apply, prod_comp]
  refine Finset.prod_congr (s₁ := @Finset.erase ℚ (fun a b => Classical.propDecidable (a = b)) points t)
    (s₂ := points.erase t) ?_ ?_
  · ext x
    simp
  intro s hs
  rw [← taylor_apply, taylor_pow, taylor_mul, map_sub, taylor_X, taylor_C, taylor_C]
  congr 1
  have hst : t - s ≠ 0 := sub_ne_zero.mpr (Finset.ne_of_mem_erase hs).symm
  calc
    _ = X * C ((t - s)⁻¹) + C ((t - s) * (t - s)⁻¹) := by
      rw [C_mul, C_sub]
      ring
    _ = _ := by simp [hst, add_comm]

theorem clears_pow {d : ℕ} {p : Polynomial ℚ} (hp : Clears d p) (J : ℕ) :
    Clears (d ^ J) (p ^ J) := by
  induction J with
  | zero => simpa using clears_of_integer 1 integerPolynomials.one_mem
  | succ J ih => simpa only [pow_succ] using clears_mul ih hp

/-- A common coefficient denominator for the actual shifted cardinal factor. -/
theorem taylor_cardinal_clears {Q J : ℕ} {t : ℚ} (ht : t ∈ samplePoints Q) :
    Clears (cardinalDenominator Q J) (taylor t (cardinalFactor (samplePoints Q) J t)) := by
  rw [taylor_cardinal_product]
  have hp : ∀ s ∈ (samplePoints Q).erase t,
      Clears Q.factorial (1 + X * C ((t - s)⁻¹)) := by
    intro s hs
    apply clears_add (clears_of_integer _ integerPolynomials.one_mem)
    have hc := sample_inverse_clears ht (Finset.mem_of_mem_erase hs) (Finset.ne_of_mem_erase hs)
    have hm := clears_mul (clears_of_integer 1 integer_X) hc
    simpa only [Nat.one_mul] using hm
  have h := clears_prod ((samplePoints Q).erase t) (Q.factorial ^ J)
    (fun s => (1 + X * C ((t - s)⁻¹)) ^ J) (fun s hs => clears_pow (hp s hs) J)
  rw [← pow_mul] at h
  apply clears_of_dvd h
  apply pow_dvd_pow
  have hc : ((samplePoints Q).erase t).card ≤ Q :=
    (Finset.card_erase_le).trans_eq (samplePoints_card Q)
  nlinarith

theorem coeffBound_mul_affine {p : Polynomial ℚ} {a B : ℚ}
    (hp : CoeffBound p B) (ha : |a| ≤ 1) (hB : 0 ≤ B) :
    CoeffBound (p * (1 + X * C a)) (2 * B) := by
  have hq := coeffBound_C_mul_unit (coeffBound_mul_X hp hB) ha
  have he : p * (1 + X * C a) = p + C a * (p * X) := by ring
  rw [he]
  simpa only [two_mul] using coeffBound_add hp hq

theorem coeffBound_mul_affine_power {p : Polynomial ℚ} {a B : ℚ}
    (hp : CoeffBound p B) (ha : |a| ≤ 1) (hB : 0 ≤ B) (J : ℕ) :
    CoeffBound (p * (1 + X * C a) ^ J) (B * 2 ^ J) := by
  induction J with
  | zero => simpa using hp
  | succ J ih =>
    rw [pow_succ, ← mul_assoc]
    have h := coeffBound_mul_affine ih ha (by positivity)
    convert h using 1
    rw [pow_succ]
    ring

theorem coeffBound_affine_power_product {I : Type*} (s : Finset I) (a : I → ℚ)
    (ha : ∀ i ∈ s, |a i| ≤ 1) (J : ℕ) :
    CoeffBound (∏ i ∈ s, (1 + X * C (a i)) ^ J) (2 ^ (s.card * J)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using coeffBound_C (c := 1) (B := 1) (by norm_num) (by norm_num)
  | @insert i s hi ih =>
    have hp := ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))
    have h := coeffBound_mul_affine_power hp (ha i (Finset.mem_insert_self i s)) (by positivity) J
    rw [← pow_add] at h
    rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi, mul_comm]
    convert h using 1
    congr 1
    ring

/-- Coefficients of the actual normalized Taylor cardinal input have a finite
binomial bound without any inverse-series hypothesis. -/
theorem taylor_cardinal_coeffBound {Q J : ℕ} {t : ℚ} (ht : t ∈ samplePoints Q) :
    CoeffBound (taylor t (cardinalFactor (samplePoints Q) J t)) ((2 : ℚ) ^ (Q * J)) := by
  rw [taylor_cardinal_product]
  have h := coeffBound_affine_power_product ((samplePoints Q).erase t)
    (fun s => (t - s)⁻¹) (fun s hs => sample_inverse_abs ht
      (Finset.mem_of_mem_erase hs) (Finset.ne_of_mem_erase hs)) J
  have hc : ((samplePoints Q).erase t).card ≤ Q :=
    (Finset.card_erase_le).trans_eq (samplePoints_card Q)
  intro k
  exact (h k).trans (pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_right J hc))

theorem cardinalDenominator_pos (Q J : ℕ) : 0 < cardinalDenominator Q J :=
  Nat.pow_pos (Nat.factorial_pos Q)

/-- Literal common-denominator representations for every coefficient fed to the
cached normalized inverse-jet recurrence. -/
theorem taylor_cardinal_representation {Q J : ℕ} {t : ℚ} (ht : t ∈ samplePoints Q) (k : ℕ) :
    Representation ((taylor t (cardinalFactor (samplePoints Q) J t)).coeff k)
      (cardinalDenominator Q J) (cardinalDenominator Q J * 2 ^ (Q * J)) := by
  obtain ⟨P, hP⟩ := taylor_cardinal_clears (J := J) ht
  change P.map (Int.castRingHom ℚ) = _ at hP
  have he := congrArg (fun p : Polynomial ℚ => p.coeff k) hP
  simp only [Polynomial.coeff_map, Polynomial.coeff_C_mul] at he
  change ((P.coeff k : ℤ) : ℚ) = _ at he
  have hd : (0 : ℚ) < cardinalDenominator Q J := by exact_mod_cast cardinalDenominator_pos Q J
  refine ⟨P.coeff k, ?_, ?_⟩
  · apply (eq_div_iff (ne_of_gt hd)).mpr
    simpa only [mul_comm] using he.symm
  · have hb := taylor_cardinal_coeffBound (J := J) ht k
    have hm := mul_le_mul_of_nonneg_left hb hd.le
    have hz : |((P.coeff k : ℤ) : ℚ)| ≤ (cardinalDenominator Q J * 2 ^ (Q * J) : ℕ) := by
      rw [he, abs_mul, abs_of_nonneg hd.le]
      exact_mod_cast hm
    have hz' : |P.coeff k| ≤ ((cardinalDenominator Q J * 2 ^ (Q * J) : ℕ) : ℤ) := by exact_mod_cast hz
    rw [← Int.natCast_natAbs] at hz'
    exact_mod_cast hz'

/-- Normalization is an actual identity at the selected sample, not an assumed input. -/
theorem taylor_cardinal_constant (Q J : ℕ) (t : ℚ) :
    (taylor t (cardinalFactor (samplePoints Q) J t)).coeff 0 = 1 := by
  rw [taylor_coeff_zero, cardinalFactor_eval]

/-- The cardinal denominator has an explicit polynomial-size bit budget. -/
theorem cardinalDenominator_le_power (Q J : ℕ) :
    cardinalDenominator Q J ≤ 2 ^ (Nat.clog 2 Q * Q * (Q * J)) := by
  unfold cardinalDenominator
  calc
    Q.factorial ^ (Q * J) ≤ (Q ^ Q) ^ (Q * J) := Nat.pow_le_pow_left (Nat.factorial_le_pow Q) _
    _ ≤ ((2 ^ Nat.clog 2 Q) ^ Q) ^ (Q * J) := by
      gcongr
      exact Nat.le_pow_clog (by decide) Q
    _ = _ := by rw [← pow_mul, ← pow_mul]; simp only [Nat.mul_assoc]

end RiemannGaussian.SemiprimeCardinalHeight
